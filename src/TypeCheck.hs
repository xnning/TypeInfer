{-# LANGUAGE DeriveGeneric, DeriveDataTypeable, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, ScopedTypeVariables, OverloadedStrings, TemplateHaskell  #-}

module TypeCheck (oneStep, typecheck, eval) where

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.Trans.Maybe
import qualified Data.Text as T
import           Unbound.Generics.LocallyNameless

import           PrettyPrint
import           Syntax
import           Environment
import qualified Data.Set as Set

import           Data.List(intersect, findIndex)
import           Data.Maybe (isJust)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

-----------------------------------------
--  Operational Semantics: Expr
-----------------------------------------

done :: MonadPlus m => m a
done = mzero

-- | Small step, call-by-name operational semantics
step :: Expr -> MaybeT FreshM Expr
-- S_BETA
step (App (Lam bnd) t2) = do
  (delta, b) <- unbind bnd
  return $ subst delta t2 b
step (App (LamAnn bnd) t2) = do
  ((delta, _), b) <- unbind bnd
  return $ subst delta t2 b
-- S_APP
step (App t1 t2) =
      App <$> step t1 <*> pure t2
  <|> App <$> pure t1 <*> step t2
-- S_CastDownUp
step (CastDown (CastUp e)) = return e
-- S_CastDown
step (CastDown e) = CastDown <$> step e
-- S-Let
step (Let bnd) = do
  ((n, Embed e), b) <- unbind bnd
  let n' = name2String n
  pure (subst n e b)
-- S-Ann
step (Ann e t)  =  (Ann <$> step e <*> pure t)
-- prim operation
-- eval op. eval n. eval m
step (PrimOp op (Lit n) (Lit m)) = do
  let x = evalOp op
  return (Lit (n `x` m))
step (PrimOp op e1 e2) =
      PrimOp <$> pure op <*> step e1 <*> pure e2
  <|> PrimOp <$> pure op <*> pure e1 <*> step e2
step _    = done

evalOp :: Operation -> Int -> Int -> Int
evalOp Add = (+)
evalOp Sub = (-)
evalOp Mult = (*)

-- | transitive closure of `step`
tc :: (Monad m, Functor m) => (a -> MaybeT m a) -> a -> m a
tc f a = do
  ma' <- runMaybeT (f a)
  case ma' of
    Nothing -> return a
    Just a' -> tc f a'

eval :: Expr -> Expr
eval x = runFreshM (tc step x)

oneStep :: (MonadError T.Text m) => Expr -> m Expr
oneStep e = do
  case runFreshM . runMaybeT $ (step e) of
    Nothing -> throwError $ T.concat ["Cannot reduce ", showExpr e]
    Just e' -> return e'

-----------------------------------------
--  Typing Rules: Bi-Directional
-----------------------------------------

typecheck :: Expr -> (Either T.Text Expr)
typecheck e = runTcMonad initialEnv $ do
   infertype e >>= applyEnv >>= generalization
   {-typ <- infertype e-}
   {-applied <- applyEnv  typ-}
   {-genelized <- generalization applied-}
   {-env <- printEnv-}
   {-throwError $ T.concat ["env: ", T.pack env, ";\ntype: ", showExpr typ, ";\napplied env: ", showExpr applied, ";\ngenelized: ", showExpr genelized]-}

data Mode = Infer | Check Expr deriving (Show)

infertype :: Expr ->  TcMonad Expr
infertype e = bicheck e Infer

checktype :: Expr -> Expr -> TcMonad Expr
checktype e ty = bicheck e $ Check ty

bicheck :: Expr -> Mode -> TcMonad Expr
-- Var LetVar
bicheck (Var cnm) Infer = do
  sigma <- lookupVarTy cnm
  inst sigma
-- Lam Infer
bicheck (Lam bnd) Infer = do
  (x, body) <- unbind bnd
  x'@(Var nm) <- genVar
  let body' = subst x x' body

  alpha <- ctxGenAddTVar
  beta <- ctxGenAddTVar
  ctxAddCstrVar nm alpha

  checktype body' beta
  throwAfterVar nm

  return (epiWithName [(nm, alpha)] beta)
-- Lam Check
bicheck (Lam bnd) (Check p@(Pi bd)) = do
  (x, lam_body) <- unbind bnd
  (pix, tau1, tau2) <- unpi p

  x'@(Var nm) <- genVar
  let lam_body' = subst x x' lam_body
      tau2' = subst pix x' tau2

  ctxAddCstrVar nm tau1
  checktype lam_body' tau2'
  throwAfterVar nm

  return (epiWithName [(nm, tau1)] tau2')
-- LamAnn
bicheck (LamAnn bnd) Infer = do
  ((x, Embed tau1), e) <- unbind bnd
  checktype tau1 estar

  x'@(Var nm) <- genVar
  ctxAddCstrVar nm tau1
  tau2 <- infertype (subst x x' e)
  throwAfterVar nm

  return (epiWithName [(nm, tau1)] tau2)
-- App
bicheck (App e1 e2) Infer = do
  tau1 <- infertype e1
  applied_tau1 <- applyEnv tau1
  app_typing applied_tau1 e2
-- Ann
bicheck (Ann expr tau) Infer = do
  checktype tau Star
  checktype expr tau
-- Let
bicheck (Let bnd) mode = do
  ((x, Embed e1), e2) <- unbind bnd
  tau1 <- infertype e1
  sigma <- generalize tau1

  x'@(Var nm) <- genVar
  ctxAddLetVar nm sigma e1

  tau2 <- bicheck (subst x x' e2) mode
  throwAfterVar nm

  return tau2
-- ECPLICIT-PI
bicheck p@(Pi bnd) Infer = do
  (x, tau1, tau2) <- unpi p
  checktype tau1 Star
  ctxAddCstrVar x tau1
  checktype tau2 Star
  throwAfterVar x
  return estar
-- AX
bicheck Star Infer = return Star
-- CASTUP-CHECK
bicheck (CastUp e) (Check tau2) = do
  applied_tau2 <- applyEnv tau2
  tau1 <- oneStep applied_tau2
  checktype e tau1
-- CASTDOWN
bicheck (CastDown e) Infer = do
  tau1 <- infertype e
  applied_tau1 <- applyEnv tau1
  oneStep applied_tau1
-- Others
bicheck Nat Infer  = return estar
bicheck (Lit n) Infer = return Nat
bicheck (PrimOp op e1 e2) Infer = do
  checktype e1 Nat
  checktype e2 Nat
  return Nat
-- Sub
bicheck e (Check tau2) = do
  tau1 <- infertype e
  applied_tau1 <- applyEnv tau1
  applied_tau2 <- applyEnv tau2
  unify applied_tau1 applied_tau2
  return applied_tau2
-- Error
bicheck e mode = throwError $ T.concat [T.pack $ show mode, " type failed\nexpr: ", showExpr e]

-----------------------------------------
--  Application Typing Rule
-----------------------------------------

app_typing :: Expr -> Expr -> TcMonad Expr
-- APP-Pi
app_typing p@(Pi bnd) e = do
  (x, tau1, tau2) <- unpi p
  checktype e tau1
  return (subst x e tau2)
-- APP-TVar
app_typing (TVar nm) e = do
  alpha1 <- genTVarBefore nm
  alpha2 <- genTVarBefore nm

  cnm <- genName
  addSubsitution nm (epiWithName [(cnm, alpha1)] alpha2)
  checktype e alpha1

  return alpha2
-- OTHER-Error
app_typing ty e2 =
  throwError $ T.concat ["expr of type ", showExpr ty, "\ncan not be applied to ", showExpr e2]

-----------------------------------------
--  Polymorphic Relation & Unification
-----------------------------------------

unify :: Expr -> Expr -> TcMonad ()
-- ExplicitPi
unify s1@(Pi bnd1) s2@(Pi bnd2) = do
     (x1, tau1, tau2) <- unpi s1
     (x2, tau1', tau2') <- unpi s2
     unify tau1 tau1'
     ctxAddCstrVar x1 tau1

     applied_tau2 <- applyEnv tau2
     applied_tau2' <- applyEnv (subst x2 (Var x1) tau2')
     unify applied_tau2 applied_tau2'

     throwAfterVar x1
-- APP
unify s1@(App tau1 tau2) s2@(App tau1' tau2') = do
    unify tau1 tau1'

    applied_tau2 <- applyEnv tau2
    applied_tau2' <- applyEnv tau2'

    unify applied_tau2 applied_tau2'
-- LAM
unify s1@(Lam bnd1) s2@(Lam bnd2) = do
    (x1, body1) <- unbind bnd1
    (x2, body2) <- unbind bnd2
    let body2' = subst x2 (Var x1) body2

    ctxAddVar x1
    unify body1 body2'

    throwAfterVar x1
-- LAM ANN
unify s1@(LamAnn bnd1) s2@(LamAnn bnd2) = do
  ((x1, Embed tau1), e1) <- unbind bnd1
  ((x2, Embed tau2), e2) <- unbind bnd2
  unify tau1 tau2

  ctxAddCstrVar x1 tau1
  applied_e1 <- applyEnv e1
  applied_e2 <- applyEnv $ subst x2 (Var x1) e2
  unify applied_e1 applied_e2

  throwAfterVar x1
-- ANN
unify (Ann e1 tau1) (Ann e2 tau2) = do
    unify tau1 tau2
    applied_e1 <- applyEnv e1
    applied_e2 <- applyEnv e2
    unify applied_e1 applied_e2
-- CASTUP
unify (CastUp tau1) (CastUp tau2) = unify tau1 tau2
-- CASTDOWN
unify (CastDown tau1) (CastDown tau2) = unify tau1 tau2
-- Let
unify (Let bnd1) (Let bnd2) = do
  ((x1, Embed tau1), tau2) <- unbind bnd1
  ((x2, Embed tau3), tau4) <- unbind bnd2
  unify tau1 tau3
  applied_tau2 <- applyEnv tau2
  applied_tau4 <- applyEnv (subst x2 (Var x1) tau4)
  unify applied_tau2 applied_tau4
-- Star
unify Star Star = return ()
-- Nat
unify Nat Nat = return ()
-- Lit
unify (Lit n) (Lit m) | n == m = return ()
-- Operation
unify (PrimOp op n1 n2) (PrimOp op2 m1 m2) | op == op2 = do
  unify n1 m1
  applied_n2 <- applyEnv n2
  applied_m2 <- applyEnv m2
  unify applied_n2 applied_m2
-- Var
unify (Var tm1) (Var tm2) | tm1 == tm2 = existsVar tm1
-- EVar-ID
unify (TVar tm1) (TVar tm2) | tm1 == tm2 = existsTVar tm1
-- EVar-EVar
unify alpha@(TVar tm1) beta@(TVar tm2) = do
  tm1_tm2 <- tvarExistsBefore tm1 tm2
  if tm1_tm2
  then addSubsitution tm2 alpha
  else addSubsitution tm1 beta
-- EVar-Uni
unify ev@(TVar tm1) tau1 = do
  occur_check tm1 tau1

  wellDefinedBeforeTVar tm1 tau1
  addSubsitution tm1 tau1
-- EVar-right
unify tau1 ev@(TVar tm1) = unify ev tau1
-- Other-Error
unify sigma1 sigma2 = throwError $ T.concat ["unify failed\nexpr1: ", showExpr sigma1, "\nexpr2: ", showExpr sigma2]

-------------------------------------------
--  Generalization
-------------------------------------------

generalize :: Expr -> TcMonad Expr
generalize tau = applyEnv tau >>= generalization

-------------------------------------------
--  Instantiation
-------------------------------------------

inst ::  Expr -> TcMonad Expr
inst t = applyEnv t >>= instantiate

-------------------------------------------
--  Utility
-------------------------------------------

unpi :: Expr -> TcMonad (TmName, Expr, Expr)
unpi (Pi bnd) = do
  (Cons tele, b) <- unbind bnd
  let ((x, Embed tau1), rest) = unrebind tele
      tau2 = mkpi rest b
  return (x, tau1, tau2)
