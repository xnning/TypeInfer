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

-----------------------------------------
--  Operational Semantics: CheckedExpr
-----------------------------------------

-- | Small step, call-by-name operational semantics
cstep :: CheckedExpr -> MaybeT FreshM CheckedExpr
-- S_BETA
cstep (CApp (CLam bnd _) t2 _) = do
  (delta, b) <- unbind bnd
  return $ subst delta t2 b
-- S_APP
cstep (CApp t1 t2 ty) =
      CApp <$> cstep t1 <*> pure t2 <*> pure ty
  <|> CApp <$> pure t1 <*> cstep t2 <*> pure ty
-- S_CastDownUp
cstep (CCastDown (CCastUp e _) _) = return e
-- S_CastDown
cstep (CCastDown e ty) = CCastDown <$> cstep e <*> pure ty
-- S-Let
cstep (CLet bnd _) = do
  ((n, Embed e), b) <- unbind bnd
  pure (subst n e b)
-- S-Ann
cstep (CAnn e t ty) = CAnn <$> cstep e <*> pure t <*> pure ty
-- prim operation
-- eval op. eval n. eval m
cstep (CPrimOp op (CLit n) (CLit m)) = do
  let x = evalOp op
  return (CLit (n `x` m))
cstep (CPrimOp op e1 e2) =
      CPrimOp <$> pure op <*> cstep e1 <*> pure e2
  <|> CPrimOp <$> pure op <*> pure e1 <*> cstep e2
cstep _    = done

oneStep :: (MonadError T.Text m) => CheckedExpr -> m CheckedExpr
oneStep e = do
  case runFreshM . runMaybeT $ (cstep e) of
    Nothing -> throwError $ T.concat ["Cannot reduce ", showCheckedExpr e]
    Just e' -> return e'

-----------------------------------------
--  Typing Rules: Bi-Directional
-----------------------------------------

typecheck :: Expr -> (Either T.Text CheckedExpr)
typecheck e = runTcMonad initialEnv $ do
   getCheckedType <$> (infertype e) >>= applyEnv >>= generalization
   {-typ <- getCheckedType <$> (infertype e)-}
   {-applied <- applyEnv  typ-}
   {-genelized <- generalization applied-}
   {-env <- printEnv-}
   {-throwError $ T.concat ["env: ", T.pack env, ";\ntype: ", showCheckedExpr typ, ";\napplied env: ", showCheckedExpr applied, ";\ngenelized: ", showCheckedExpr genelized]-}

data Mode = Infer | Check CheckedExpr deriving (Show)

infertype :: Expr ->  TcMonad CheckedExpr
infertype e = bicheck e Infer

checktype :: Expr -> CheckedExpr -> TcMonad CheckedExpr
checktype e ty = bicheck e $ Check ty

bicheck :: Expr -> Mode -> TcMonad CheckedExpr
-- if Mode is (Check ty), ty is rho
bicheck (Var x) Infer = do
  let cnm = tmname2c x
  sigma <- lookupVarTy cnm
  sigma' <- instSigma sigma Infer
  return (evar2c x sigma')
-- Lam Infer
bicheck (Lam bnd) Infer = do
  (x, body) <- unbind bnd
  x'@(Var nm) <- genVar
  let body' = subst x x' body

  alpha <- ctxGenAddTVar CStar
  beta <- ctxGenAddTVar CStar
  let cnm = tmname2c nm
  ctxAddCstrVar cnm alpha

  checked_body <- checktype body' beta
  throwAfterVar cnm

  return (CLam (bind cnm checked_body) (cepiWithName [(cnm, alpha)] beta))
-- Lam Check
bicheck (Lam bnd) (Check (CPi bd))  = do
  (x, lam_body) <- unbind bnd
  (CCons teles, ty_body) <- unbind bd
  let ((pix, Embed sigma1), rest) = unrebind teles

  x'@(Var nm) <- genVar
  let cnm = tmname2c nm
      cvar = CVar cnm sigma1
      lam_body' = subst x x' lam_body
      sigma2 = mkpi (subst pix cvar rest) (subst pix cvar ty_body)

  ctxAddCstrVar cnm sigma1
  checked_body <- checktype lam_body' sigma2
  throwAfterVar cnm

  return (CLam (bind cnm checked_body) (cepiWithName [(cnm, sigma1)] sigma2))
-- App
bicheck (App e1 e2) Infer = do
  checked_e1 <- infertype e1
  let rho1 = getCheckedType checked_e1
  applied_rho <- applyEnv rho1
  app_typing applied_rho checked_e1 e2
-- Ann
bicheck (Ann expr sigma) Infer = do
  checked_sigma <- checktype sigma CStar
  checked_expr <- polySigma expr (Check checked_sigma)
  rho <- instSigma (checked_sigma) Infer
  return $ CAnn checked_expr checked_sigma rho
-- Let: TODO
{-bicheck (Let bnd) mode = do-}
  {-((x, Embed e1), e2) <- unbind bnd-}
  {-checked_e1 <- withEnv (infertype e1)-}
  {-let substed_e2 = subst x e1 e2-}
  {-bicheck substed_e2 mode-}
-- IMPLICIT-PI
bicheck p@(Forall bnd) Infer = do
  (Cons tele, b) <- unbind bnd
  let ((x, Embed sigma1), rest) = unrebind tele
      sigma2 = expr_mkforall rest b
      cnm = tmname2c x
  checked_sigma1 <- checktype sigma1 CStar
  ctxAddCstrVar cnm checked_sigma1
  checked_sigma2 <- checktype sigma2 CStar
  throwAfterVar cnm
  return $ CForall (bind (CCons (rebind (cnm, Embed checked_sigma1) CEmpty)) checked_sigma2)
-- ECPLICIT-PI
bicheck p@(Pi bnd) Infer = do
  (Cons tele, b) <- unbind bnd
  let ((x, Embed sigma1), rest) = unrebind tele
      sigma2 = expr_mkpi rest b
      cnm = tmname2c x
  checked_sigma1 <- checktype sigma1 CStar
  ctxAddCstrVar cnm checked_sigma1
  checked_sigma2 <- checktype sigma2 CStar
  throwAfterVar cnm
  return $ CPi (bind (CCons (rebind (cnm, Embed checked_sigma1) CEmpty)) checked_sigma2)
-- AX
bicheck Star Infer = return CStar
-- CASTUP-CHECK
bicheck (CastUp e) (Check rho) = do
  checked_rho <- applyEnv rho
  sigma <- oneStep checked_rho
  polySigma e (Check sigma)
-- CASTDOWN
bicheck (CastDown e) Infer = do
  checked_e <- infertype e
  let rho1 = getCheckedType checked_e
  applied_rho1 <- applyEnv rho1
  sigma <- oneStep applied_rho1
  rho2 <- instSigma sigma Infer
  return $ CCastDown checked_e rho2
-- Others
bicheck Nat Infer  = return CNat
bicheck (Lit n) Infer = return (CLit n)
bicheck (PrimOp op e1 e2) Infer = do
  checked_e1 <- checktype e1 CNat
  checked_e2 <- checktype e2 CNat
  return (CPrimOp op checked_e1 checked_e2)
-- Sub
bicheck e rho@(Check ty) = do
  checked_expr <- infertype e
  let rho1 =  getCheckedType checked_expr
  instSigma rho1 rho
  return $ changeCheckedType checked_expr ty
bicheck e mode = throwError $ T.concat ["Type checking ", showExpr e, " with mode ", T.pack $ show mode, " failed"]

-----------------------------------------
--  Application Typing Rule
-----------------------------------------

app_typing :: CheckedExpr -> CheckedExpr -> Expr -> TcMonad CheckedExpr
-- APP-Pi
app_typing (CPi bnd) checked_e1 e2 = do
  (CCons tele, b) <- unbind bnd
  let ((x, Embed sigma1), rest) = unrebind tele
      sigma2 = mkpi rest b

  checked_e2 <- polySigma e2 (Check sigma1)
  rho <- instSigma (subst x checked_e2 sigma2) Infer
  return (CApp checked_e1 checked_e2 rho)
-- APP-TVar
app_typing (CTVar nm ty) checked_e1 e2 = do
  instSigma ty (Check CStar)

  alpha1 <- genTVarBefore nm CStar
  alpha2 <- genTVarBefore nm CStar

  cnm <- genCName
  addSubsitution nm (cepiWithName [(cnm, alpha1)] alpha2)
  checked_e2 <- checktype e2 alpha1

  return (CApp checked_e1 checked_e2 alpha2)
-- OTHER-Error
app_typing ty checked_e1 e2 =
  throwError $ T.concat ["expr ", showCheckedExpr checked_e1,
      "\nwith type ", showCheckedExpr ty, "\ncan not be applied to ", showExpr e2]

-----------------------------------------
--  Polymorphic Relation & Unification
-----------------------------------------

data Procedure = Dsk | Unify deriving (Show)

dsk :: CheckedExpr -> CheckedExpr -> TcMonad ()
dsk = dsk_unify Dsk

unify :: CheckedExpr -> CheckedExpr -> TcMonad ()
unify = dsk_unify Unify

dsk_unify :: Procedure -> CheckedExpr -> CheckedExpr -> TcMonad ()
-- ImplicitPi-Dsk-R
dsk_unify Dsk sigma1 sigma2@(CForall _) = do
    rho2 <- skolemInstantiate sigma2
    dsk sigma1 rho2
-- ImplicitPi-Dsk-L
dsk_unify Dsk sigma1@(CForall _) sigma2 = do
    marker <- addMarker
    rho1 <- instantiate sigma1
    dsk rho1 sigma2
    deleteAfterMarker marker
-- ImplicitPi-Unify
dsk_unify Unify s1@(CForall bnd1) s2@(CForall bnd2) = do
     (bind1, b1) <- unbind bnd1
     (bind2, b2) <- unbind bnd2
     case (bind1, bind2) of
        (CEmpty, CEmpty) -> unify b1 b2
        (CCons cons1, CCons cons2) -> do
            let ((x1, Embed sigma1), rest1) = unrebind cons1
            let ((x2, Embed sigma3), rest2) = unrebind cons2
            unify sigma1 sigma3
            sigma2 <- applyEnv $ mkforall rest1 b1
            sigma4 <- applyEnv . (subst x2 (CVar x1 sigma1)) $ mkforall rest2 b2
            ctxAddCstrVar x1 sigma1
            unify sigma2 sigma4
        _ -> unify_error s1 s2
-- ExplicitPi
dsk_unify proc s1@(CPi bnd1) s2@(CPi bnd2) = do
     (bind1, b1) <- unbind bnd1
     (bind2, b2) <- unbind bnd2
     case (bind1, bind2) of
        (CEmpty, CEmpty) -> unify b1 b2
        (CCons cons1, CCons cons2) -> do
            let ((x1, Embed sigma1), rest1) = unrebind cons1
            let ((x2, Embed sigma3), rest2) = unrebind cons2
            unify sigma1 sigma3
            sigma2 <- applyEnv $ mkpi rest1 b1
            sigma4 <- applyEnv . (subst x2 (CVar x1 sigma1)) $ mkpi rest2 b2
            ctxAddCstrVar x1 sigma1
            unify sigma2 sigma4
        _ -> unify_error s1 s2
-- APP
dsk_unify proc s1@(CApp tau1 sigma1 _) s2@(CApp tau2 sigma2 _) = do
    unify sigma1 sigma2
    applied_tau1 <- applyEnv tau1
    applied_tau2 <- applyEnv tau2
    dsk_unify proc applied_tau1 applied_tau2
-- LAM
dsk_unify proc s1@(CLam bnd1 t1) s2@(CLam bnd2 t2) = do
    CPi bpi <- applyEnv t1
    ((CCons cons), t2) <- unbind bpi
    let ((_, Embed sigma1), _) = unrebind cons

    (x1, body1) <- unbind bnd1
    (x2, body2) <- unbind bnd2
    let body2' = subst x2 (CVar x1 sigma1) body2

    ctxAddCstrVar x1 sigma1
    unify body1 body2'
-- ANN
dsk_unify proc (CAnn sigma1 sigma2 _) (CAnn sigma3 sigma4 _) = do
    unify sigma2 sigma4
    sigma1' <- applyEnv sigma1
    sigma3' <- applyEnv sigma3
    dsk_unify proc sigma1' sigma3'
-- CASTUP
dsk_unify proc (CCastUp sigma1 _) (CCastUp sigma2 _) = dsk_unify proc sigma1 sigma2
-- CASTDOWN
dsk_unify proc (CCastDown sigma1 _) (CCastDown sigma2 _) = dsk_unify proc sigma1 sigma2
dsk_unify proc (CLet bnd1 _) (CLet bnd2 _) = do
  ((x1, Embed sigma1), sigma2) <- unbind bnd1
  ((x2, Embed sigma3), sigma4) <- unbind bnd2
  unify sigma1 sigma3
  sigma2' <- applyEnv sigma2
  sigma4' <- applyEnv sigma4
  dsk_unify proc sigma2' sigma4'
-- Star
dsk_unify proc CStar CStar = return ()
-- Nat
dsk_unify proc CNat CNat = return ()
-- Lit
dsk_unify proc (CLit n) (CLit m) | n == m = return ()
-- Operation
dsk_unify proc (CPrimOp op n1 n2) (CPrimOp op2 m1 m2) | op == op2 = do
  unify n1 n2
  applied_n2 <- applyEnv n2
  applied_m2 <- applyEnv m2
  unify applied_n2 applied_m2
-- Var
dsk_unify proc (CVar tm1 _) (CVar tm2 _) | tm1 == tm2 = existsVar tm1
-- EVar
dsk_unify proc (CTVar tm1 _) (CTVar tm2 _) | tm1 == tm2 = existsTVar tm1
-- EVar-Uni
dsk_unify Unify ev@(CTVar tm1 tau) tau1 = do
  occur_check tm1 tau1

  unifiable <- unifiableType tau1
  unless unifiable $ unify_error ev tau1

  let sigma = getCheckedType tau1
  applied_sigma <- applyEnv sigma
  applied_tau <-  applyEnv tau
  dsk applied_sigma applied_tau

  applied_tau1 <- applyEnv tau1
  tau2 <- sigma2tau Co [] ev applied_tau1
  addSubsitution tm1 tau2
-- EVar-Dsk
dsk_unify Dsk ev@(CTVar tm1 tau) sigma = do
  occur_check tm1 sigma

  let sigma1 = getCheckedType sigma
  applied_sigma1 <- applyEnv sigma1
  applied_tau <-  applyEnv tau
  dsk applied_sigma1 applied_tau

  applied_sigma <- applyEnv sigma
  tau1 <- sigma2tau Co [] ev applied_sigma
  addSubsitution tm1 tau1
-- EVar-right
dsk_unify _ tau1 ev@(CTVar tm1 tau) = unify ev tau1
-- Other-Error
dsk_unify proc sigma1 sigma2 = do
  throwError $ T.concat ["call dsk_unify with proc ", T.pack $ show proc,
    " with expr1 ", showCheckedExpr sigma1, " and expr2 ", showCheckedExpr sigma2]

unify_error :: (MonadError T.Text m) => CheckedExpr -> CheckedExpr -> m a
unify_error = dsk_unify_error Unify

dsk_error :: (MonadError T.Text m) => CheckedExpr -> CheckedExpr -> m a
dsk_error = dsk_unify_error Dsk

dsk_unify_error :: (MonadError T.Text m) => Procedure -> CheckedExpr -> CheckedExpr -> m a
dsk_unify_error p e1 e2 = throwError $ T.concat ["procedure ", T.pack $ show p, " ", showCheckedExpr e1, " and ", showCheckedExpr e2, " failed"]

-- tau test
unifiableType :: CheckedExpr -> TcMonad Bool
unifiableType (CTVar _ _ )   = return True
unifiableType (CVar _ _)       = return True
unifiableType CStar          = return True
unifiableType CNat           = return True
unifiableType (CLam bnd _)     = return True
unifiableType (CLamAnn bnd _)  = return True
unifiableType (CApp e1 e2 _)   = multiUnifiableType [e1, e2]
unifiableType (CAnn e1 e2 _)   = multiUnifiableType [e1, e2]
unifiableType (CCastUp e _)    = unifiableType e
unifiableType (CCastDown e _)  = unifiableType e
unifiableType e@(CPi bd)      = do
    (tele, body) <- unbind bd
    let CCons bnd = tele
        ((nm, Embed t), rest) = unrebind bnd
    multiUnifiableType [t, mkpi rest body]
unifiableType (CLet bnd _)     = unbind bnd >>= (\((_, Embed e), b) -> multiUnifiableType [e, b])
unifiableType _             = return False

multiUnifiableType :: [CheckedExpr] -> TcMonad Bool
multiUnifiableType [] = return True
multiUnifiableType (hd:tl) = do
    r1 <- unifiableType hd
    if r1 then multiUnifiableType tl
    else return False

-----------------------------------------
--  sigma2tau
-----------------------------------------

data Variant = Co | Contra deriving (Show)

revert :: Variant -> Variant
revert Co = Contra
revert Contra = Co

sigma2tau :: Variant -> [CTmName] -> CheckedExpr -> CheckedExpr -> TcMonad CheckedExpr
-- MONO-VAR
sigma2tau _ bounds t@(CTVar tm1 _) v@(CVar tm2 _) = do
  exist_before <- varExistsBefore tm2 tm1
  let bounded = elem tm2 bounds
  unless (exist_before || bounded) $
      throwError $ T.concat ["var ", showCheckedExpr v, " does nont exist before evar ", showCheckedExpr t]
  return v
-- MONO-Star
sigma2tau _ _ t CStar = return CStar
-- MONO-Lam
sigma2tau _ _ t e@(CLam _ _) = return e
-- MONO-EVar
sigma2tau _ _ alpha@(CTVar tm1 _) beta@(CTVar tm2 ty) = do
  exist_before <- tvarExistsBefore tm2 tm1
  -- MONO-Evar-Left
  if exist_before then return beta
  -- MONO-Evar-Right
  else do beta1 <- genTVarBefore tm1 ty
          addSubsitution tm2 beta1
          return beta1
-- MONO-Pi
sigma2tau variant bounds alpha@(CTVar tm1 _) (CPi bnd) = do
  (tele, body) <- unbind bnd
  let CCons bd = tele
      ((nm, Embed sigma1), rest) = unrebind bd
      sigma2 = mkpi rest body

  tau1 <- sigma2tau (revert variant) bounds alpha sigma1
  tau2 <- applyEnv sigma2 >>= sigma2tau variant (nm : bounds) alpha

  return $ CPi (bind (CCons (rebind (nm, Embed tau1) CEmpty)) tau2)
-- MONO-Forall
sigma2tau Contra bounds alpha@(CTVar tm1 _) sigma@(CForall _) =
  monoInstantiate tm1 sigma >>= sigma2tau Contra bounds alpha
-- MONO-Other
sigma2tau variant bounds alpha sigma2@(CApp e1 e2 ty) = do
  e1' <- sigma2tau variant bounds alpha e1
  e2' <- applyEnv e2 >>= sigma2tau variant bounds alpha
  return $ CApp e1' e2' ty
sigma2tau variant bounds alpha sigma2@(CAnn e1 e2 ty) = do
  e1' <- sigma2tau variant bounds alpha e1
  e2' <- applyEnv e2 >>= sigma2tau variant bounds alpha
  return $ CAnn e1' e2' ty
sigma2tau variant bounds alpha sigma2@(CLet bnd ty) = do
  ((nm, Embed e), b) <- unbind bnd
  e' <- sigma2tau variant bounds alpha e
  b' <- applyEnv b >>= sigma2tau variant bounds alpha
  return $ CLet (bind (nm, Embed e') b') ty
sigma2tau variant bounds alpha sigma2@(CCastUp e1 ty) = do
  e1' <- sigma2tau variant bounds alpha e1
  return $ CCastUp e1' ty
sigma2tau variant bounds alpha sigma2@(CCastDown e1 ty) = do
  e1' <- sigma2tau variant bounds alpha e1
  return $ CCastDown e1' ty
sigma2tau _ _ _ e@(CLit _) = return e
sigma2tau _ _ _ e@CNat = return e
sigma2tau variant bounds alpha e@(CPrimOp op e1 e2) = do
  e1' <- sigma2tau variant bounds alpha e1
  e2' <- applyEnv e2 >>= sigma2tau variant bounds alpha
  return $ CPrimOp op e1' e2'
sigma2tau variant bounds alpha sigma =
  throwError $ T.concat ["sigma2tau: mode ", T.pack $ show variant, " with tvar ", showCheckedExpr alpha, " with expr ", showCheckedExpr sigma]

-------------------------------------------
--  Generalization
-------------------------------------------

polySigma :: Expr -> Mode -> TcMonad CheckedExpr
-- GEN INFER
polySigma expr Infer = do
  checked_expr <- infertype expr
  let typ = getCheckedType checked_expr
  applied <- applyEnv typ
  generalization applied
-- GEN CHECK
polySigma expr (Check sigma) = do
  applied <- applyEnv sigma
  rho <- skolemInstantiate applied
  checktype expr rho

-------------------------------------------
--  Instantiation
-------------------------------------------

instSigma ::  CheckedExpr -> Mode -> TcMonad CheckedExpr
-- INST INFER
instSigma t Infer = applyEnv t >>= instantiate
-- INST CHECK
instSigma sigma (Check rho) = do
    applied_sigma <- applyEnv sigma
    applied_rho <- applyEnv rho
    dsk applied_sigma applied_rho
    return applied_rho
