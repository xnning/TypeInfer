{-# LANGUAGE OverloadedStrings, TemplateHaskell, FlexibleContexts #-}

module TypeCheck (oneStep, typecheck, eval) where

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.Trans.Maybe
import qualified Data.Text as T
import           Lens.Micro
import           Unbound.Generics.LocallyNameless

import           PrettyPrint
import           Syntax
import           Environment
import qualified Data.Set as Set

import           Data.List(intersect)

-----------------------------------------
--  Operational Semantics
-----------------------------------------

done :: MonadPlus m => m a
done = mzero

-- | Small step, call-by-value operational semantics
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
-- Let
-- eval definition. subst body.
step (Let bnd) = do
  ((n, Embed e), b) <- unbind bnd
  let n' = name2String n
  elet n' <$>     step e <*> pure b
              <|> pure (subst n e b)
-- prim operation
-- eval op. eval n. eval m
step (PrimOp op (Lit n) (Lit m)) = do
  let x = evalOp op
  return (Lit (n `x` m))
step (PrimOp op e1 e2) =
      PrimOp <$> pure op <*> step e1 <*> pure e2
  <|> PrimOp <$> pure op <*> pure e1 <*> step e2
step (Ann e t)  =  (Ann <$> step e <*> pure t)
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
    (ty, _) <- infertype e
    generalization ty

data Mode = Infer | Check Expr

infertype :: Expr -> TcMonad (Expr, Sub)
infertype e = infer e Infer

checktype :: Expr -> Expr -> TcMonad (Expr, Sub)
checktype e ty = infer e $ Check ty

infer :: Expr -> Mode -> TcMonad (Expr, Sub)
-- if Mode is (Check ty), ty is rho
infer (Var x) mode = do
  sigma <- lookupTy x
  instSigma sigma mode

infer (Lam bnd) Infer = do
  (x, body) <- unbind bnd
  tau <- genTVar estar
  let body' = subst x (Skolem x tau) body
  (rho, sub) <- infertype body'
  let res = epiWithName [(x, multiSubst sub tau)] rho
  return (res, sub)

infer (Lam bnd) (Check rho)  = do
  (x, body) <- unbind bnd
  (nm1, sigma1, sigma2, sub1) <- unpi rho
  substEnv sub1 $ do
     let body' = subst x (Skolem nm1 sigma1) body
     (ans, sub2) <- checktype body' sigma2
     return (ans, sub2 `compose` sub1)

infer (LamAnn bnd) Infer = do
  ((x, Embed t), body) <- unbind bnd
  (_, sub1) <- checktype t estar
  let t' = multiSubst sub1 t
  substEnv sub1 $ do
    let body' = subst x (Skolem x t') body
    (body_type, sub2) <- infertype body'
    let res = epiWithName [(x, multiSubst sub2 t')] body_type
    return (res, sub2 `compose` sub1)

infer (LamAnn bnd) (Check ty) = do
  ((x, Embed t), body) <- unbind bnd
  (_, sub1) <- checktype t estar
  let sigma = multiSubst sub1 t
  let ty' = multiSubst sub1 ty
  substEnv sub1 $ do
    (nm1, sigma1, sigma2, sub2) <- unpi ty'
    substEnv sub2 $ do
      let sigma' = multiSubst sub2 sigma
      sub3 <- subCheck sigma1 sigma'
      substEnv sub3 $ do
          let sigma'' = multiSubst sub3 sigma'
              sigma1' = multiSubst sub3 sigma1
          let body' = subst x (Skolem nm1 sigma'') body
          (_, sub4) <- checkSigma body' $ (multiSubst sub3 sigma2)
          let sub = sub4 `compose` sub3 `compose` sub2 `compose` sub1
          return (multiSubst sub ty, sub)

infer (App e1 e2) mode = do
  (rho1, sub1) <- infertype e1
  (nm1, sigma1, sigma2, sub2) <- unpi rho1
  substEnv (sub2 `compose` sub1) $ do
    (_, sub3) <- checkSigma e2 sigma1
    let app_type = multiSubst sub3 $ subst nm1 e2 sigma2
    (res, sub4) <- instSigma app_type mode
    return (res, sub4 `compose` sub3 `compose` sub2 `compose` sub1)

infer (Ann expr ty) mode = do
  (_, sub1) <- checktype ty estar
  let ty' = multiSubst sub1 ty
  substEnv sub1 $ do
     (_, sub2) <- checkSigma expr ty'
     let ty'' = multiSubst sub2 ty'
     substEnv sub2 $ do
        (res, sub3) <- instSigma ty'' mode
        return (res, sub3 `compose` sub2 `compose` sub1)

infer (Let bnd) mode = do
  ((x, Embed e), body) <- unbind bnd
  (_, s1) <- infertype e
  substEnv s1 $ do
      let e2 = subst x e body
      (rho, s2) <- infer e2 mode
      return (rho, s2 `compose` s1)

infer (Kind Star) mode = instSigma estar mode
infer Nat         mode = instSigma estar mode
infer (Lit{})     mode = instSigma Nat mode
infer (PrimOp op m n) mode = do
  (_, sub1) <- checktype m Nat
  substEnv sub1 $ do
      (_, sub2) <- checktype n Nat
      substEnv sub2 $ do
          (_, sub3) <- instSigma Nat mode
          return (Nat, sub3 `compose` sub2 `compose` sub1)
infer (Pi ty) mode     = inferFun ty mode
infer (Forall ty) mode = inferFun ty mode
infer (TVar _ t) mode   = instSigma t mode
infer (Skolem _ t) mode = instSigma t mode
infer (CastUp e) (Check rho1) = do
    rho2 <- oneStep rho1
    checktype e rho2
infer (CastDown e) mode = do
    (rho1, sub1) <- infertype e
    substEnv sub1 $ do
        sigma <- oneStep rho1
        (res, sub2) <- instSigma sigma mode
        return (res, sub2 `compose` sub1)

infer e _ = throwError $ T.concat ["Type checking ", showExpr e, " failed"]

inferFun ty mode = do
    (_, sub) <- instSigma estar mode
    substEnv sub $ do
       let p = multiSubst sub $ Pi ty
       (nm, a, r, sub) <- unpi p
       (_, sub1) <- checktype a estar
       substEnv sub1 $ do
           (_, sub2) <- checktype (multiSubst sub1 r) estar
           return (estar, sub2 `compose` sub1 `compose` sub)

compose :: Sub -> Sub -> Sub
compose s1 s2 = map (\(n, t) -> (n, multiSubst s1 t)) s2 ++ s1

-----------------------------------------
--  Unification
-----------------------------------------

-- | alpha equality
checkEq :: Expr -> Expr -> TcMonad ()
checkEq e1 e2 =
  unless (aeq e1 e2) $ throwError $
    T.concat ["Couldn't match: ", showExpr e1, " with ", showExpr e2]

-- unify tau tau
unify :: Expr -> Expr -> TcMonad Sub
unify (TVar n _)   (TVar n2 _) | n == n2 = return []
unify (TVar n k)    t                    = varBind n k t
unify  t           (TVar n k)            = varBind n k t
unify (CastUp e)   (CastUp e2)           = unify e e2
unify (CastDown e) (CastDown e2)         = unify e e2
unify (App n m)    (App a b )            = multiUnify [(n, a), (m, b)]
unify (Ann n m)    (Ann a b)             = multiUnify [(n, a), (m, b)]
unify  e1           e2       | aeq e1 e2 = return []
unify  e1           e2                   = throwError $ T.concat ["unification ", showExpr e1, " and ", showExpr e2, " falied"]

multiUnify :: [(Expr, Expr)] -> TcMonad Sub
multiUnify [] = return []
multiUnify ((t1,t2):tl) = do
    sub1 <- unify t1 t2
    sub2 <- substEnv sub1 $ multiUnify (map (\(x,y)->(multiSubst sub1 x, multiSubst sub1 y)) tl)
    return $ sub2 `compose` sub1

varBind :: TmName -> Expr -> Expr -> TcMonad Sub
varBind n k t = do
   (_, sub1) <- checktype t k
   let t' = multiSubst sub1 t
   freevar <- ftv t'
   unless ( not $ n `elem` (map fst freevar)) $
      throwError $ T.concat ["occur check fails: ", showExpr (Var n), ", ", showExpr t']
   return $ [(n,t')] `compose` sub1

-----------------------------------------
--  Polymorphic Relation
-----------------------------------------

-- dsk
subCheck :: Expr -> Expr -> TcMonad Sub
subCheck sigma1 sigma2 = do
    (skole, rho) <- pr sigma2
    let skole' = map (\(Skolem x _) -> x) skole
    sub <- subCheckRho sigma1 rho
    t1 <- fmap (map fst) $ substEnv sub ftvctx
    t2 <- fmap (map fst) . ftv $ multiSubst sub sigma1
    t3 <- fmap (map fst) . ftv $ multiSubst sub sigma2
    let bad_fv = skole' `intersect` (t1 ++ t2 ++ t3)
    if null bad_fv
    then return sub
    else throwError $ T.concat ["Type ", showExpr sigma1, " is not as least as polymorphic as type ", showExpr sigma2]

-- dsk*
subCheckRho :: Expr -> Expr -> TcMonad Sub
-- SPEC
subCheckRho sigma1@(Forall _) rho2 = do
    rho1 <- instantiate sigma1
    subCheckRho rho1 rho2
-- FUN
subCheckRho rho1 rho2@(Pi _) = fun rho1 rho2
subCheckRho rho1@(Pi _) rho2 = fun rho1 rho2
-- OTHER-CASE
subCheckRho rho1 rho2 = unify rho1 rho2

fun :: Expr -> Expr -> TcMonad Sub
fun rho1 rho2 = do
    (nm1, a1, r1, sub1) <- unpi rho1
    (nm2, a2, r2, sub2) <- unpi (multiSubst sub1 rho2)
    sub3 <- subCheck a2 (multiSubst sub2 a1)
    let sub4 = sub3 `compose` sub2 `compose` sub1
    let a1' = multiSubst sub4 a1
        a2' = multiSubst sub4 a2
    let subst1 = sub4
        subst2 = [(nm2, Skolem nm1 a1')] `compose` sub4
        rho1' = multiSubst subst1 r1
        rho2' = multiSubst subst2 r2
    sub5 <- subCheckRho rho1' rho2'
    return $ sub5 `compose` sub4

unpi (Pi bd) = do
    (tele, body) <- unbind bd
    let Cons bnd = tele
        ((nm, Embed t), rest) = unrebind bnd
    newnm <- genName
    let sub = [(nm, Skolem newnm t)]
    return (newnm, t, mkpi (substTele sub rest) (multiSubst sub body), [])
unpi tau = do
    nm1 <- genName
    a1 <- genTVar estar
    r1 <- genTVar estar
    sub <- unify tau $ epiWithName [(nm1, a1)] r1
    return (nm1, a1, r1, sub)

mkpi tele body =
    case tele of Empty -> body
                 _     -> Pi (bind tele body)

-----------------------------------------
--  Generalization
-----------------------------------------

-- GEN INFER
inferSigma :: Expr -> TcMonad (Expr, Sub)
inferSigma expr = do
    (rho, sub) <- infertype expr
    sigma <- generalization rho
    return (sigma, sub)

-- GEN CHECK
checkSigma :: Expr -> Expr -> TcMonad (Expr, Sub)
checkSigma expr sigma = do
    (skole, rho) <- pr sigma
    let skole' = map (\(Skolem x _) -> x) skole
    (res, sub) <- checktype expr rho
    t1 <- fmap (map fst) $ substEnv sub ftvctx
    t2 <- fmap (map fst) . ftv $ multiSubst sub sigma
    let bad_fv = skole' `intersect` (t1 ++ t2)
    if null bad_fv
    then return (res, sub)
    else throwError $ T.concat ["CheckSigma ", showExpr expr, " : ", showExpr sigma, "fail"]

-----------------------------------------
--  Instantiation
-----------------------------------------

instSigma ::  Expr -> Mode -> TcMonad (Expr, Sub)
-- INST INFER
instSigma t Infer = do
    ty <- instantiate t
    return (ty, [])
-- INST CHECK
instSigma t (Check ty) = do
    sub <- subCheckRho t ty
    return (multiSubst sub ty, sub)

-----------------------------------------
--  Pr: floating foralls.
-----------------------------------------

-- pr
pr :: Expr -> TcMonad ([Expr], Expr)
-- PR-POLY
pr (Forall bd) = do
    (tele, body_type) <- unbind bd
    go tele [] body_type
    where go Empty acc body_type = do
            (acc', rho) <- pr body_type
            return (acc ++ acc', rho)
          go (Cons bnd) acc body_type = do
            let ((nm, Embed t), rest) = unrebind bnd
            x <- genSkolemVar t
            let sub = [(nm, x)]
                rest' = substTele sub rest
                body_type' = multiSubst sub body_type
            go rest' (acc ++ [x]) body_type'
-- PR-FUN
pr (Pi bd) = do
    (tele, body_type) <- unbind bd
    (skole, rho) <- pr body_type
    if null skole
    then return ([], Pi bd)
    else return (skole, Pi (bind tele rho))
-- PR-OTHER-CASE
pr t = return ([], t)

