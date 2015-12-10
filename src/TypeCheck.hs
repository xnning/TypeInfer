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

done :: MonadPlus m => m a
done = mzero

-- | Small step, call-by-value operational semantics
step :: Expr -> MaybeT FreshM Expr
step (Var{}) = done
step (TVar{}) = done
step (Skolem{}) = done
step (Kind{}) = done
step (Lam{}) = done
step (Pi{}) = done
step (Lit{}) = done
step (Nat) = done
step (App (Lam bnd) t2) = do
  (delta, b) <- unbind bnd
  return $ subst delta t2 b
step (App t1 t2) =
  App <$> step t1 <*> pure t2
  <|> App <$> pure t1 <*> step t2
step (Let bnd) = do
  ((n, Embed e), b) <- unbind bnd
  let n' = name2String n
  elet n' <$> step e <*> pure b <|> pure (subst n e b)
step (PrimOp op (Lit n) (Lit m)) = do
  let x = evalOp op
  return (Lit (n `x` m))
step (PrimOp op e1 e2) =
  PrimOp <$> pure op <*> step e1 <*> pure e2
  <|> PrimOp <$> pure op <*> pure e1 <*> step e2
step (CastUp{}) = done
step (CastDown (CastUp e)) = return e
step (CastDown e) = CastDown <$> step e

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

-- | type checker with positivity and contractiveness test
typecheck :: Expr -> (Either T.Text Expr)
typecheck e = runTcMonad initialEnv $ do
    (e', sub) <- infer e
    let ty =  multiSubst sub e'
    ty' <- generalization ty
    return ty'

type Sub = [(TmName, Expr)]

infer :: Expr -> TcMonad (Expr, Sub)
infer (Var x) = do
  sigma <- lookupTy x
  t <- instantiate sigma
  return (t, [])

infer (Lam bnd) = do
  (x, body) <- unbind bnd
  newName <- genName
  (body_type, sub) <- extendCtx [(x, TVar newName estar)] $ infer body
  return (Fun (multiSubst sub $ TVar newName estar) body_type, sub)

infer (App m n) = do
  (t1, s1) <- infer m
  substEnv s1 $ do
        (t2, se) <- infer n
        let s2 = se `compose` s1
        newName <- genName
        s3 <- unification (multiSubst s2 t1) (Fun t2 $ TVar newName estar)
        return (multiSubst s3 $ TVar newName estar, s3 `compose` s2 `compose` s1)

infer (Let bnd) = do
  ((x, Embed e), e2) <- unbind bnd
  (t1, s1) <- infer e
  sigma <- substEnv s1 $ generalization t1
  extendCtx [(x, sigma)] $ do
    (t2, s2) <- substEnv s1 $ infer e2
    return (t2, s2 `compose` s1)

infer (Kind Star) = return (estar, [])
infer (Fun m n) = do
  (t1, s1) <- infer m
  substEnv s1 $ do
     (t2, se) <- infer n
     let s2 = se `compose` s1
     s3 <- unification (multiSubst s2 t1) estar
     s4 <- unification (multiSubst s3 t2) estar
     return (estar, s4 `compose` s3 `compose` s2 `compose` s1)

infer Nat = return (estar, [])
infer (Lit{}) = return (Nat, [])
infer (PrimOp op m n) = do
  (t1, s1) <- infer m
  substEnv s1 $ do
     (t2, se) <- infer n
     let s2 = se `compose` s1
     s3 <- unification (multiSubst s2 t1) Nat
     s4 <- unification (multiSubst s3 t2) Nat
     return (Nat, s4 `compose` s3 `compose` s2 `compose` s1)
infer e = throwError $ T.concat ["Type checking ", showExpr e, " failed"]


-- helper functions

check :: Expr -> Expr -> TcMonad ()
check m a = do
  (b, _) <- infer m
  checkEq b a

checkArg :: Expr -> Tele -> TcMonad ()
checkArg _ Empty = return ()
checkArg e (Cons rb) = do
  let ((x, Embed a), t') = unrebind rb
  check e a

checkDelta :: Tele -> TcMonad ()
checkDelta Empty = return ()
checkDelta (Cons bnd) = do
  extendCtx [(x, t)] (checkDelta t')

  where
    ((x, Embed t), t') = unrebind bnd

unPi :: Expr -> TcMonad (Bind Tele Expr)
unPi (Pi bnd) = return bnd
unPi e = throwError $ T.concat ["Expected pi type, got ", showExpr e, " instead"]

-- | alpha equality
checkEq :: Expr -> Expr -> TcMonad ()
checkEq e1 e2 =
  unless (aeq e1 e2) $ throwError $
    T.concat ["Couldn't match: ", showExpr e1, " with ", showExpr e2]

oneStep :: (MonadError T.Text m) => Expr -> m Expr
oneStep e = do
  case runFreshM . runMaybeT $ (step e) of
    Nothing -> throwError $ T.concat ["Cannot reduce ", showExpr e]
    Just e' -> return e'


getType :: Expr -> TcMonad Expr
getType (Kind Star) = return estar
getType (Skolem _ t) = return t
getType (TVar _ t)   = return t
getType (Fun e1 e2) = do
    e1' <- getType e1
    e2' <- getType e2
    checkEq e1' estar
    checkEq e2' estar
    return estar
getType Nat = return  estar
getType (Lit{}) = return Nat
getType (PrimOp{}) = return Nat
getType e = throwError $ T.concat ["unexpected type in unification ", showExpr e]

unification :: Expr -> Expr -> TcMonad Sub
unification t1 t2 = do
    t1' <- getType t1
    t2' <- getType t2
    checkEq t1' t2'
    unify t1 t2
   where unify (Fun t11 t12) (Fun t21 t22) =  do
             sub <- unification t12 t22
             sub2 <- unification (multiSubst sub t11) (multiSubst sub t21)
             return $ sub2 `compose` sub
         unify (App t1 ts1) (App t2 ts2)             = unify (Fun ts1 t1) (Fun ts2 t2)
         unify  Nat          Nat                     = return []
         unify (Kind Star)  (Kind Star)              = return []
         unify (TVar n m)   (TVar n2 m2)   | n == n2 = return []
         unify (Skolem n m) (Skolem n2 m2) | n == n2 = return []
         unify (TVar n _)    t                       = varBind n t
         unify  t           (TVar n _)               = varBind n t
         unify e1 e2 = throwError $ T.concat ["unification ", showExpr e1, " and ", showExpr e2, " falied"]
         varBind n t = do freevar <- ftv t
                          if n `elem` (map fst freevar) then throwError $ T.concat ["occur check fails: ", showExpr (Var n), ", ", showExpr t]
                          else return [(n,t)]

compose :: Sub -> Sub -> Sub
compose s1 s2 = map (\(n, t) -> (n, multiSubst s1 t)) s2 ++ s1

-----------------------------------------
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
subCheckRho rho1 rho2 = unification rho1 rho2

fun :: Expr -> Expr -> TcMonad Sub
fun rho1 rho2 = do
    (nm1, a1, r1, b1, sub1) <- unpi rho1
    (nm2, a2, r2, b2, sub2) <- unpi (multiSubst sub1 rho2)
    sub3 <- subCheck a2 (multiSubst sub2 a1)
    let sub4 = sub3 `compose` sub2 `compose` sub1
    let a1' = multiSubst sub4 a1
        a2' = multiSubst sub4 a2
    newName1 <-genName
    newName2 <-genName
    let subst1 = [(nm1, Skolem newName1 a1')] `compose` sub4
        subst2 = [(nm2, Skolem (if aeq a1' a2' then newName1 else newName2) a2')] `compose` sub4
        rho1' = mkpi (substTele subst1 r1) (multiSubst subst2 b1)
        rho2' = mkpi (substTele subst1 r2) (multiSubst subst2 b2)
    sub5 <- subCheckRho rho1' rho2'
    return $ sub5 `compose` sub4

unpi (Pi bd) = do
    (tele, body) <- unbind bd
    let Cons bnd = tele
        ((nm, Embed t), rest) = unrebind bnd
    return (nm, t, rest, body, [])
unpi tau = do
    x <- genName
    y <- genName
    nm1 <- genName
    let a1 = TVar x estar
        r1 = TVar y estar
    sub <- unification tau $ epiWithName [(nm1, a1)] r1
    return (nm1, multiSubst sub a1, Empty, multiSubst sub r1, sub)

mkpi tele body =
    case tele of Empty -> body
                 _     -> Pi (bind tele body)

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

instSigma ::  Expr -> Mode -> TcMonad (Expr, Sub)
-- INST INFER
instSigma t Infer = do
    ty <- instantiate t
    return (ty, [])
-- INST CHECK
instSigma t (Check ty) = do
    sub <- subCheck t ty
    return (multiSubst sub ty, sub)

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
            x <- genName
            let sub = [(nm, Skolem x t)]
                rest' = substTele sub rest
                body_type' = multiSubst sub body_type
            go rest' (acc ++ [Skolem x t]) body_type'
-- PR-FUN
pr (Pi bd) = do
    (tele, body_type) <- unbind bd
    (skole, rho) <- pr body_type
    if null skole
    then return ([], Pi bd)
    else return (skole, Pi (bind tele rho))
-- PR-OTHER-CASE
pr t = return ([], t)

