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

data Mode = Infer | Check Expr

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
    (e', sub) <- infertype e
    let ty =  multiSubst sub e'
    ty' <- generalization ty
    return ty'

type Sub = [(TmName, Expr)]

infertype :: Expr -> TcMonad (Expr, Sub)
infertype e = infer e Infer

checktype :: Expr -> Expr -> TcMonad (Expr, Sub)
checktype e ty = infer e $ Check ty

infer :: Expr -> Mode -> TcMonad (Expr, Sub)
-- if Mode is (Check ty), ty is rho
infer (Var x) mode = do
  sigma <- lookupTy x
  t <- instSigma sigma mode
  return t

infer (Lam bnd) Infer = do
  (x, body) <- unbind bnd
  newName <- genName
  (body_type, sub) <- extendCtx [(x, TVar newName estar)] $ infertype body
  let res = epiWithName [(x, multiSubst sub $ TVar newName estar)] body_type
  (_, sub2) <- checktype res estar
  return (res, sub2 `compose` sub)

infer (Lam bnd) (Check rho1)  = do
  (x, body) <- unbind bnd
  (nm1, a1, r1, b1, sub1) <- unpi rho1
  (ans, sub3) <- substEnv sub1 $ do
    let sub2 = [(nm1, Skolem x a1)] `compose` sub1
    extendCtx [(x, multiSubst sub1 a1)] $ checktype body (mkpi (substTele sub2 r1) (multiSubst sub2 b1))
  return (ans, sub3 `compose` sub1)

infer (LamAnn bnd) Infer = do
  ((x, Embed t), body) <- unbind bnd
  (_, sub1) <- checktype t estar
  (body_type, sub2) <- substEnv sub1 $ extendCtx [(x, multiSubst sub1 t)] $ infertype body
  let sub = sub2 `compose` sub1
  let res = epiWithName [(x, multiSubst sub t)] body_type
  return (res, sub)

infer (LamAnn bnd) (Check ty) = do
  ((x, Embed t), body) <- unbind bnd
  (nm1, a1, r1, b1, sub1) <- unpi ty
  (_, sub2) <- checktype t estar
  substEnv (sub2 `compose` sub1) $ do
    sub3 <- subCheck a1 t
    substEnv sub3 $ do
        let sub4 = sub3 `compose` sub2 `compose` sub1
        extendCtx [(x, multiSubst sub4 t)] $ do
            (_, sub5) <- checkSigma body $ mkpi (substTele sub4 r1) (multiSubst sub4 b1)
            return (multiSubst (sub5 `compose` sub4) ty, sub5 `compose` sub4)

infer (App m n) mode = do
  (rho1, sub1) <- infertype m
  (nm1, a1, r1, b1, sub2) <- unpi rho1
  let sub = sub2 `compose` sub1
  substEnv sub $ do
    (_, sub3) <- checkSigma n a1
    let sub4 = sub3 `compose` sub
    let app_type = case r1 of Empty -> b1
                              _     -> Pi (bind (substTele sub4 r1) (multiSubst sub4 b1))
    (res, sub5) <- instSigma app_type mode
    return (res, sub5 `compose` sub4)

infer (Ann expr ty) mode = do
  (_, sub1) <- checktype ty estar
  substEnv sub1 $ do
     (_, sub2) <- checkSigma expr ty
     substEnv sub2 $ do
        (res, sub3) <- instSigma ty mode
        return (res, sub3 `compose` sub2 `compose` sub1)

infer (Let bnd) mode = do
  ((x, Embed e), body) <- unbind bnd
  (et, s1) <- infertype e
  let e2 = multiSubst ([(x, multiSubst s1 e)] `compose` s1) body
  (rho, s2) <- infer e2 mode
  return (rho, s2 `compose` s1)

infer (Kind Star) Infer = return (estar, [])
infer (Kind Star) (Check ty) = do
    sub <- unification ty estar
    return (estar, sub)

infer Nat Infer = return (estar, [])
infer Nat (Check ty) = do
    sub <- unification ty estar
    return (estar, sub)
infer (Lit{}) Infer = return (Nat, [])
infer (Lit{}) (Check ty) = do
    sub <- unification ty Nat
    return (Nat, sub)
infer (PrimOp op m n) mode = do
  (t1, s1) <- infertype m
  substEnv s1 $ do
     (t2, se) <- infertype n
     let s2 = se `compose` s1
     s3 <- unification (multiSubst s2 t1) Nat
     s4 <- unification (multiSubst s3 t2) Nat
     case mode of Infer -> return (Nat, s4 `compose` s3 `compose` s2 `compose` s1)
                  Check ty -> do
                             s5 <- unification ty Nat
                             return (Nat, s5 `compose` s4 `compose` s3 `compose` s2 `compose` s1)
infer (Pi ty) mode = do
    sub <- case mode of Infer -> return []
                        Check typ -> unification typ estar
    let (Pi ty') = multiSubst sub (Pi ty)
    (tele, body) <- unbind ty'
    (_, sub2) <- go tele body
    return (estar, sub `compose` sub2)
    where
        go Empty body = checktype body estar
        go (Cons bnd) body = do
            let ((x, Embed t), rest) = unrebind bnd
            (_, sub) <- checktype t estar
            extendCtx [(x, t)] $ do (res, sub2) <- go (substTele sub rest) (multiSubst sub body)
                                    return $ (res, sub `compose` sub2)

infer (Forall ty) mode = do
    sub <- case mode of Infer -> return []
                        Check typ -> unification typ estar
    let (Forall ty') = multiSubst sub (Forall ty)
    (tele, body) <- unbind ty'
    (_, sub2) <- go tele body
    return (estar, sub `compose` sub2)
    where
        go Empty body = checktype body estar
        go (Cons bnd) body = do
            let ((x, Embed t), rest) = unrebind bnd
            (_, sub) <- checktype t estar
            extendCtx [(x, t)] $ do (res, sub2) <- go (substTele sub rest) (multiSubst sub body)
                                    return $ (res, sub `compose` sub2)

infer (TVar _ t) Infer = return (t, [])
infer (TVar _ t) (Check ty) = do
    sub <- unification t ty
    return (multiSubst sub t, sub)

infer e _ = throwError $ T.concat ["Type checking ", showExpr e, " failed"]

-- helper functions

checkfail e ty = throwError $ T.concat ["Type checking failed, expect ", showExpr e, " to have type ", showExpr ty]

check :: Expr -> Expr -> TcMonad ()
check m a = do
  (b, _) <- infertype m
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
getType Nat = return  estar
getType (Lit{}) = return Nat
getType (PrimOp{}) = return Nat
getType e = throwError $ T.concat ["unexpected type in unification ", showExpr e]

-- TODO: castup castdown let ect. appear in unification
unification :: Expr -> Expr -> TcMonad Sub
unification t1 t2 = do
    t1' <- getType t1
    t2' <- getType t2
    checkEq t1' t2'
    unify t1 t2
   where unify  Nat          Nat                     = return []
         unify (Kind Star)  (Kind Star)              = return []
         unify (TVar n m)   (TVar n2 m2)   | n == n2 = return []
         unify (Skolem n m) (Skolem n2 m2) | n == n2 = return []
         unify (TVar n _)    t                       = varBind n t
         unify  t           (TVar n _)               = varBind n t
         unify  e1  e2                  | aeq e1 e2  = return []
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

