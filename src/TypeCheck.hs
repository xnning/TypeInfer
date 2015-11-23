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

done :: MonadPlus m => m a
done = mzero

-- | Small step, call-by-value operational semantics
step :: Expr -> MaybeT FreshM Expr
step (Var{}) = done
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
  extendCtxWithTvar [(newName, estar)]
  (body_type, sub) <- extendCtx [(x, Var newName)] $ infer body
  return (Fun (multiSubst sub $ Var newName) body_type, sub)

infer (App m n) = do
  (t1, s1) <- infer m
  substEnv s1 $ do
        (t2, se) <- infer n
        let s2 = se `compose` s1
        newName <- genName
        extendCtxWithTvar [(newName, estar)]
        s3 <- unification (multiSubst s2 t1) (Fun t2 $ Var newName)
        return (multiSubst s3 $ Var newName, s3 `compose` s2 `compose` s1)

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
infer e = throwError $ T.concat ["Type checking ", showExpr e, " falied"]


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
getType (Var n) = lookupTVar n
getType (Fun e1 e2) = do
    e1' <- getType e1
    e2' <- getType e2
    checkEq e1' estar
    checkEq e2' estar
    return estar
getType Nat = return  estar
getType (Lit{}) = return Nat
getType (PrimOp{}) = return Nat
getType e = throwError $ T.concat ["get type ", showExpr e, " falied"]

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
         unify (App t1 ts1) (App t2 ts2) = unify (Fun ts1 t1) (Fun ts2 t2)
         unify (Var n) t = varBind n t
         unify t (Var n) = varBind n t
         unify Nat Nat   = return []
         unify (Kind Star) (Kind Star) = return []
         unify e1 e2 = throwError $ T.concat ["unification ", showExpr e1, " and ", showExpr e2, " falied"]
         varBind n t = if aeq t (Var n) then return []
                       else do freevar <- ftv t
                               if n `Set.member` freevar then throwError $ T.concat ["occur check fails: ", showExpr (Var n), ", ", showExpr t]
                               else return [(n,t)]

compose :: Sub -> Sub -> Sub
compose s1 s2 = map (\(n, t) -> (n, multiSubst s1 t)) s2 ++ s1

