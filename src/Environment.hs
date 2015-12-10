{-# LANGUAGE OverloadedStrings, TemplateHaskell, FlexibleContexts #-}

module Environment (
    lookupTy,
    extendCtx,
    runTcMonad,
    TcMonad,
    initialEnv,
    multiSubst,
    teleToEnv,
    ftv,
    instantiate,
    generalization,
    substEnv,
    genName,
    substTele,
    ftvctx
    ) where

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import qualified Data.Text as T
import           Lens.Micro
import           Lens.Micro.TH
import           Unbound.Generics.LocallyNameless

import           Syntax
import qualified Data.Set as Set
import           PrettyPrint

type Env = [(TmName, Expr)]
type Sub = [(TmName, Expr)]
data Context = Ctx {_env :: Env}

makeLenses ''Context

type TcMonad = FreshMT (StateT Context (Except T.Text))


runTcMonad :: Context -> TcMonad a -> (Either T.Text a)
runTcMonad env m = runExcept $ evalStateT (runFreshMT m) env

initialEnv :: Context
initialEnv = Ctx []

lookupTy :: (MonadState Context m, MonadError T.Text m) => TmName -> m Expr
lookupTy v = do
  ctx <- gets _env
  case lookup v ctx of
    Nothing  -> throwError $ T.concat ["Ty Not in scope: ", T.pack . show $ v]
    Just res -> return res

extendCtx :: (MonadState Context m) => Env -> m a -> m a
extendCtx d c = do
  ctx <- get
  withNewEnv (d ++ (_env ctx)) c

multiSubst :: Sub -> Expr -> Expr
multiSubst sub typ = (foldl (\ty (x, t) -> subst x t ty) typ sub)

substEnv ::  (MonadState Context m)  => Sub -> m a -> m a
substEnv sub c = do
  ctx <- get
  let env = map (\(t,e) -> (t, multiSubst sub e)) $ _env ctx
  withNewEnv env c

withNewEnv :: (MonadState Context m) => Env -> m a -> m a
withNewEnv env c = do
  ctx <- get
  put ctx{_env = env}
  res <- c
  ctx2 <- get
  put ctx2{_env = _env ctx}
  return res

teleToEnv :: Tele -> Env
teleToEnv Empty  = []
teleToEnv (Cons rb) = (x, t) : teleToEnv b
  where
    ((x, Embed t), b) = unrebind rb

substTele :: Sub -> Tele -> Tele
substTele sub Empty = Empty
substTele sub (Cons rb) = Cons $ rebind (x, Embed (multiSubst sub t)) (substTele sub b)
  where
    ((x, Embed t), b) = unrebind rb

genName :: (Fresh m) => m TmName
genName = fresh (string2Name "a")

-- instantiation used in var
instantiate :: (MonadState Context m, MonadError T.Text m, Fresh m) => Expr -> m Expr
instantiate ty = case ty of
     Forall bnd -> do
        (bind, b) <- unbind bnd
        work bind b
     x -> return x
    where
     work Empty body = instantiate body
     work (Cons rb) body = do
         let ((x, Embed t), b) = unrebind rb
         newName <- genName
         let b' = subst x (TVar newName t) b
             body' = subst x (TVar newName t) body
         work b' body'

-- generalization used in let
generalization :: (MonadState Context m, MonadError T.Text m, Fresh m) => Expr -> m Expr
generalization ty = do
    free <- ftv ty
    free_ctx <- ftvctx
    let freewithty = free `ftv_diff` free_ctx
    if null freewithty then return ty
    else return $ forallWithName freewithty ty

-- free variables
type Freevar = [(TmName, Expr)]

ftv ::  (MonadState Context m, MonadError T.Text m, Fresh m) => Expr -> m Freevar
ftv (Var n) = return [(n, undefined)]
ftv (Skolem n k) = return [(n, k)]
ftv (TVar n k) = return [(n, k)]
ftv (App t1 t2) = do
    t1' <- ftv t1
    t2' <- ftv t2
    return (t1' `ftv_union` t2')
ftv (Fun t1 t2) = do
    t1' <- ftv t1
    t2' <- ftv t2
    return (t1' `ftv_union` t2')
ftv (Pi bnd) = do
     (bind, b) <- unbind bnd
     bind' <- ftvtele bind
     b' <- ftv b
     return $ bind' `ftv_union` b'
ftv (Forall bnd) = do
     (bind, b) <- unbind bnd
     bind' <- ftvtele bind
     b' <- ftv b
     bound <- boundtele bind
     return $ bind' `ftv_union` b' `ftv_diff` bound
ftv _ = return []

ftvtele ::  (MonadState Context m, MonadError T.Text m, Fresh m) => Tele -> m Freevar
ftvtele Empty = return []
ftvtele (Cons rb) = do
   let ((x, Embed t), b) = unrebind rb
   t' <- ftv t
   b' <- ftvtele b
   return $ t' `ftv_union` b'

boundtele ::  (MonadState Context m, MonadError T.Text m, Fresh m) => Tele -> m Freevar
boundtele Empty = return []
boundtele (Cons rb) = do
   let ((x, Embed t), b) = unrebind rb
   b' <- boundtele b
   return $ [(x, t)] `ftv_union` b'


ftvctx ::(MonadState Context m, MonadError T.Text m, Fresh m) =>  m Freevar
ftvctx = do
    ctx <- gets _env
    foldM (\fv (_, t)-> do
                t' <- ftv t
                return $ fv `ftv_union` t')
          []
          ctx

ftv_diff :: Freevar -> Freevar -> Freevar
ftv_diff s1 s2 = filter (\(nm, _) -> not $ nm `elem` lst) s1 where lst = map fst s2

ftv_union :: Freevar -> Freevar -> Freevar
ftv_union s1 s2 = foldr (\var@(nm, _) acc -> if nm `elem` lst then acc else acc ++ [var] ) s1 s2 where lst = map fst s1

