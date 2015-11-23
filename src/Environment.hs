{-# LANGUAGE OverloadedStrings, TemplateHaskell, FlexibleContexts #-}

module Environment (
    lookupTy,
    extendCtx,
    runTcMonad,
    TcMonad,
    initialEnv,
    multiSubst,
    teleToEnv,
    lookupTVar,
    extendCtxWithTvar,
    ftv,
    instantiate,
    generalization,
    substEnv,
    genName
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
data Context = Ctx {_env :: Env, _tvarenv :: Env}

makeLenses ''Context

type TcMonad = FreshMT (StateT Context (Except T.Text))


runTcMonad :: Context -> TcMonad a -> (Either T.Text a)
runTcMonad env m = runExcept $ evalStateT (runFreshMT m) env

initialEnv :: Context
initialEnv = Ctx [] []

lookupTy :: (MonadState Context m, MonadError T.Text m) => TmName -> m Expr
lookupTy v = do
  ctx <- gets _env
  case lookup v ctx of
    Nothing  -> throwError $ T.concat ["Ty Not in scope: ", T.pack . show $ v]
    Just res -> return res

lookupTVar :: (MonadState Context m, MonadError T.Text m) => TmName -> m Expr
lookupTVar v = do
  ctx <- gets _tvarenv
  case lookup v ctx of
    Nothing  -> throwError $ T.concat ["TVar Not in scope: ", T.pack . show $ v]
    Just res -> return res

extendCtx :: (MonadState Context m) => Env -> m a -> m a
extendCtx d c = do
  ctx <- get
  withNewEnv (d ++ (_env ctx)) c

extendCtxWithTvar :: (MonadState Context m) => Env -> m ()
extendCtxWithTvar d = do
  ctx <- get
  put ctx{_tvarenv = d ++ (_tvarenv ctx)}

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

genName :: (Fresh m) => m TmName
genName = fresh (string2Name "a")

-- instantiation used in var
instantiate :: (MonadState Context m, MonadError T.Text m, Fresh m) => Expr -> m Expr
instantiate ty = case ty of
     Pi bnd -> do
        (bind, b) <- unbind bnd
        work bind b
     x -> return x
    where
     work Empty body = return body
     work (Cons rb) body = do
         let ((x, Embed t), b) = unrebind rb
         newName <- genName
         extendCtxWithTvar [(newName, t)]
         let b' = subst x (Var newName) b
             body' = subst x (Var newName) body
         work b' body'

-- generalization used in let
generalization :: (MonadState Context m, MonadError T.Text m, Fresh m) => Expr -> m Expr
generalization ty = do
    free <- ftv ty
    free_ctx <- ftvctx
    let diff = free Set.\\ free_ctx
    freewithty <- mapM (\n -> do
                           t <- lookupTVar n
                           return (n, t))
                       (Set.toList diff)
    if null freewithty then return ty
    else return $ epiWithName freewithty ty

-- free variables
ftv ::  (MonadState Context m, MonadError T.Text m, Fresh m) => Expr -> m (Set.Set TmName)
ftv (Var n) = return $ Set.singleton n
ftv (App t1 t2) = do
    t1' <- ftv t1
    t2' <- ftv t2
    return (t1' `Set.union` t2')
ftv (Fun t1 t2) = do
    t1' <- ftv t1
    t2' <- ftv t2
    return (t1' `Set.union` t2')
ftv (Pi bnd) = do
     (bind, b) <- unbind bnd
     b' <- ftv b
     bind' <- ftvtele bind
     return $ b' Set.\\ bind'
ftv _ = return Set.empty

ftvtele ::  (MonadState Context m, MonadError T.Text m, Fresh m) => Tele -> m (Set.Set TmName)
ftvtele Empty = return Set.empty
ftvtele (Cons rb) = do
   let ((x, Embed t), b) = unrebind rb
   t' <- ftv t
   b' <- ftvtele b
   return $ t' `Set.union` b'

ftvctx ::(MonadState Context m, MonadError T.Text m, Fresh m) =>  m (Set.Set TmName)
ftvctx = do
    ctx <- gets _env
    foldM (\fv (_, t)-> do
                t' <- ftv t
                return $ fv `Set.union` t')
          Set.empty
          ctx


