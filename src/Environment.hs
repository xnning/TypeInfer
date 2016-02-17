{-# LANGUAGE OverloadedStrings, TemplateHaskell, FlexibleContexts #-}

module Environment (
    lookupTy,
    extendCtx,
    runTcMonad,
    TcMonad,
    initialEnv,
    multiSubst,
    ftv,
    instantiate,
    generalization,
    substEnv,
    genName,
    genSkolemVar,
    genTVar,
    substTele,
    ftvctx,
    Sub
    ) where

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import qualified Data.Text as T
import           Unbound.Generics.LocallyNameless

import           Syntax
import qualified Data.Set as Set
import           PrettyPrint

type Env = [(TmName, Expr)]
type Sub = [(TmName, Expr)]
data Context = Ctx {_env :: Env}

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

-- change env

extendCtx :: (MonadState Context m) => Env -> m a -> m a
extendCtx d act = do
  origin <- gets _env
  withNewEnv (d ++ origin) act

withNewEnv :: (MonadState Context m) => Env -> m a -> m a
withNewEnv env act = do
  origin <- gets _env
  put $ Ctx {_env = env}
  res <- act
  put $ Ctx {_env = origin}
  return res

substEnv ::  (MonadState Context m)  => Sub -> m a -> m a
substEnv sub act = do
  origin <- gets _env
  let env = map (\(t,e) -> (t, multiSubst sub e)) origin
  withNewEnv env act

-- subst

multiSubst :: Sub -> Expr -> Expr
multiSubst sub typ = (foldl (\ty (x, t) -> subst x t ty) typ sub)

substTele :: Sub -> Tele -> Tele
substTele sub Empty = Empty
substTele sub (Cons rb) = Cons $ rebind (x, Embed (multiSubst sub t)) (substTele sub b)
  where
    ((x, Embed t), b) = unrebind rb

-- generate name
genName :: (Fresh m) => m TmName
genName = fresh (string2Name "a")

genTVar :: (Fresh m) => Expr -> m Expr
genTVar t = do nm <- genName
               return $ TVar nm t

genSkolemVar :: (Fresh m) => Expr -> m Expr
genSkolemVar t = do nm <- genName
                    return $ Skolem nm t

-- instantiation used in var
instantiate :: (MonadState Context m, MonadError T.Text m, Fresh m) => Expr -> m Expr
instantiate ty = case ty of
     Forall bnd -> do (bind, b) <- unbind bnd
                      work bind b
     _          -> return ty
  where
     work Empty body     = instantiate body
     work (Cons rb) body = do
         let ((x, Embed t), b) = unrebind rb
         tvar <- genTVar t
         work (subst x tvar b)
              (subst x tvar body)

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

ftv :: (MonadState Context m, MonadError T.Text m, Fresh m) => Expr -> m Freevar
ftv (Var    n  ) = return [(n, undefined)]
ftv (Skolem n k) = do
    f1 <- ftv k
    return $ [(n, k)] `ftv_union` f1
ftv (TVar   n k) = do
    f1 <- ftv k
    return $ [(n, k)] `ftv_union` f1
ftv (App  t1 t2) = ftv_do_union t1 t2
ftv (Ann   e  t) = ftv_do_union e  t
ftv (Pi     bnd) = ftv_fun bnd
ftv (Forall bnd) = ftv_fun bnd
ftv (CastUp   e) = ftv e
ftv (CastDown e) = ftv e
ftv (Lam    bnd) = do
     (x, body) <- unbind bnd
     body'     <- ftv body
     return $ body' `ftv_diff` [(x, undefined)]
ftv (Let    bnd) = do
     ((x, Embed e), body) <- unbind bnd
     e'    <- ftv e
     body' <- ftv body
     return $ e' `ftv_union` body' `ftv_diff` [(x, undefined)]
ftv           _  = return []

ftv_do_union :: (MonadState Context m, MonadError T.Text m, Fresh m) => Expr -> Expr -> m Freevar
ftv_do_union e1 e2 = do
    e1' <- ftv e1
    e2' <- ftv e2
    return $ e1' `ftv_union` e2'

ftv_fun :: (MonadState Context m, MonadError T.Text m, Fresh m) => Bind Tele Expr -> m Freevar
ftv_fun bnd = do
     (bind, b) <- unbind bnd
     bind'     <- ftvtele bind
     b'        <- ftv b
     bound     <- boundtele bind
     return    $ bind' `ftv_union` b' `ftv_diff` bound

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

