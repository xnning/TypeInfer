{-# LANGUAGE OverloadedStrings, TemplateHaskell, FlexibleContexts #-}

module Environment (
      TcMonad
    , runTcMonad
    , initialEnv

    , generalization
    , instantiate

    , lookupVarTy
    , ctxAddVar
    , ctxAddCstrVar
    , ctxAddLetVar
    , ctxGenAddTVar

    , existsVar
    , existsTVar
    , tvarExistsBefore

    , genVar
    , genName

    , throwAfterVar
    , getUnsolvedAndThrowAfter
    , addMarker
    , deleteAfterMarker

    , genTVarBefore
    , addSubsitution

    , applyEnv
    , applyEnvAfter
    , printEnv

    , occur_check
    , traverseI
    , wellDefinedBeforeTVar
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

import           Data.List
import           Data.Maybe (fromJust, listToMaybe)

-----------------------------------------
--  Data Constructor
-----------------------------------------

type TypeConstraint = Expr
type Substitution = Expr
data VarInfo =   VarInfo TmName (Maybe TypeConstraint, Maybe Substitution)
               | TVarInfo TmName (Maybe Substitution)
               | Marker TmName
               deriving (Show)
type Env = [VarInfo]

data Context = Ctx {_env :: Env}

type TcMonad = FreshMT (StateT Context (Except T.Text))

-----------------------------------------
--  Run Interface
-----------------------------------------

runTcMonad :: Context -> TcMonad a -> (Either T.Text a)
runTcMonad env m = runExcept $ evalStateT (runFreshMT m) env

initialEnv :: Context
initialEnv = Ctx []

-----------------------------------------
--  Utility on Data Constructor
-----------------------------------------

showEnv :: Env -> String
showEnv env = unwords $ map (show) env

printEnv :: (MonadState Context m) => m String
printEnv = do
  env <- gets _env
  return $ showEnv env

getVarInfo :: (MonadState Context m, MonadError T.Text m) => TmName -> m VarInfo
getVarInfo tm = do
  env <- gets _env
  let vm = listToMaybe [x | x@(VarInfo tm2 _) <- env, tm2 == tm]
  case vm of
    Just vi -> return vi
    Nothing -> throwError $ T.concat ["var not in scope: ", T.pack . show $ tm, ".\ncurrent context:\n", T.pack . showEnv $ env]

getTVarInfo :: (MonadState Context m, MonadError T.Text m) => TmName -> m VarInfo
getTVarInfo tm = do
  env <- gets _env
  let vm = listToMaybe [x | x@(TVarInfo tm2 _) <- env, tm2 == tm]
  case vm of
    Just vi -> return vi
    Nothing -> throwError $ T.concat ["tvar not in scope: ", T.pack . show $ tm, ".\ncurrent context:\n", T.pack . showEnv $ env]

infoGetType :: VarInfo -> Maybe TypeConstraint
infoGetType (VarInfo _ (ty, _)) = ty

tinfoGetSubst :: VarInfo -> Maybe Substitution
tinfoGetSubst (TVarInfo _ sub) = sub

makeVarInfo :: TmName -> Maybe TypeConstraint -> Maybe Substitution -> VarInfo
makeVarInfo tm ty ts = VarInfo tm (ty, ts)

makeTVarInfo :: TmName -> Maybe Substitution -> VarInfo
makeTVarInfo tm ts = TVarInfo tm ts

-----------------------------------------
--  Utility on Fetching Information
-----------------------------------------

existsVar :: (MonadState Context m, MonadError T.Text m) => TmName -> m ()
existsVar tm = void $ getVarInfo tm

existsTVar :: (MonadState Context m, MonadError T.Text m) => TmName -> m ()
existsTVar tm = void $ getTVarInfo tm

findTVarInfo :: TmName -> VarInfo -> Bool
findTVarInfo tm e =
  case e of TVarInfo tm2 _ -> tm == tm2
            _              -> False

findVarInfo :: TmName -> VarInfo -> Bool
findVarInfo tm e =
  case e of VarInfo tm2 _ -> tm == tm2
            _             -> False

tvarExistsBefore :: (MonadState Context m, MonadError T.Text m) => TmName -> TmName -> m Bool
tvarExistsBefore v1 v2 = do
  existsTVar v1
  existsTVar v2

  env <- gets _env
  let i1 = fromJust $ findIndex (findTVarInfo v1) env
  let i2 = fromJust $ findIndex (findTVarInfo v2) env
  return (i1 < i2)

lookupVarTy :: (MonadState Context m, MonadError T.Text m) => TmName -> m TypeConstraint
lookupVarTy v = do
  tyc <- (infoGetType <$> getVarInfo v)
  case tyc of
     Just ty -> return ty
     _ -> throwError $ T.concat ["var ", T.pack . show $ v, " has no type in env"]

lookupTySubst :: (MonadState Context m, MonadError T.Text m) => TmName -> m (Maybe Substitution)
lookupTySubst v = do
  info <- getTVarInfo v
  return (tinfoGetSubst info)

-----------------------------------------
--  Apply Environment
-----------------------------------------

applyVarInfo ::VarInfo -> Expr -> Expr
applyVarInfo v e = case v of
                      (TVarInfo nm (Just sub)) -> subst nm sub e
                      (VarInfo nm (_, Just sub)) -> subst nm sub e
                      _ -> e

applyEnv :: (MonadState Context m) => Expr -> m Expr
applyEnv e = do
    env <- gets _env
    return $ foldr applyVarInfo e env

applyEnvAfter :: (MonadState Context m) => TmName -> Expr -> m Expr
applyEnvAfter vm e = do
  env <- gets _env
  let idx = fromJust $ findIndex (findVarInfo vm) env
      (before, after) = splitAt idx env
  return $ foldr applyVarInfo e after

-----------------------------------------
--  Change Environment: addition
-----------------------------------------

ctxAdd :: (MonadState Context m) => VarInfo -> m ()
ctxAdd info = do
  origin <- gets _env
  put $ Ctx {_env = origin ++ [info]}

ctxAddVar :: (MonadState Context m) => TmName -> m ()
ctxAddVar tm = ctxAdd $ makeVarInfo tm Nothing Nothing

ctxAddCstrVar :: (MonadState Context m) => TmName -> TypeConstraint -> m ()
ctxAddCstrVar tm ty = ctxAdd $ makeVarInfo tm (Just ty) Nothing

ctxAddLetVar :: (MonadState Context m) => TmName -> TypeConstraint -> Substitution -> m ()
ctxAddLetVar tm ty ts = ctxAdd $ makeVarInfo tm (Just ty) (Just ts)

ctxAddTVar :: (MonadState Context m) => TmName -> m ()
ctxAddTVar tm = ctxAdd $ makeTVarInfo tm Nothing

ctxGenAddTVar :: (MonadState Context m, Fresh m) => m Expr
ctxGenAddTVar = do
  nm <- genName
  ctxAdd $ makeTVarInfo nm Nothing
  return (TVar nm)

addMarker :: (MonadState Context m, Fresh m) => m VarInfo
addMarker = do
  marker <- Marker <$> genName
  ctxAdd marker
  return marker

-----------------------------------------
--  Change Environment: deletion
-----------------------------------------

throwAfterVar :: (MonadState Context m) => TmName -> m ()
throwAfterVar nm = do
  env <- gets _env
  let filter_fun d = case d of VarInfo nm2 _ -> nm /= nm2
                               _             -> True
      new_env = takeWhile filter_fun env
  put $ Ctx {_env = new_env}

getUnsolvedTVar :: Env -> Env
getUnsolvedTVar [] = []
getUnsolvedTVar (x:l) =
  case x of
     TVarInfo tm Nothing -> x : getUnsolvedTVar l
     _ -> getUnsolvedTVar l

getUnsolvedAndThrowAfter :: (MonadState Context m) => TmName -> m ()
getUnsolvedAndThrowAfter vm = do
  env <- gets _env
  let idx = fromJust $ findIndex (findVarInfo vm) env
      (before, after) = splitAt idx env
      unsolved = getUnsolvedTVar after
  put $ Ctx {_env = before ++ unsolved}

deleteAfterMarker :: (MonadState Context m) => VarInfo -> m ()
deleteAfterMarker (Marker nm) = do
  env <- gets _env
  let filter_fun d = case d of Marker nm2 -> nm /= nm2
                               _          -> True
      new_env = takeWhile filter_fun env
  put $ Ctx {_env = new_env}

-----------------------------------------
--  Change Environment: insertion
-----------------------------------------

genTVarBefore :: (MonadState Context m, Fresh m) => TmName -> m Expr
genTVarBefore tm = do
  env <- gets _env
  let idx = fromJust $ findIndex (findTVarInfo tm) env
      (before, after) = splitAt idx env
  nm <- genName
  let tvar = makeTVarInfo nm Nothing
  put $ Ctx {_env = before ++ [tvar] ++ after}
  return (TVar nm)

addSubsitution :: (MonadState Context m, Fresh m) => TmName -> Substitution -> m ()
addSubsitution tm sub = do
  env <- gets _env
  let idx = fromJust $ findIndex (findTVarInfo tm) env
      (before, (TVarInfo _ Nothing) :after) = splitAt idx env
  let tvar' = makeTVarInfo tm (Just sub)
  put $ Ctx {_env = before ++ [tvar'] ++ after}

-----------------------------------------
--  Generate Names
-----------------------------------------

genName :: (Fresh m) => m TmName
genName = fresh (string2Name "a")

genVar :: (Fresh m) => m Expr
genVar = Var <$> genName

genTVar :: (Fresh m) => m Expr
genTVar = do nm <- genName
             return (TVar nm)

-----------------------------------------
--  instantiation
-----------------------------------------

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
         tvar <- ctxGenAddTVar
         work (subst x tvar b)
              (subst x tvar body)

-----------------------------------------
--  generalization
-----------------------------------------

-- generalization used in let
generalization :: (MonadState Context m, MonadError T.Text m, Fresh m) => Expr -> m Expr
generalization ty = do
  free <- ftv ty
  free_ctx <- ftvctx
  let freewithty =  free `ftv_diff` free_ctx
  return $ if null freewithty then ty
           else forallWithName (zip freewithty (repeat estar)) ty

-----------------------------------------
--  Free Variables
-----------------------------------------

-- free variables
type Freevar = [TmName]

occur_check :: (MonadState Context m, MonadError T.Text m, Fresh m) => TmName -> Expr -> m ()
occur_check tm e = do
    names <- ftv e
    unless (notElem tm names) $
      throwError $ T.concat ["occur check fails: tvar ", T.pack . show $ tm, " in type ", showExpr e]

ftv :: (MonadState Context m, MonadError T.Text m, Fresh m) => Expr -> m Freevar
ftv (TVar     n ) = return [n]
ftv (App  t1 t2 ) = ftv_do_union t1 t2
ftv (Lam    bnd ) = do (x, body) <- unbind bnd
                       ftv body
ftv (LamAnn bnd ) = do ((x, Embed ty), body) <- unbind bnd
                       ftv_do_union ty body
ftv (CastUp   e ) = ftv e
ftv (CastDown e ) = ftv e
ftv (Ann   e  t ) = ftv_do_union e  t
ftv (Let    bnd ) = do ((x, Embed e), body) <- unbind bnd
                       ftv_do_union body e
ftv (Pi     bnd ) = ftv_fun bnd
ftv (Forall bnd ) = ftv_fun bnd
ftv (PrimOp _ e1 e2) = ftv_do_union e1 e2
ftv           _       = return []

ftv_do_union :: (MonadState Context m, MonadError T.Text m, Fresh m) => Expr -> Expr -> m Freevar
ftv_do_union e1 e2 = ftv_union <$> ftv e1 <*> ftv e2

ftv_fun :: (MonadState Context m, MonadError T.Text m, Fresh m) => Bind Tele Expr -> m Freevar
ftv_fun bnd = do
     (bind, b) <- unbind bnd
     ftv_union <$> ftvtele bind <*> ftv b

ftvtele ::  (MonadState Context m, MonadError T.Text m, Fresh m) => Tele -> m Freevar
ftvtele Empty = return []
ftvtele (Cons rb) = do
   let ((x, Embed t), b) = unrebind rb
   ftv_union <$> ftv t <*> ftvtele b

ftvinfo :: (MonadState Context m, MonadError T.Text m, Fresh m) => VarInfo -> m Freevar
ftvinfo (VarInfo _ (Just ty, _)) = (applyEnv ty) >>= ftv
ftvinfo _ = return []

ftvctx ::(MonadState Context m, MonadError T.Text m, Fresh m) =>  m Freevar
ftvctx =  do
    ctx <- gets _env
    foldM (\fv info -> do
                t' <- ftvinfo info
                return $ fv `ftv_union` t')
          []
          ctx

ftv_diff :: Freevar -> Freevar -> Freevar
ftv_diff s1 s2 = filter (\nm -> not $ nm `elem` s2) s1

ftv_union :: Freevar -> Freevar -> Freevar
ftv_union s1 s2 = foldr (\nm acc -> if nm `elem` s1 then acc else acc ++ [nm] ) s1 s2

-----------------------------------------
--  Well defined
-----------------------------------------

traverseI :: (MonadState Context m, MonadError T.Text m, Fresh m) => TmName -> Expr -> m Expr
traverseI alpha expr = go expr
  where -- I-Var
        go x@(Var _) = return x
        -- I-Star
        go Star = return Star
        go (TVar beta) = do
           beta_first <- beta `tvarExistsBefore` alpha
           -- I-EVar1
           if beta_first then return (TVar beta)
           -- I-EVar2
           else do
             alpha1 <- genTVarBefore alpha
             addSubsitution beta alpha1
             return alpha1
        -- I-Others
        go (App e1 e2) = App <$> go e2 <*> (applyEnv e2 >>= go)
        go (Lam bnd) = unbind bnd >>= \(x, body) -> (\body' -> Lam (bind x body')) <$> go body
        go (LamAnn bnd) = do
          ((x, Embed t), body) <- unbind bnd
          let makelamann =  \t' body' -> LamAnn (bind (x, embed t') body')
          makelamann <$> go t <*> go body
        go (CastUp e1) = CastUp <$> go e1
        go (CastDown e1) = CastDown <$> go e1
        go (Ann e1 e2) = Ann <$> go e1 <*> go e2
        go (Let bnd) = do
          ((x, Embed t), body) <- unbind bnd
          let makelet = \t' body' -> Let (bind (x, embed t') body')
          makelet <$> go t <*> go body
        go p@(Pi bnd) = do
          (x, t1, t2) <- unpi p
          let makepi = \t1' t2' -> epiWithName [(x, t1')] t2'
          makepi <$> go t1 <*> go t2
        go Nat = return Nat
        go x@Lit{} = return x
        go (PrimOp op e1 e2) = PrimOp op <$> go e1 <*> go e2


wellDefined :: (MonadState Context m, MonadError T.Text m, Fresh m) => Expr -> m ()
wellDefined (Var nm) = existsVar nm
wellDefined (TVar nm) = existsTVar nm
wellDefined Star = return ()
wellDefined (App e1 e2) = wellDefined e1 >> wellDefined e2
wellDefined (Lam bnd) = do
  (x, body) <- unbind bnd
  ctxAddVar x
  wellDefined body
  throwAfterVar x
wellDefined (CastUp x) = wellDefined x
wellDefined (CastDown x) = wellDefined x
wellDefined (Ann e1 e2) = wellDefined e1 >> wellDefined e2
wellDefined Nat = return ()
wellDefined (Lit _) = return ()
wellDefined (PrimOp _ e1 e2) = wellDefined e2 >> wellDefined e2
wellDefined p@(Pi bnd) = do
  (x, tau1, tau2) <- unpi p
  wellDefined tau1
  ctxAddCstrVar x tau1
  wellDefined tau2
  throwAfterVar x
wellDefined (Let bnd) = do
  ((n, Embed e), b) <- unbind bnd
  wellDefined e
  ctxAddVar n
  wellDefined b
  throwAfterVar n

wellDefinedBeforeTVar :: (MonadState Context m, MonadError T.Text m, Fresh m) => TmName -> Expr -> m ()
wellDefinedBeforeTVar tm e = do
  env <- gets _env
  let idx = fromJust $ findIndex (findTVarInfo tm) env
      (before, after) = splitAt idx env
  put $ Ctx {_env = before}
  wellDefined e
  put $ Ctx {_env = env}

-----------------------------------------
--  Utility
-----------------------------------------

unpi :: (Fresh m) => Expr -> m (TmName, Expr, Expr)
unpi (Pi bnd) = do
  (Cons tele, b) <- unbind bnd
  let ((x, Embed tau1), rest) = unrebind tele
      tau2 = mkpi rest b
  return (x, tau1, tau2)
