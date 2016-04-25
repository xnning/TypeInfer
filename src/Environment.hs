{-# LANGUAGE OverloadedStrings, TemplateHaskell, FlexibleContexts #-}

module Environment (
      TcMonad
    , runTcMonad
    , initialEnv

    , generalization
    , instantiate
    , skolemInstantiate

    , lookupVarTy
    , ctxAddCstrVar
    , ctxGenAddTVar

    , existsVar
    , existsTVar
    , varExistsBefore
    , tvarExistsBefore

    , genVar
    , genCName

    , throwAfterVar
    , addMarker
    , deleteAfterMarker

    , genTVarBefore
    , addSubsitution
    , monoInstantiate

    , applyEnv
    , printEnv
    , withEnv

    , occur_check
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

type TypeConstraint = CheckedExpr
type Substitution = CheckedExpr
data VarInfo =   VarInfo CTmName (Maybe TypeConstraint)
               | TVarInfo CTmName (TypeConstraint, Maybe Substitution)
               | Marker CTmName
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

getVarInfo :: (MonadState Context m, MonadError T.Text m) => CTmName -> m VarInfo
getVarInfo tm = do
  env <- gets _env
  let vm = listToMaybe [x | x@(VarInfo tm2 _) <- env, tm2 == tm]
  case vm of
    Just vi -> return vi
    Nothing -> throwError $ T.concat ["var not in scope: ", T.pack . show $ tm, ". current context:", T.pack . showEnv $ env]

getTVarInfo :: (MonadState Context m, MonadError T.Text m) => CTmName -> m VarInfo
getTVarInfo tm = do
  env <- gets _env
  let vm = listToMaybe [x | x@(TVarInfo tm2 _) <- env, tm2 == tm]
  case vm of
    Just vi -> return vi
    Nothing -> throwError $ T.concat ["tvar not in scope: ", T.pack . show $ tm]

infoGetType :: VarInfo -> Maybe TypeConstraint
infoGetType (VarInfo _ ty) = ty

tinfoGetType :: VarInfo -> TypeConstraint
tinfoGetType (TVarInfo _ (ty, sub)) = ty

tinfoGetSubst :: VarInfo -> Maybe Substitution
tinfoGetSubst (TVarInfo _ (_, sub)) = sub

makeVarInfo :: CTmName -> Maybe TypeConstraint -> VarInfo
makeVarInfo = VarInfo

makeTVarInfo :: CTmName -> TypeConstraint -> Maybe Substitution -> VarInfo
makeTVarInfo tm ty ts = TVarInfo tm (ty, ts)

-----------------------------------------
--  Utility on Fetching Information
-----------------------------------------

existsVar :: (MonadState Context m, MonadError T.Text m) => CTmName -> m ()
existsVar tm = getVarInfo tm >>= (\_ -> return ())

existsTVar :: (MonadState Context m, MonadError T.Text m) => CTmName -> m ()
existsTVar tm = getTVarInfo tm >>= (\_ -> return ())

findVarInfo :: CTmName -> VarInfo -> Bool
findVarInfo tm e =
  case e of VarInfo tm2 _ -> tm == tm2
            _             -> False

findTVarInfo :: CTmName -> VarInfo -> Bool
findTVarInfo tm e =
  case e of TVarInfo tm2 _ -> tm == tm2
            _             -> False

existsBefore :: (MonadState Context m, MonadError T.Text m) =>
    (CTmName -> m (), VarInfo -> Bool) -> (CTmName -> m (), VarInfo -> Bool)
    -> CTmName -> CTmName -> m Bool
existsBefore (exist1, index1) (exist2, index2) tm1 tm2= do
  exist1 tm1
  exist2 tm2

  env <- gets _env
  let i1 = fromJust $ findIndex index1 env
  let i2 = fromJust $ findIndex index2 env
  return (i1 < i2)

var_fun v = (existsVar, findVarInfo v)
tvar_fun v = (existsTVar, findTVarInfo v)

varExistsBefore :: (MonadState Context m, MonadError T.Text m) => CTmName -> CTmName -> m Bool
varExistsBefore v1 v2 = existsBefore (var_fun v1) (tvar_fun v2) v1 v2

tvarExistsBefore :: (MonadState Context m, MonadError T.Text m) => CTmName -> CTmName -> m Bool
tvarExistsBefore v1 v2 = existsBefore (tvar_fun v1) (tvar_fun v2) v1 v2

lookupVarTy :: (MonadState Context m, MonadError T.Text m) => CTmName -> m TypeConstraint
lookupVarTy v = do
  info <- getVarInfo v
  case (infoGetType info) of
    Just ty -> return ty
    Nothing -> throwError $ T.concat ["var has no type: ", T.pack . show $ v]

lookupTyCstr :: (MonadState Context m, MonadError T.Text m) => CTmName -> m TypeConstraint
lookupTyCstr v = do
  info <- getTVarInfo v
  return (tinfoGetType info)

lookupTySubst :: (MonadState Context m, MonadError T.Text m) => CTmName -> m (Maybe Substitution)
lookupTySubst v = do
  info <- getTVarInfo v
  return (tinfoGetSubst info)

-----------------------------------------
--  With Environment
-----------------------------------------

withEnv :: (MonadState Context m) => m a -> m a
withEnv block = do
  env <- gets _env
  res <- block
  put $ Ctx {_env = env}
  return res

-----------------------------------------
--  Apply Environment
-----------------------------------------

applyVarInfo ::VarInfo -> CheckedExpr -> CheckedExpr
applyVarInfo v e = case v of
                      (TVarInfo nm (_, Just sub)) -> subst nm sub e
                      _ -> e

applyEnv :: (MonadState Context m) => CheckedExpr -> m CheckedExpr
applyEnv e = do
    env <- gets _env
    return $ foldr applyVarInfo e env

-----------------------------------------
--  Change Environment: addition
-----------------------------------------

-- change env
_ctxAddVar :: (MonadState Context m) => CTmName -> Maybe TypeConstraint -> m ()
_ctxAddVar tm ty = do
  let info = makeVarInfo tm ty
  origin <- gets _env
  put $ Ctx {_env = origin ++ [info]}

ctxAddCstrVar :: (MonadState Context m) => CTmName -> TypeConstraint -> m ()
ctxAddCstrVar tm ty = _ctxAddVar tm (Just ty)

ctxAddTVar :: (MonadState Context m) => CTmName -> TypeConstraint -> m ()
ctxAddTVar tm ty = do
  let info = makeTVarInfo tm ty Nothing
  origin <- gets _env
  put $ Ctx {_env = origin ++ [info]}

ctxGenAddTVar :: (MonadState Context m, Fresh m) => TypeConstraint -> m CheckedExpr
ctxGenAddTVar ty = do
  nm <- genCName
  let info = makeTVarInfo nm ty Nothing
  origin <- gets _env
  put $ Ctx {_env = origin ++ [info]}
  return (CTVar nm ty)

addMarker :: (MonadState Context m, Fresh m) => m VarInfo
addMarker = do
  marker <- Marker <$> genCName
  env <- gets _env
  put $ Ctx {_env = env ++ [marker]}
  return marker

-----------------------------------------
--  Change Environment: deletion
-----------------------------------------

throwAfterVar :: (MonadState Context m) => CTmName -> m ()
throwAfterVar nm = do
  env <- gets _env
  let filter_fun d = case d of VarInfo nm2 _ -> nm /= nm2
                               _             -> True
      new_env = takeWhile filter_fun env
  put $ Ctx {_env = new_env}

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

genTVarBefore :: (MonadState Context m, Fresh m) => CTmName -> TypeConstraint -> m CheckedExpr
genTVarBefore tm ty = do
  env <- gets _env
  let idx = fromJust $ findIndex (findTVarInfo tm) env
      (before, after) = splitAt idx env
  nm <- genCName
  let tvar = makeTVarInfo nm ty Nothing
  put $ Ctx {_env = before ++ [tvar] ++ after}
  return (CTVar nm ty)

addSubsitution :: (MonadState Context m, Fresh m) => CTmName -> Substitution -> m ()
addSubsitution tm sub = do
  env <- gets _env
  let idx = fromJust $ findIndex (findTVarInfo tm) env
      (before, (TVarInfo _ (ty, Nothing)) :after) = splitAt idx env
  let tvar' = makeTVarInfo tm ty (Just sub)
  put $ Ctx {_env = before ++ [tvar'] ++ after}

monoInstantiate :: (MonadState Context m, Fresh m) => CTmName -> CheckedExpr -> m CheckedExpr
monoInstantiate tm (CForall bd) = do
    ((CCons bnd), body_type) <- unbind bd
    let ((nm, Embed t), rest) = unrebind bnd
    alpha <- genTVarBefore tm t
    return $ subst nm alpha (mkforall rest body_type)

-----------------------------------------
--  Generate Names
-----------------------------------------

genName :: (Fresh m) => m TmName
genName = fresh (string2Name "a")

genCName :: (Fresh m) => m CTmName
genCName = fresh (string2Name "a")

genVar :: (Fresh m) => m Expr
genVar = Var <$> genName

genTVar :: (Fresh m) => TypeConstraint -> m CheckedExpr
genTVar ty = do nm <- genCName
                return (CTVar nm ty)

-----------------------------------------
--  instantiation
-----------------------------------------

-- instantiation used in var
instantiate :: (MonadState Context m, MonadError T.Text m, Fresh m) => CheckedExpr -> m CheckedExpr
instantiate ty = case ty of
     CForall bnd -> do (bind, b) <- unbind bnd
                       work bind b
     _           -> return ty
  where
     work CEmpty body     = instantiate body
     work (CCons rb) body = do
         let ((x, Embed t), b) = unrebind rb
         tvar <- ctxGenAddTVar t
         work (subst x tvar b)
              (subst x tvar body)

-- instantiation used in var
skolemInstantiate :: (MonadState Context m, MonadError T.Text m, Fresh m) => CheckedExpr -> m CheckedExpr
skolemInstantiate ty = case ty of
     CForall bnd -> do (bind, b) <- unbind bnd
                       work bind b
     _           -> return ty
  where
     work CEmpty body     = skolemInstantiate body
     work (CCons rb) body = do
         let ((x, Embed t), b) = unrebind rb
         cm <- genCName
         ctxAddCstrVar cm t
         work (subst x (CVar cm t)  b)
              (subst x (CVar cm t) body)

-----------------------------------------
--  generalization
-----------------------------------------

-- generalization used in let
generalization :: (MonadState Context m, MonadError T.Text m, Fresh m) => CheckedExpr -> m CheckedExpr
generalization ty = do
  free <- ftv ty
  free_ctx <- ftvctx
  let freewithty =  free `ftv_diff` free_ctx
  return $ if null freewithty then ty
           else cforallWithName freewithty ty

-----------------------------------------
--  Free Variables
-----------------------------------------

-- free variables
type Freevar = [(CTmName, CheckedExpr)]

occur_check :: (MonadState Context m, MonadError T.Text m, Fresh m) => CTmName -> CheckedExpr -> m ()
occur_check tm e = do
    fvs <- ftv e
    let names = map fst fvs
    unless (notElem tm names) $
      throwError $ T.concat ["occur check fails: tvar ", T.pack . show $ tm, " in type ", showCheckedExpr e]

ftv :: (MonadState Context m, MonadError T.Text m, Fresh m) => CheckedExpr -> m Freevar
ftv (CTVar     n t) = return [(n, t)]
ftv (CApp  t1 t2 _) = ftv_do_union t1 t2
ftv (CLam    bnd _) = do (x, body) <- unbind bnd
                         ftv body
ftv (CLamAnn bnd _) = do ((x, Embed ty), body) <- unbind bnd
                         ftv_do_union ty body
ftv (CCastUp   e _) = ftv e
ftv (CCastDown e _) = ftv e
ftv (CAnn   e  t _) = ftv_do_union e  t
ftv (CLet    bnd _) = do ((x, Embed e), body) <- unbind bnd
                         ftv_do_union body e
ftv (CPi     bnd  ) = ftv_fun bnd
ftv (CForall bnd  ) = ftv_fun bnd
ftv (CPrimOp _ e1 e2) = ftv_do_union e1 e2
ftv           _       = return []

ftv_do_union :: (MonadState Context m, MonadError T.Text m, Fresh m) => CheckedExpr -> CheckedExpr -> m Freevar
ftv_do_union e1 e2 = do
    e1' <- ftv e1
    e2' <- ftv e2
    return $ e1' `ftv_union` e2'

ftv_fun :: (MonadState Context m, MonadError T.Text m, Fresh m) => Bind CTele CheckedExpr -> m Freevar
ftv_fun bnd = do
     (bind, b) <- unbind bnd
     bind'     <- ftvtele bind
     b'        <- ftv b
     return    $ bind' `ftv_union` b'

ftvtele ::  (MonadState Context m, MonadError T.Text m, Fresh m) => CTele -> m Freevar
ftvtele CEmpty = return []
ftvtele (CCons rb) = do
   let ((x, Embed t), b) = unrebind rb
   t' <- ftv t
   b' <- ftvtele b
   return $ t' `ftv_union` b'

ftvinfo :: (MonadState Context m, MonadError T.Text m, Fresh m) => VarInfo -> m Freevar
ftvinfo (VarInfo _ (Just ty)) = (applyEnv ty) >>= ftv
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
ftv_diff s1 s2 = filter (\(nm, _) -> not $ nm `elem` lst) s1 where lst = map fst s2

ftv_union :: Freevar -> Freevar -> Freevar
ftv_union s1 s2 = foldr (\var@(nm, _) acc -> if nm `elem` lst then acc else acc ++ [var] ) s1 s2 where lst = map fst s1

