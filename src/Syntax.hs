{-# LANGUAGE DeriveGeneric, DeriveDataTypeable, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, ScopedTypeVariables, OverloadedStrings  #-}

module Syntax where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless

type TmName = Name Expr

data Tele = Empty
          | Cons (Rebind (TmName,Embed Expr) Tele)
  deriving (Show, Generic, Typeable)

-- | Syntax of the core, with optimization of aggregate bindings
data Expr = Var TmName
          | Star
          | App Expr Expr
          | Lam (Bind TmName Expr)
          | LamAnn (Bind (TmName, Embed Expr) Expr)
          | CastUp Expr
          | CastDown Expr
          | Ann Expr Expr
          | Let (Bind (TmName, Embed Expr) Expr)

          -- rho sigma
          | Pi (Bind Tele Expr)
          | Forall (Bind Tele Expr)

          -- natural
          | Nat
          | Lit Int
          | PrimOp Operation Expr Expr

  deriving (Show, Generic, Typeable)

data Operation = Mult
               | Sub
               | Add
  deriving (Show, Generic, Typeable, Eq)

addExpr :: Expr -> Expr -> Expr
addExpr = PrimOp Add

subExpr :: Expr -> Expr -> Expr
subExpr = PrimOp Sub

multExpr :: Expr -> Expr -> Expr
multExpr = PrimOp Mult

instance Alpha Expr
instance Alpha Operation
instance Alpha Tele

instance Subst Expr Operation
instance Subst Expr Tele

instance Subst Expr Expr where
  isvar (Var tm) = Just (SubstName tm)
  isvar _        = Nothing

-- Examples

-- \ x : ⋆ . \ y : x . y
polyid :: Expr
polyid = elam "y" (evar "y")


-- pi x : ⋆ . x -> x
polyidty :: Expr
polyidty = epi [("x", estar)] (epi [("y", evar "x")] (evar "y"))

-- smart constructors

evar :: String -> Expr
evar = Var . string2Name

cevar :: String -> CheckedExpr -> CheckedExpr
cevar nm = CVar (string2Name nm)

tmname2c :: TmName -> CTmName
tmname2c = string2Name . show

ctvar :: String -> CheckedExpr -> CheckedExpr
ctvar e = CTVar (string2Name e)

evar2c :: TmName -> CheckedExpr -> CheckedExpr
evar2c nm = cevar (show nm)

elam :: String -> Expr -> Expr
elam t b = Lam (bind (string2Name t) b)

elamann :: String -> Expr -> Expr -> Expr
elamann t ann b = LamAnn (bind (s2n t, embed ann) b)

epi :: [(String, Expr)] -> Expr -> Expr
epi t b = Pi (bind (mkTele t) b)

epiNoDenp :: Expr -> Expr -> Expr
epiNoDenp t b = epi [("x", t)] b

epiWithName :: [(TmName, Expr)] -> Expr -> Expr
epiWithName t b = let pi =  foldr (\(n, t) acc -> Cons (rebind (n, Embed t) acc)) Empty t in  Pi (bind pi b)

eforall :: [(String, Expr)] -> Expr -> Expr
eforall t b = Forall (bind (mkTele t) b)

eforallStar :: String -> Expr -> Expr
eforallStar t b = eforall [(t, estar)] b

forallWithName :: [(TmName, Expr)] -> Expr -> Expr
forallWithName t b = let pi =  foldr (\(n, t) acc -> Cons (rebind (n, Embed t) acc)) Empty t in  Forall (bind pi b)

cforallWithName :: [(CTmName, CheckedExpr)] -> CheckedExpr -> CheckedExpr
cforallWithName t b = let pi =  foldr (\(n, t) acc -> CCons (rebind (n, Embed t) acc)) CEmpty t in  CForall (bind pi b)

estar :: Expr
estar = Star

eapp :: Expr -> Expr -> Expr
eapp = App

elet :: String -> Expr -> Expr -> Expr
elet n e1 e2 = Let (bind (s2n n, embed e1) e2)

mkTele :: [(String, Expr)] -> Tele
mkTele []          = Empty
mkTele ((x,e) : t) = Cons (rebind (string2Name x, Embed e) (mkTele t))

-----------------------------------------
--  Expr
-----------------------------------------

type CTmName = Name CheckedExpr
data CTele = CEmpty
           | CCons (Rebind (CTmName,Embed CheckedExpr) CTele)
  deriving (Show, Generic, Typeable)

type CType = CheckedExpr
data CheckedExpr = CVar CTmName CType
          | CStar
          | CApp CheckedExpr CheckedExpr CType
          | CLam (Bind CTmName CheckedExpr) CType
          | CLamAnn (Bind (CTmName, Embed CheckedExpr) CheckedExpr) CType
          | CCastUp CheckedExpr CType
          | CCastDown CheckedExpr CType
          | CAnn CheckedExpr CheckedExpr CType
          | CLet (Bind (CTmName, Embed CheckedExpr) CheckedExpr) CType

          -- rho sigma
          | CPi (Bind CTele CheckedExpr)
          | CForall (Bind CTele CheckedExpr)

          -- natural
          | CNat
          | CLit Int
          | CPrimOp Operation CheckedExpr CheckedExpr

          -- helper, not in syntax
          | CTVar CTmName CType
  deriving (Show, Generic, Typeable)

instance Alpha CheckedExpr
instance Alpha CTele

instance Subst CheckedExpr Operation
instance Subst CheckedExpr CTele
instance Subst CheckedExpr CheckedExpr where
  isvar (CVar tm _) = Just (SubstName tm)
  isvar (CTVar tm _) = Just (SubstName tm)
  isvar _           = Nothing

mkCTele :: [(String, CheckedExpr)] -> CTele
mkCTele []           = CEmpty
mkCTele ((x,e) : t)  = CCons (rebind (string2Name x, Embed e) (mkCTele t))

cepiWithName :: [(CTmName, CheckedExpr)] -> CheckedExpr -> CheckedExpr
cepiWithName t b = let pi =  foldr (\(n, t) acc -> CCons (rebind (n, Embed t) acc)) CEmpty t in  CPi (bind pi b)

expr_mkpi :: Tele -> Expr -> Expr
expr_mkpi tele body =
    case tele of Empty -> body
                 _     -> Pi (bind tele body)

mkpi :: CTele -> CheckedExpr -> CheckedExpr
mkpi tele body =
    case tele of CEmpty -> body
                 _     -> CPi (bind tele body)

expr_mkforall :: Tele -> Expr -> Expr
expr_mkforall tele body =
    case tele of Empty -> body
                 _     -> Forall (bind tele body)

mkforall :: CTele -> CheckedExpr -> CheckedExpr
mkforall tele body =
    case tele of CEmpty -> body
                 _     -> CForall (bind tele body)

getCheckedType :: CheckedExpr -> CheckedExpr
getCheckedType e = case e of
  CVar _ t      -> t
  CTVar _ t     -> t
  CStar         -> CStar
  CApp _ _ t    -> t
  CLam _ t      -> t
  CLamAnn _ t   -> t
  CCastDown _ t -> t
  CCastUp _ t   -> t
  CAnn _ _ t    -> t
  CLet _ t      -> t
  CPi _         -> CStar
  CForall _     -> CStar
  CNat          -> CStar
  CLit _        -> CNat
  CPrimOp _ _ _ -> CNat

changeCheckedType :: CheckedExpr -> CheckedExpr -> CheckedExpr
changeCheckedType e t = case e of
  CVar x _      -> CVar x t
  CTVar x _     -> CTVar x t
  CApp x1 x2 _  -> CApp x1 x2 t
  CLam x1 _     -> CLam x1 t
  CLamAnn x _   -> CLamAnn x t
  CCastDown x _ -> CCastDown x t
  CCastUp x _   -> CCastUp x t
  CAnn x1 x2 _  -> CAnn x1 x2 t
  CLet x _      -> CLet x t
  _ -> e

