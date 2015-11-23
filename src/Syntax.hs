{-# LANGUAGE DeriveGeneric, DeriveDataTypeable, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, ScopedTypeVariables, OverloadedStrings  #-}

module Syntax where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless

type TmName = Name Expr

-- | Classifier
data ClassTag = Prog
              | Logic
  deriving (Eq, Show, Generic, Typeable)

-- | Positivity
data PosTag = Pos
            | Neg
  deriving (Eq, Show)

data Tele = Empty
          | Cons (Rebind (TmName,Embed Expr) Tele)
  deriving (Show, Generic, Typeable)

-- | Syntax of the core, with optimization of aggregate bindings
data Expr = Var TmName
          | App Expr Expr
          | Lam (Bind TmName Expr)
          | Fun Expr Expr
          | Pi (Bind Tele Expr)
          | Kind Kinds

          | Let (Bind (TmName, Embed Expr) Expr)
          | Nat
          | Lit Int
          | PrimOp Operation Expr Expr
  deriving (Show, Generic, Typeable)

data Operation = Mult
               | Sub
               | Add
  deriving (Show, Generic, Typeable)

addExpr :: Expr -> Expr -> Expr
addExpr = PrimOp Add

subExpr :: Expr -> Expr -> Expr
subExpr = PrimOp Sub

multExpr :: Expr -> Expr -> Expr
multExpr = PrimOp Mult

data Kinds = Star
  deriving (Show, Generic, Typeable)

instance Alpha ClassTag
instance Alpha Expr
instance Alpha Operation
instance Alpha Kinds
instance Alpha Tele

instance Subst Expr Operation
instance Subst Expr Kinds
instance Subst Expr Tele
instance Subst Expr ClassTag

instance Subst Expr Expr where
  isvar (Var v) = Just (SubstName v)
  isvar _ = Nothing


-- Examples

-- \ x : ⋆ . \ y : x . y
polyid :: Expr
polyid = elam "y" (evar "y")


-- pi x : ⋆ . x -> x
polyidty :: Expr
polyidty = epi [("x", estar)] (earr (evar "x") (evar "x"))

-- smart constructors

evar :: String -> Expr
evar = Var . string2Name

elam :: String -> Expr -> Expr
elam t b = Lam (bind (string2Name t) b)

epi :: [(String, Expr)] -> Expr -> Expr
epi t b = Pi (bind (mkTele t) b)

epiWithName :: [(TmName, Expr)] -> Expr -> Expr
epiWithName t b = let pi =  foldr (\(n, t) acc -> Cons (rebind (n, Embed t) acc)) Empty t in  Pi (bind pi b)

earr :: Expr -> Expr -> Expr
earr t1 t2 = Fun t1 t2

estar :: Expr
estar = Kind Star

eapp :: Expr -> Expr -> Expr
eapp = App

elet :: String -> Expr -> Expr -> Expr
elet n e1 e2 = Let (bind (s2n n, embed e1) e2)

mkTele :: [(String, Expr)] -> Tele
mkTele []          = Empty
mkTele ((x,e) : t) = Cons (rebind (string2Name x, Embed e) (mkTele t))
