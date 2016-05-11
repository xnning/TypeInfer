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

          | TVar TmName

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
  isvar (TVar tm) = Just (SubstName tm)
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

estar :: Expr
estar = Star

eapp :: Expr -> Expr -> Expr
eapp = App

elet :: String -> Expr -> Expr -> Expr
elet n e1 e2 = Let (bind (s2n n, embed e1) e2)

mkTele :: [(String, Expr)] -> Tele
mkTele []          = Empty
mkTele ((x,e) : t) = Cons (rebind (string2Name x, Embed e) (mkTele t))

mkforall :: Tele -> Expr -> Expr
mkforall tele body =
    case tele of Empty -> body
                 _     -> Forall (bind tele body)

mkpi :: Tele -> Expr -> Expr
mkpi tele body =
    case tele of Empty -> body
                 _     -> Pi (bind tele body)
