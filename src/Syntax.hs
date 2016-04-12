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

          -- helper, not in syntax
          | TVar   TmName Expr
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

instance Alpha Expr
instance Alpha Operation
instance Alpha Tele

instance Subst Expr Operation
instance Subst Expr Tele

instance Subst Expr Expr where
  subst tm a expr = go expr
    where
      go (Var tm2)   | tm == tm2 = a
                     | otherwise = Var tm2
      go (TVar v ty) | tm == v = a
                     | otherwise = TVar v (go ty)
      go (App e1 e2) = App (go e1) (go e2)
      go (Lam bd)    = Lam (subst tm a bd)
      go (LamAnn bd) = LamAnn (subst tm a bd)
      go (CastDown e) = CastDown (go e)
      go (CastUp e  ) = CastUp (go e)
      go (Ann e1 e2 ) = Ann (go e1) (go e2)
      go (Let bd)     = Let (subst tm a bd)
      go (Pi bd)      = Pi (subst tm a bd)
      go (Forall bd)  = Forall (subst tm a bd)
      go (PrimOp op e1 e2) = PrimOp op (go e1) (go e2)
      go x            = x

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
