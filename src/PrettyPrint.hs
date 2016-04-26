module PrettyPrint (showExpr, showCheckedExpr) where

import qualified Data.Text as T
import           Text.PrettyPrint.ANSI.Leijen (Doc, (<+>), (<>), text, dot, colon)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Unbound.Generics.LocallyNameless

import           Syntax


class Pretty p where
  ppr :: (Applicative m, Fresh m) => p -> m Doc

instance Pretty Expr where
  ppr (Var x) = return . text . show $ x
  ppr (App e es) = PP.parens <$> ((<+>) <$> ppr e <*> (ppr es))
  ppr (Lam bnd) = unbind bnd >>= \(delta, b) -> do
    let delta' = text . show $ delta
    b' <- ppr b
    return (PP.parens $ text "λ" <> delta' <+> dot <+> b')
  ppr Star = return $ PP.char '★'
  ppr (Pi bnd) = unbind bnd >>= \(delta, b) -> do
    let Cons bb = delta
    let ((x, Embed t), bb') = unrebind bb
    b' <- ppr b
    if (show x == "_" && isEmpty bb')
      then do
        t' <- ppr t
        return (PP.parens $ t' <+> text "→" <+> b')
      else do
        delta' <- ppr delta
        return (PP.parens $ text "Π" <> delta' <+> dot <+> b')
  ppr (Forall bnd) = unbind bnd >>= \(delta, b) -> do
    let Cons bb = delta
    let ((x, Embed t), bb') = unrebind bb
    b' <- ppr b
    if (show x == "_" && isEmpty bb')
      then do
        t' <- ppr t
        return (PP.parens $ t' <+> text "→" <+> b')
      else do
        delta' <- ppr delta
        return (PP.parens $ text "∀" <> delta' <+> dot <+> b')
  ppr (Let bnd) = unbind bnd >>= \((x, Embed e1), e2) -> do
    e1' <- ppr e1
    e2' <- ppr e2
    return (text "let" <+> (text . show $ x) <+> PP.equals <+> e1' <+> text "in" <+> e2')
  ppr Nat = return $ text "nat"
  ppr (Lit n) = return . text . show $ n
  ppr (PrimOp op e1 e2) = do
    e1' <- ppr e1
    e2' <- ppr e2
    op' <- ppr op
    return $ PP.parens (e1' <+> op' <+> e2')
  ppr (LamAnn bnd) = unbind bnd >>= \((x, Embed ann), body) -> do
    let x' = text . show $ x
    ann' <- ppr ann
    body' <- ppr body
    return (PP.parens $ text "λ" <> x' <+> text ":" <+> ann' <+> dot <+> body')
  ppr (CastUp e) = do
    e' <- ppr e
    return (PP.parens $ text "cast↑" <+> e')
  ppr (CastDown e) = do
    e' <- ppr e
    return (PP.parens $ text "cast↓" <+> e')
  ppr (Ann e1 e2) = do
    e1' <- ppr e1
    e2' <- ppr e2
    return (PP.parens $ e1' <+> text ":" <+> e2')

instance Pretty Operation where
  ppr Add = return . text $ "+"
  ppr Mult = return . text $ "*"
  ppr Sub = return . text $ "-"

instance Pretty Tele where
  ppr Empty = return PP.empty
  ppr (Cons bnd) = do
    t' <- ppr t
    bnd' <- ppr b'
    return ((PP.parens $ (text . show $ x) <+> colon <+> t') <> bnd')

    where
      ((x, Embed t), b') = unrebind bnd

instance Pretty CTele where
  ppr CEmpty = return PP.empty
  ppr (CCons bnd) = do
    t' <- ppr t
    bnd' <- ppr b'
    return ((PP.parens $ (text . show $ x) <+> colon <+> t') <> bnd')

    where
      ((x, Embed t), b') = unrebind bnd

instance Pretty CheckedExpr where
  ppr (CVar x _) = return . text .show $ x
  ppr (CTVar x _) = return . text . show $ x
  ppr (CApp e es _) = PP.parens <$> ((<+>) <$> ppr e <*> (ppr es))
  ppr (CLam bnd _) = unbind bnd >>= \(delta, b) -> do
    let delta' = text . show $ delta
    b' <- ppr b
    return (PP.parens $ text "λ" <> delta' <+> dot <+> b')
  ppr CStar = return $ PP.char '★'
  ppr (CPi bnd) = unbind bnd >>= \(delta, b) -> do
    let CCons bb = delta
    let ((x, Embed t), bb') = unrebind bb
    b' <- ppr b
    if (show x == "_" && isCEmpty bb')
      then do
        t' <- ppr t
        return (PP.parens $ t' <+> text "→" <+> b')
      else do
        delta' <- ppr delta
        return (PP.parens $ text "Π" <> delta' <+> dot <+> b')
  ppr (CForall bnd) = unbind bnd >>= \(delta, b) -> do
    let CCons bb = delta
    let ((x, Embed t), bb') = unrebind bb
    b' <- ppr b
    if (show x == "_" && isCEmpty bb')
      then do
        t' <- ppr t
        return (PP.parens $ t' <+> text "→" <+> b')
      else do
        delta' <- ppr delta
        return (PP.parens $ text "∀" <> delta' <+> dot <+> b')
  ppr (CLet bnd _) = unbind bnd >>= \((x, Embed e1), e2) -> do
    e1' <- ppr e1
    e2' <- ppr e2
    return (text "let" <+> (text . show $ x) <+> PP.equals <+> e1' <+> text "in" <+> e2')
  ppr CNat = return $ text "nat"
  ppr (CLit n) = return . text . show $ n
  ppr (CPrimOp op e1 e2) = do
    e1' <- ppr e1
    e2' <- ppr e2
    op' <- ppr op
    return $ PP.parens (e1' <+> op' <+> e2')
  ppr (CCastUp e _) = do
    e' <- ppr e
    return (PP.parens $ text "cast↑" <+> e')
  ppr (CCastDown e _) = do
    e' <- ppr e
    return (PP.parens $ text "cast↓" <+> e')
  ppr (CAnn e1 e2 _) = do
    e1' <- ppr e1
    e2' <- ppr e2
    return (PP.parens $ e1' <+> text ":" <+> e2')

showExpr :: Expr -> T.Text
showExpr = T.pack . show . runFreshM . ppr

showCheckedExpr :: CheckedExpr -> T.Text
showCheckedExpr = T.pack . show . runFreshM . ppr

isEmpty :: Tele -> Bool
isEmpty Empty = True
isEmpty _ = False

isCEmpty :: CTele -> Bool
isCEmpty CEmpty = True
isCEmpty _ = False
