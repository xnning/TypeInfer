module PrettyPrint (showExpr) where

import qualified Data.Text as T
import           Text.PrettyPrint.ANSI.Leijen (Doc, (<+>), (<>), text, dot, colon)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Unbound.Generics.LocallyNameless

import           Syntax


class Pretty p where
  ppr :: (Applicative m, LFresh m) => p -> m Doc

instance Pretty Expr where
  ppr (Var x) = return . text . show $ x
  ppr (App e es) = PP.parens <$> ((<+>) <$> ppr e <*> (ppr es))
  ppr (Lam bnd) = lunbind bnd $ \(delta, b) -> do
    let delta' = text . show $ delta
    b' <- ppr b
    return (PP.parens $ text "λ" <> delta' <+> dot <+> b')
  ppr (Kind Star) = return $ PP.char '★'
  ppr (Pi bnd) = lunbind bnd $ \(delta, b) -> do
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
  ppr (Let bnd) = lunbind bnd $ \((x, Embed e1), e2) -> do
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
  ppr (Fun e1 e2) = do
    e1' <- ppr e1
    e2' <- ppr e2
    return (PP.parens $ e1' <+> text "→" <+> e2' )

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

showExpr :: Expr -> T.Text
showExpr = T.pack . show . runLFreshM . ppr

isEmpty :: Tele -> Bool
isEmpty Empty = True
isEmpty _ = False
