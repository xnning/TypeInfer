

haskell version

```haskell
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE RankNTypes #-}

module ExprChurch where

-- GADTs definition
-- data Expr a where
--   I :: Int -> Expr Int
--   B :: Bool -> Expr Bool
--   P :: Expr a -> Expr b -> Expr (a, b)

-- eval :: Expr a -> a
-- eval (I i) = i
-- eval (B b) = b
-- eval (P a b) = (eval a, eval b)

-- Church Encoding
newtype Expr t = Expr {
  unExpr :: forall expr .
            (Int -> expr Int) ->
            (Bool -> expr Bool) ->
            (forall a b . expr a -> expr b -> expr (a, b)) ->
            expr t
  }


-- Constructor
i :: Int -> Expr Int
i x = Expr (\i' _ _ -> i' x)

b :: Bool -> Expr Bool
b x = Expr (\_ b' _ -> b' x)

p :: Expr a -> Expr b -> Expr (a, b)
p x y = Expr (\i' b' p' -> p' (unExpr x i' b' p') (unExpr y i' b' p'))

-- Pattern matching
newtype Id a = Id { unId :: a }

eval :: Expr a -> a
eval e = unId $ unExpr e Id Id (\x y -> Id (unId x, unId y))

test :: IO ()
test = do
  let e = p (i 1) (b True)
  print $ eval e
```
\newpage

in original system (as in paper)
``` haskell
let Int : * = nat in
let String : * = nat in
let PairT : * = mu x : * -> * -> * . \a : * . \b : * . (c : *) -> (a -> b -> c) -> c in
let Pair : * = \a : * . \b : * . \x : a . \y : b .
    fold 3 [PairT a b] (\c : * . \f : a -> b -> c . f x y) in
let fst : * = \a : * . \b : * . \p : PairT a b . (unfold 3 p) a (\x : a . \y : b . x) in
let snd : * = \a : * . \b : * . \p : PairT a b . (unfold 3 p) b (\x : a . \y : b . y) in
let Expr : * = \t : * . (expr : * -> *) -> (Int -> expr Int) -> (String -> expr String)
        -> ((a : *) -> (b : *) -> expr a -> expr b -> expr (PairT a b)) -> expr t in
let I : * = \x : Int . fold 1 [Expr Int] \expr : * -> * .\i : Int -> expr Int .
        \s : String -> expr String .\p : (a : *) -> (b : *) -> expr a -> expr b -> expr (PairT a b) .
        i x in
let Id : * = \a : * . a in let P : * = \a : * .\b : * .\x : Expr a .\y : Expr b .
        fold 1 [Expr (PairT a b)] \expr : * -> * .\i : Int -> expr Int .
        \s : String -> expr String .\p : (a : *) -> (b : *) -> expr a -> expr b -> expr (PairT a b) .
        p a b ((unfold 1 x) expr i s p) ((unfold 1 y) expr i s p) in
let S : * = \x : Int . fold 1 [Expr Int] \expr : * -> * .\i : Int -> expr Int .
        \s : String -> expr String .\p : (a : *) -> (b : *) -> expr a -> expr b -> expr (PairT a b) .
        s x in
let eval : * = \t : * .\e : Expr t . unfold 1 (unfold 1 e) Id (\x : Int . fold 1 [Id Int] x)
        (\x : String . fold 1 [Id String] x) (\a : * .\b : * .\x : Id a .\y : Id b .
        fold 1 [Id (PairT a b)] Pair a b (unfold 1 x) (unfold 1 y)) in
let test : * = eval (PairT Int String) (P Int String (I 1) (S 2)) in
fst Int String test
```

\newpage

in current system with all annotations

``` haskell
let Int = nat in
let String = nat in
let PairT = \a:*.\b:*. /\(c:*)./\(/\a./\b.c).c in
let Pair = \a:*.\b:*.\x:a.\y:b.
        ((castup (castup (\c : * . \f : (/\a./\ b. c) . f x y))):(PairT a b)) in
let fst = \a:*.\b:*.\p:PairT a b. (castdown (castdown p)) a (\x : a . \y : b . x) in
let snd = \a:*.\b:*.\p:PairT a b. (castdown (castdown p)) b (\x : a . \y : b . y) in
let Expr = \t:*. /\(expr:/\*.*)./\(/\Int. expr Int). /\(/\String. expr String).
          /\(/\(a:*)(b:*)./\expr a./\ expr b. expr (PairT a b)). expr t in
let Id = \a:*. a in
let eval = \t:*. \e:Expr t. castdown ((castdown e) Id (\x:Int. ((castup x):(Id Int)))
        (\x:String. ((castup x):(Id String))) (\a:*.\b:*.\x:Id a.\y:Id b.
        ((castup (Pair a b (castdown x) (castdown y))):(Id (PairT a b))))) in
let I = \x:Int. ((castup (\expr:(/\*.*).\i:(/\Int.expr Int).\s:(/\String.expr String).
        \p:(/\(a:*)(b:*)./\expr a./\ expr b. expr (PairT a b)). i x) ):(Expr Int)) in
let S = \x:String. ((castup (\expr:(/\*.*).\i:(/\Int.expr Int).\s:(/\String.expr String).
        \p:(/\(a:*)(b:*)./\expr a./\ expr b. expr (PairT a b)). s x) ):(Expr String)) in
let P = \a:*.\b:*.\x:Expr a.\y:Expr b. ((castup (\expr:(/\*.*).\i:(/\Int.expr Int).
        \s:(/\String.expr String).\p:(/\(a:*)(b:*)./\expr a./\ expr b. expr (PairT a b)).
        p a b ((castdown x) expr i s p) ((castdown y) expr i s p))):(Expr (PairT a b))) in
let test =  eval (PairT Int String) (P Int String (I 1) (S 2))
in fst Int String test
```
\newpage

in current system without annotation

``` haskell
let Int = nat in
let String = nat in
let PairT = \a:*.\b:*.\/c./\(/\a./\b.c).c in
let Pair = ((\x.\y.castup (castup (\f. f x y))):(\/a.\/b./\a./\b.PairT a b)) in
let fst = (\p. (castdown (castdown p)) (\x.\y.x)):(\/a.\/b./\PairT a b. a) in
let snd = (\p. (castdown (castdown p)) (\x.\y.y)):(\/a.\/b./\PairT a b. b) in
let Expr = \/t. \/(expr:/\*.*)./\(/\Int. expr Int). /\(/\String. expr String).
        /\(\/a.\/b./\expr a./\expr b. expr (PairT a b)). expr t in
let Id = \a. a in
let eval = \e. e (\x. x) (\x. x) (\x.\y. (Pair x y)) in
let I = \x.     \i.\s.\p. i x in
let S = \x.     \i.\s.\p. s x in
let P = \x. \y. \i.\s.\p. p (x i s p) (y i s p) in
let test =  eval (P (I 1) (S 2)) in
fst test
```

