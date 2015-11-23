# FunImpl

## Summary

`FunImpl` is a type checker and interpreter for the dependently typed
language `Fun` presented in the paper "Type-level Computation One Step
at a Time". It comes with a read-eval-print loop allowing one to
fiddle with `Fun`. This is an overview of how to interact.

## Installation ##

1. Make sure you have installed the dependencies:

    + Install GHC (version 7.8 or above)
    + Alex and Happy (install by `cabal install alex happy`)

2. Build and install

    We recommend installing in a sandbox by `cabal sandbox init`

    ```bash
    cabal update
    make
    ```

## Fun Cheatsheet

A program consists of a (possibly empty) list of datatypes or records,
each separated by ";", and an expression:

```
program := datatype1 ; ... ; datatypen ; expr
```

+ Predefined types, terms and operation: `nat` for integers, `1,2,...` and plus operation `+`
+ Kind expression: `*`, `* -> *`
+ Lambda expression: `\x : nat . x + 1`
+ Function type: `nat -> nat`
+ Dependent product type: `(x : nat) -> (y : nat) -> f x -> f y`
+ Recursive type: `mu x : * . nat -> x`
+ Cast up: `fold 1 [(\x : * . x) nat] 3`
+ Cast down: `unfold 1 e`
+ Datatype: `data List (a : *) = Nil | Cons (x : a) (xs : List a);`
+ Record: `rcrd Person = P {age : nat, address : nat};`
+ Case expression: `case e of Nil => 0 | Cons (x : nat) (xs : List a) => x`
+ Let binding: `let x : nat = 1 in x + 1`
+ Letrec binding: `letrec f : nat -> nat = f 3 in f 4`

## REPL

```bash
make repl
```

Commands begin with colon (`:`). Following commands are available:

+ `<expr>`                   pretty print expression
+ `:t <expr>`                print type of expression
+ `:trans <expr>`            print translation of expression
+ `:e <expr>`                evaluate expression
+ `:q`                       quit gracefully

## Examples

See `examples` directory for large examples.
