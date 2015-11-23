{
module Tokens where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-

  $white+                       ;
  "--".*                        ;
  let                           { \s -> TokenLet }
  in                            { \s -> TokenIn }
  castup                        { \s -> TokenF }
  castdown                      { \s -> TokenU }
  \/\\                          { \s -> TokenPi }
  mu                            { \s -> TokenMu }
  nat                           { \s -> TokenNat }
  $digit+                       { \s -> TokenInt (read s) }
  \=                            { \s -> TokenEq }
  \:                            { \s -> TokenColon }
  \.                            { \s -> TokenDot }
  \\                            { \s -> TokenLam }
  \-\>                          { \s -> TokenArr }
  \+                            { \s -> TokenPlus }
  \-                            { \s -> TokenMinus }
  \*                            { \s -> TokenTimes }
  \/                            { \s -> TokenDiv }
  \(                            { \s -> TokenLParen }
  \)                            { \s -> TokenRParen }
  \[                            { \s -> TokenLB }
  \]                            { \s -> TokenRB }
  $alpha [$alpha $digit \_ \']* { \s -> TokenSym s }
{
-- The token type:
data Token = TokenLet
           | TokenIn
           | TokenF
           | TokenU
           | TokenPi
           | TokenMu
           | TokenNat
           | TokenInt Int
           | TokenSym String
           | TokenEq
           | TokenLam
           | TokenArr
           | TokenColon
           | TokenDot
           | TokenPlus
           | TokenMinus
           | TokenTimes
           | TokenDiv
           | TokenLParen
           | TokenRParen
           | TokenRB
           | TokenLB
           deriving (Eq,Show)
scanTokens = alexScanTokens
}
