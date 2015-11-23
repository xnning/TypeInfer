{
module Parser (parseExpr) where
import Data.Char (isDigit, isSpace, isAlpha)
import Data.List (stripPrefix)
import Syntax
import Tokens
}


%name parser
%tokentype { Token }
%error { parseError }


%token
    fold   { TokenF }
    unfold { TokenU }
    pi     { TokenPi }
    let    { TokenLet }
    in     { TokenIn }
    mu     { TokenMu }
    nat    { TokenNat }
    id     { TokenSym $$ }
    digits { TokenInt $$ }
    ':'    { TokenColon }
    '='    { TokenEq }
    '.'    { TokenDot }
    '['    { TokenLB }
    ']'    { TokenRB }
    '->'   { TokenArr }
    '('    { TokenLParen }
    ')'    { TokenRParen }
    '*'    { TokenTimes }
    '\\'   { TokenLam }
    '+'    { TokenPlus }


%right in
%right '.'
%right '->'
%right ']'
%right '|'
%left '+'
%left UNFOLD


%monad { Either String }

%%

expr : '\\' id '.' expr                         { elam $2 $4 }
     | pi teles '.' expr                        { epi $2 $4  }

     -- surface language
     | expr '+' expr                            { PrimOp Add $1 $3 }
     | expr '->' expr                           { earr $1 $3 }
     | let id '=' expr in expr                  { elet $2 $4 $6 }
     | aexp                                     { $1 }

aexp : aexp term                                { App $1 $2 }
     | term                                     { $1 }

term : nat                                      { Nat }
     | id                                       { evar $1 }
     | digits                                   { Lit $1 }
     | '*'                                      { Kind Star }
     | '(' expr ')'                             { $2 }

teles :             { [] }
      | tele teles  {$1:$2}

tele : '(' id ':' expr ')'         { ($2, $4) }


{

parseError _ = Left "Parse error!"

parseExpr = parser . scanTokens

}
