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
    pi     { TokenPi }
    forall { TokenForall }
    let    { TokenLet }
    in     { TokenIn }
    mu     { TokenMu }
    nat    { TokenNat }
    castup { TokenF}
    castdown { TokenU }
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

expr : forall tau_teles '.' rho                 { eforall $2 $4 }
     | rho                                      { $1 }

     -- sugar: * by default
     | forall id '.' expr                       { eforallStar $2 $4 }

sigma : expr                                    { $1 }

rho  : tau                                      { $1 }
     | pi sigma_teles '.' sigma                 { epi $2 $4 }
     | rho_app                                  { $1 }
     | castup expr                              { CastUp $2 }
     | castdown expr                            { CastDown $2 }
     | let id '=' expr in expr                  { elet $2 $4 $6 }
     | expr ':' sigma                           { Ann $1 $3 }

     -- sugar
     | sigma '->' sigma                         { epiNoDenp $1 $3 }
     | sigma_tele '->' sigma                    { epi [$1] $3 }

     -- surface language
     | rho '+' rho                              { PrimOp Add $1 $3 }

tau  : id                                       { evar $1 }
     | '*'                                      { Kind Star }
     | tau_app                                  { $1 }
     | '\\' id '.' expr                         { elam $2 $4 }
     | '\\' id ':' sigma '.' expr               { elamann $2 $4 $6 }
     | castup tau                               { CastUp $2 }
     | castdown tau                             { CastDown $2 }
     | pi tau_teles '.' tau                     { epi $2 $4 }
     | let id '=' tau in tau                    { elet $2 $4 $6 }
     | tau ':' tau                              { Ann $1 $3 }

     -- sugar
     | tau '->' tau                             { epiNoDenp $1 $3 }
     | tau_tele '->' tau                        { epi [$1] $3 }

     -- surface language
     | nat                                      { Nat }
     | digits                                   { Lit $1 }
     | tau '+' tau                              { PrimOp Add $1 $3 }

tau_app : tau_app tau_term                      { App $1 $2 }
        | tau_term                              { $1 }

tau_term : '(' tau ')'                           { $2 }

rho_app : rho_app exp_term                      { App $1 $2 }
        | exp_term                              { $1 }

exp_term : '(' expr ')'                         { $2 }

sigma_teles :                                   { [] }
            | sigma_tele sigma_teles            { $1:$2 }

sigma_tele : '(' id ':' sigma ')'               { ($2, $4) }

tau_teles :                                     { [] }
          | tau_tele tau_teles                  { $1:$2 }

tau_tele : '(' id ':' tau ')'                   { ($2, $4) }

{

parseError _ = Left "Parse error!"

parseExpr = parser . scanTokens

}
