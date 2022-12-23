{
{-# LANGUAGE OverloadedStrings #-}

module Parser (parseExpr) where

import Data.Text (Text, pack)

import Expr
import qualified Lexer
}

%name parseExpr Expr
%tokentype { Lexer.Token }
%error { parseError }


%token
  Let     { Lexer.Let }
  List    { Lexer.List }
  ','     { Lexer.Comma }
  Lambda  { Lexer.Lambda }
  '->'    { Lexer.Arrow }
  '('     { Lexer.LPar }
  ')'     { Lexer.RPar }
  '['     { Lexer.LBrk }
  ']'     { Lexer.RBrk }
  ':'     { Lexer.Colon }
  tvarstr { Lexer.TVar $$  }
  lit     { Lexer.Lit $$ }
  varstr  { Lexer.Var $$ }

%%

tvar :: { Text } : tvarstr { pack $1 }
var  :: { Text } : varstr { pack $1 }

some_rev(p)
  : p                 { [$1] }
  | some_rev(p) ',' p { $3 : $1 }

some(p)
  : some_rev(p) { reverse $1 }

Expr
  :: { Expr }
  : lit                               { Lit $1 }
  | var                               { Var $1 }
  | Lambda '(' some(var) ',' Expr ')' { Lam $3 $5 }
  | var '->' Expr                     { Lam [$1] $3 }
  | '(' some(var) ')' '->' Expr       { Lam $2 $5 }
  | Let '(' var ',' Expr ',' Expr ')' { Let $3 $5 $7 }
  | List '(' some(Expr) ')'           { List $3 }
  | '[' some(Expr) ']'                { List $2 }
  | Expr ':' Type                     { Asc $1 $3 }
  | Expr '(' some(Expr) ')'           { App $1 $3 }
  | '(' Expr ')'                      { $2 }

Type
  :: { Type }
  : var                          { TCon $1 [] }
  | var '(' some(Type) ')'       { TCon $1 $3 }
  | List '(' some(Type) ')'      { TCon "List" $3 }
  | tvar                         { TQVar $1 }
  | Type '->' Type               { TFun [$1] $3 }
  | '(' some(Type) ')' '->' Type { TFun $2 $5 }
  | '(' Type ')'                 { $2 }
  | lit                          { TNat $1 }

{
parseError :: [Lexer.Token] -> a
parseError = error . ("Parse error: "++) . show
}
