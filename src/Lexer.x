{
module Lexer (Token(..), alexScanTokens) where
}

%wrapper "basic"

$digit = [0-9]
$alpha = [a-zA-Z]

@ident = ($alpha | \_) ($alpha | $digit | \_)*

tokens :-
    $white+ ;
    Let        { const Let }
    Lambda     { const Lambda }
    "->"       { const Arrow }
    "("        { const LPar }
    ")"        { const RPar }
    ":"        { const Colon }
    ","        { const Comma }
    $digit+    { Lit . read }
    "?" @ident { TVar . tail }
    @ident     { Var }
{
data Token
    = Let
    | Comma
    | Lambda | Arrow
    | LPar | RPar
    | Colon | TVar String 
    | Lit Int | Var String
    deriving (Eq, Show)
}
