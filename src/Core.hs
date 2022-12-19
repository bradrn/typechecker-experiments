module Core where

import Data.Text (Text)

import Expr (InferError)

data Expr
    = Lit Int
    | Var Text
    | App Expr [Expr]
    | Lam [Text] Expr
    | Let Text Expr Expr
    | List [Expr]
    | Deferred InferError
    deriving (Eq, Show)
