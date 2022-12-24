{-# LANGUAGE OverloadedStrings #-}

module Expr where

import Data.Text (Text, intercalate)

data Expr
    = Lit Int
    | Var Text
    | App Expr [Expr]
    | Lam [Text] Expr
    | Let Text Expr Expr
    | Asc Expr Type
    | List [Expr]
    deriving (Eq, Show)

data Type
    = TCon Text [Type]
    | TQVar Text
    | TFun [Type] Type
    deriving (Eq, Show)

pprintType :: Type -> Text
pprintType (TCon t []) = t
pprintType (TCon t ats) =
    t <> "(" <> intercalate "," (pprintType <$> ats) <> ")"
pprintType (TQVar t) = "?" <> t
pprintType (TFun [at@(TQVar _)] rt) = pprintType at <> " -> " <> pprintType rt
pprintType (TFun ats rt) =
    "(" <> intercalate "," (pprintType <$> ats) <> ") -> " <> pprintType rt
