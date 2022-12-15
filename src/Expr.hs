{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}

module Expr where

import Data.Primitive.MutVar
import Data.Text (Text, intercalate)
import Data.Void

data Expr
    = Lit Int
    | Var Text
    | App Expr [Expr]
    | Lam [Text] Expr
    | Let Text Expr Expr
    | Asc Expr (Type Void)
    | List [Expr]
    deriving (Eq, Show)

data Type v
    = TCon Text [Type v]
    | TVar v
    | TRigid Text
    | TQVar Text
    | TFun [Type v] (Type v)
    deriving (Eq, Show, Functor)

data TV s = Unbound Text | Link (Type (Var s))
type Var s = MutVar s (TV s)

pprintType :: Type Void -> Text
pprintType (TCon t []) = t
pprintType (TCon t ats) =
    t <> "(" <> intercalate "," (pprintType <$> ats) <> ")"
pprintType (TRigid _) = error "unexpected internal rigid type"
pprintType (TVar t) = absurd t
pprintType (TQVar t) = "?" <> t
pprintType (TFun [at@(TQVar _)] rt) = pprintType at <> " -> " <> pprintType rt
pprintType (TFun ats rt) =
    "(" <> intercalate "," (pprintType <$> ats) <> ") -> " <> pprintType rt
