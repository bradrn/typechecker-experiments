{-# LANGUAGE DeriveFunctor #-}

module Core where

import Data.Primitive.MutVar
import Data.Text (Text)
import Data.Void

import qualified Expr

data Expr
    = Lit Int
    | Var Text
    | App Expr [Expr]
    | Lam [Text] Expr
    | Let Text Expr Expr
    | List [Expr]
    | Deferred InferError
    deriving (Eq, Show)

data Type v
    = TCon Text [Type v]
    | TVar v
    | TRigid Text
    | TQVar Text
    | TFun [Type v] (Type v)
    | TError InferError
    deriving (Eq, Show, Functor)

data InferError
    = OccursError
    | CannotUnify (Type Void) (Type Void)
    | UnknownName Text
    deriving (Eq, Show)

data TV s = Unbound Text | Link (Type (Var s))
type Var s = MutVar s (TV s)

exprToCore :: Expr.Type -> Type Void
exprToCore (Expr.TCon t ts) = TCon t $ exprToCore <$> ts
exprToCore (Expr.TQVar v) = TQVar v
exprToCore (Expr.TFun ats rt) = TFun (exprToCore <$> ats) (exprToCore rt)
