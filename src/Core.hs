module Core where

import Data.Text (Text)

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

data Type
    = TCon Text [Type]
    | TMeta Int
    | TRigid Var
    | TQVar Var
    | TFun [Type] Type
    | TError InferError
    deriving (Eq, Show)

data InferError
    = OccursError
    | CannotUnify Type Type
    | UnknownName Text
    deriving (Eq, Show)

data TV = Unbound | Link Type
    deriving (Eq, Show)

newtype Var = WrapVar { readVar :: Text }
    deriving (Eq, Show, Ord)

exprToCore :: Expr.Type -> Type
exprToCore (Expr.TCon t ts) = TCon t $ exprToCore <$> ts
exprToCore (Expr.TQVar v) = TQVar $ WrapVar v
exprToCore (Expr.TFun ats rt) = TFun (exprToCore <$> ats) (exprToCore rt)
