{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}

module Interpreter where

import Control.Monad.Error.Class (MonadError(throwError))
import Control.Monad.Reader
import Data.Functor ((<&>))
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Text (Text)

import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as Map

import Core
import Expr (InferError)

type Env m = Map Text (Value m)

addNames :: Env m -> Env m -> Env m
addNames = Map.merge
    Map.preserveMissing                   -- combine new names (1st arg of addNames)
    Map.preserveMissing                   -- with current environment (2nd arg of addNames)
    (Map.zipWithMatched $ \_k n _c -> n)  -- preferring the former

data Value m
    = VInt Int
    | VList [Value m]
    | VClosure (Env m) ([Value m] -> m (Value m))

renderValue :: Value m -> String
renderValue (VInt i) = show i
renderValue (VList vs) = '[' : intercalate "," (renderValue <$> vs) ++ "]"
renderValue (VClosure _ _) = "(fn)"

-- | Test if two 'Value's are equal, treating all closures as unequal.
concreteEq :: Value m -> Value m -> Bool
concreteEq (VInt i) (VInt j) = i == j
concreteEq (VList vs) (VList ws) = and $ zipWith concreteEq vs ws
concreteEq _ _ = False

newtype Interpret a = Interpret { runInterpret :: Env Interpret -> Either InferError a }
    deriving (Functor, Applicative, Monad, MonadReader (Env Interpret), MonadError InferError)
        via ReaderT (Env Interpret) (Either InferError)

interpret :: Env Interpret -> Expr -> Either InferError (Value Interpret)
interpret = \env e -> runInterpret (interpret' e) env
  where
    interpret' :: Expr -> Interpret (Value Interpret)
    interpret' (Lit i) = pure $ VInt i
    interpret' (Var t) =
        asks (Map.lookup t) <&> \case
            Nothing -> error "interpret': unknown name - error in typechecker!"
            Just v -> v
    interpret' (App f as) =
        interpret' f >>= \case
            VClosure cl f' -> do
                as' <- traverse interpret' as
                local (addNames cl) $ f' as'
            _ -> error "interpret': tried to apply non-function - error in typechecker!"
    interpret' (Lam names x) =
        ask <&> \env -> VClosure env $ \as ->
            let argsEnv = Map.fromList $ zip names as
            in local (addNames argsEnv) $ interpret' x
    interpret' (Let v x y) = do
        x' <- interpret' x
        local (Map.insert v x') $ interpret' y
    interpret' (List xs) = VList <$> traverse interpret' xs
    interpret' (Deferred err) = throwError err
