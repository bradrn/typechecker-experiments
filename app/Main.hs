{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import System.Console.Haskeline

import Control.Monad.Reader (local)

import qualified Data.Map.Strict as Map

import Expr (Type(..))
import Core (InferError(..))
import qualified Core
import Interpreter
import Lexer (alexScanTokens)
import Parser
import Typecheck

processExpr :: String -> (Core.Type, Either InferError (Value Interpret))
processExpr x =
        let (t, c) = testInfer defaultEnvType $ parseExpr $ alexScanTokens x
        in (t, interpret defaultEnvVal c)
  where
    defaultEnvVal = Map.fromList
        [ ("Add", VClosure Map.empty $ \[VInt i, VInt j] -> pure $ VInt $ i + j)
        , ("Map", VClosure Map.empty $ \[VClosure env f, VList xs] ->
            local (addNames env) $ fmap VList $ traverse (f . pure) xs)
        ]
    defaultEnvType = Map.fromList
        [ ("Add", TFun [TCon "Int" [], TCon "Int" []] (TCon "Int" []))
        , ("Map", TFun [TFun [TQVar "a"] (TQVar "a"), TCon "List" [TQVar "a"]] (TCon "List" [TQVar "a"]))
        ]

main :: IO ()
main = runInputT defaultSettings loop

loop :: InputT IO ()
loop = getInputLine "> " >>= \case
    Nothing -> pure ()
    Just x -> do
        let (t, o) = processExpr x
        outputStrLn $ show t
        outputStrLn $ either show renderValue o
        loop
