{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import System.Console.Haskeline

import qualified Data.Map.Strict as Map

import Expr (Type(..))
import Core (InferError(..))
import Interpreter
import Lexer (alexScanTokens)
import Parser
import Typecheck

processExpr :: String -> Either InferError (Value Interpret)
processExpr x =
        interpret defaultEnvVal $ snd $
        testInfer defaultEnvType $ parseExpr $ alexScanTokens x
  where
    defaultEnvVal = Map.fromList
        [ ("Add", VClosure Map.empty $ \[VInt i, VInt j] -> pure $ VInt $ i + j)
        ]
    defaultEnvType = Map.fromList
        [ ("Add", TFun [TCon "Int" [], TCon "Int" []] (TCon "Int" []))
        ]

main :: IO ()
main = runInputT defaultSettings loop

loop :: InputT IO ()
loop = getInputLine "> " >>= \case
    Nothing -> pure ()
    Just x -> do
        let o = processExpr x
        outputStrLn $ either show renderValue o
        loop
