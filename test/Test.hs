{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.String (fromString)
import Data.Void

import Expr
import Lexer
import Parser
import Typecheck

typecheck :: String -> Either InferError (Type Void)
typecheck = testInfer . parseExpr . alexScanTokens

testTypecheck :: String -> String -> Either InferError (Type Void) -> TestTree
testTypecheck n x t = testCase n $ typecheck x @?= t

-- helpers
qt = TQVar . fromString . ('t':) . show
qt_ = TQVar . fromString . ("__t"++) . show
int = TCon "Int" []
(-->) i o = TFun [i] o
(-:>) is o = TFun is o

main :: IO ()
main = defaultMain $ testGroup "Tests"
    [ testGroup "Success"
        [ testTypecheck "id" "x -> x"                          $ Right $ qt 0 --> qt 0
        , testTypecheck "let" "x -> Let(y, x, y)"              $ Right $ qt 0 --> qt 0
        , testTypecheck "intfun" "x -> Let(y, x, y(1))"        $ Right $ (int --> qt 1) --> qt 1
        , testTypecheck "unify" "(x, y) -> z -> z(x(1), x(y))" $ Right $ TFun [int --> qt 4, int] $ ([qt 4, qt 4] -:> qt 5) --> qt 5
        , testTypecheck "asc" "x -> (x : Int)"                 $ Right $ int --> int
        -- below from https://okmij.org/ftp/ML/generalization/unsound.ml
        , testTypecheck "gen1" "(x, y) -> Let(x, x(y), x -> y(x))" $ Right $
            [(qt 3 --> qt 4) --> qt 2, qt 3 --> qt 4] -:> (qt 3 --> qt 4)
        , testTypecheck "gen2" "Let(id, x->x, x -> Let(y, Let(z, x(id), z), y))" $ Right $
            ((qt 2 --> qt 2) --> qt 3) --> qt 3
        ]
    , testGroup "Fail"
        [ testTypecheck "occur" "x -> x(x)" $ Left OccursError
        , testTypecheck "name" "x -> y" $ Left $ UnknownName "y"
        , testTypecheck "unify" "Let(id, x->x, (x, z) -> z(x(id), x(1)))" $ Left $
            CannotUnify (qt_ 3 --> qt_ 3) int
        , testTypecheck "bidi" "Let(id, x->x, ((x, z) -> z(x(id), x(1))) : ((Int -> a), (a, a) -> b) -> b)" $ Left $
            CannotUnify int (qt_ 3 --> qt_ 3)
        , testTypecheck "lamnotfun" "(x -> x) : int" $ Left LamNotFun
        ]
    ]
