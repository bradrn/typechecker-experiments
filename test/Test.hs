{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad (unless)
import Data.String (fromString)
import Data.Void

import qualified Data.Map.Strict as Map

import qualified Expr
import Core
import Interpreter
import Lexer (alexScanTokens)
import Parser
import Typecheck

typecheck :: String -> (Type, Expr)
typecheck = testInfer Map.empty . parseExpr . alexScanTokens

testTypecheck :: String -> String -> (Type, Expr) -> TestTree
testTypecheck n x t = testCase n $ typecheck x @?= t

testInterpret :: String -> String -> Either InferError (Value Interpret) -> TestTree
testInterpret n x v =
    testCase n $ assertConcreteEq v $
        interpret defaultEnvVal $ snd $
        testInfer defaultEnvType $ parseExpr $ alexScanTokens x
  where
    defaultEnvVal = Map.fromList
        [ ("Add", VClosure Map.empty $ \[VInt i, VInt j] -> pure $ VInt $ i + j)
        ]
    defaultEnvType = Map.fromList
        [ ("Add", Expr.TFun [Expr.TCon "Int" [], Expr.TCon "Int" []] (Expr.TCon "Int" []))
        ]

    -- adapted from tasty-hunit source
    assertConcreteEq :: Either InferError (Value m) -> Either InferError (Value m) -> Assertion
    assertConcreteEq expected actual =
        unless (concreteEq' actual expected) (assertFailure msg)
      where
        msg = "expected: " ++ either show renderValue expected
            ++ "\n but got: " ++ either show renderValue actual

        concreteEq' (Left e1) (Left e2) = e1 == e2
        concreteEq' (Right v1) (Right v2) = concreteEq v1 v2
        concreteEq' _ _ = False

-- helpers
qt = TQVar . WrapVar . fromString . ('t':) . show
qt_ = TVar . WrapVar . fromString . ("t"++) . show
int = TCon "Int" []
list = TCon "Dim" . (TNat 1:) . pure
(-->) i o = TFun [i] o
(-:>) is o = TFun is o

main :: IO ()
main = defaultMain $ testGroup "Tests"
    [ testGroup "Success"
        [ testTypecheck "id" "x -> x"                          (qt 0 --> qt 0, Lam ["x"] (Var "x"))
        , testTypecheck "let" "x -> Let(y, x, y)"              (qt 0 --> qt 0, Lam ["x"] (Let "y" (Var "x") (Var "y")))
        , testTypecheck "intfun" "x -> Let(y, x, y(1))"
              ((int --> qt 1) --> qt 1, Lam ["x"] $ Let "y" (Var "x") $ App (Var "y") [Lit 1])
        , testTypecheck "unify" "(x, y) -> z -> z(x(1), x(y))"
              ( TFun [int --> qt 4, int] $ ([qt 4, qt 4] -:> qt 5) --> qt 5
              , Lam ["x", "y"] $ Lam ["z"] $ App (Var "z") [App (Var "x") [Lit 1], App (Var "x") [Var "y"]]
              )
        , testTypecheck "asc" "x -> (x : Int)"
              (int --> int, Lam ["x"] (Var "x"))
        , testTypecheck "list1" "[1,2,3]"                      (list int, List $ Lit <$> [1,2,3])
        , testTypecheck "list2" "[1,2,3] : Dim(1, Int)"        (list int, List $ Lit <$> [1,2,3])
        -- below from https://okmij.org/ftp/ML/generalization/unsound.ml
        , testTypecheck "gen1" "(x, y) -> Let(x, x(y), x -> y(x))"
            ( [(qt 3 --> qt 4) --> qt 2, qt 3 --> qt 4] -:> (qt 3 --> qt 4)
            , Lam ["x", "y"] $ Let "x" (App (Var "x") [Var "y"]) $ Lam ["x"] $ App (Var "y") [Var "x"]
            )
        , testTypecheck "gen2" "Let(id, x->x, x -> Let(y, Let(z, x(id), z), y))"
            ( ((qt 2 --> qt 2) --> qt 3) --> qt 3
            , Let "id" (Lam ["x"] $ Var "x") $ Lam ["x"] $ Let "y" (Let "z" (App (Var "x") [Var "id"]) (Var "z")) (Var "y")
            )
        ]
    , testGroup "Fail"
        [ testTypecheck "occur" "x -> x(x)"
            (qt 0 --> qt 2, Lam ["x"] (Deferred OccursError))
        , testTypecheck "name" "x -> y"
            (qt 0 --> qt 1, Lam ["x"] (Deferred (UnknownName "y")))
        , testTypecheck "unify" "Let(id, x->x, (x, z) -> z(x(id), x(1)))"
            ( [(qt 3 --> qt 3) --> qt 4, [qt 4, qt 7] -:> qt 6] -:> qt 6
            , Let "id" (Lam ["x"] (Var "x")) $ Lam ["x","z"] $ App (Var "z")
                [ App (Var "x") [Var "id"]
                , Deferred $ CannotUnify int (qt_ 3 --> qt_ 3)
                ]
            )
        , testTypecheck "bidi" "Let(id, x->x, ((x, z) -> z(x(id), x(1))) : ((Int -> a), (a, a) -> b) -> b)"
            ( [int --> TCon "a" [], [TCon "a" [], TCon "a" []] -:> TCon "b" []] -:> TCon "b" []
            , Let "id" (Lam ["x"] (Var "x")) $ Lam ["x","z"] $ App (Var "z")
                [ Deferred $ CannotUnify (qt_ 3 --> qt_ 3) int
                , App (Var "x") [Lit 1]
                ]
            )
        , testTypecheck "lamnotfun" "(x -> x) : Int"
            (int, Deferred $ CannotUnify int (qt_ 0 --> qt_ 0))
        , testTypecheck "list" "[1,2,x->x]"
            (list int, List [Lit 1, Lit 2, Deferred $ CannotUnify (qt_ 1 --> qt_ 1) int])
        ]
    , testGroup "Interpreted"
        [ testInterpret "id" "(x -> x)(1)" $ Right $ VInt 1
        , testInterpret "let" "(x -> Let(y, x, y))(2)" $ Right $ VInt 2
        , testInterpret "env" "Add(1,2)" $ Right $ VInt 3
        , testInterpret "intfun" "(x -> Let(y, x, y(1)))(z -> Add(z,2))" $ Right $ VInt 3
        , testInterpret "unify" "((x, y) -> z -> z(x(1), x(y)))(n -> Add(n,10), 2)(Add)" $ Right $ VInt 23
        , testInterpret "list" "[1,2,3]" $ Right $ VList $ VInt <$> [1,2,3]
        , testInterpret "gen1" "((x, y) -> Let(x, x(y), x -> y(x)))(a->a, a->Add(a,10))(1)" $ Right $ VInt 11
        , testInterpret "gen2" "Let(id, x->x, x -> Let(y, Let(z, x(id), z), y))(f -> f(1))" $ Right $ VInt 1
        , testInterpret "err" "Foobar(1)" $ Left $ UnknownName "Foobar"
        ]
    ]
