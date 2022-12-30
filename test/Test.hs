{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad (unless)
import Control.Monad.Reader (local)
import Data.String (fromString)
import Data.Void

import qualified Data.Map.Strict as Map

import qualified Expr
import Expr (Op(..))
import Core
import Interpreter
import Lexer (alexScanTokens)
import Parser
import Typecheck
import UnionFind (Uniq(..))

typecheck :: String -> (Type, Expr)
typecheck = testInfer defaultEnvType . parseExpr . alexScanTokens

testTypecheck :: String -> String -> (Type, Expr) -> TestTree
testTypecheck n x t = testCase n $ typecheck x @?= t

testInterpret :: String -> String -> Either InferError (Value Interpret) -> TestTree
testInterpret n x v =
    testCase n $ assertConcreteEq v $
        interpret defaultEnvVal $ snd $
        testInfer defaultEnvType $ parseExpr $ alexScanTokens x
  where
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

defaultEnvVal = Map.fromList
    [ ("Add", VClosure Map.empty $ \[VInt i, VInt j] -> pure $ VInt $ i + j)
    , ("Map", VClosure Map.empty $ \[VClosure env f, VList xs] ->
        local (addNames env) $ fmap VList $ traverse (f . pure) xs)
    ]
defaultEnvType = Map.fromList
    [ ("Add", Expr.TFun [Expr.TCon "Int" [], Expr.TCon "Int" []] (Expr.TCon "Int" []))
    , ("Map", Expr.TFun [Expr.TFun [Expr.TQVar "a"] (Expr.TQVar "a"), Expr.TCon "List" [Expr.TQVar "a"]] (Expr.TCon "List" [Expr.TQVar "a"]))
    ]

-- helpers
qt = TQVar . WrapVar . fromString . ('t':) . show
qt_ = TMeta . Uniq
int = TCon "Int" []
list = TCon "List" . pure
(-->) i o = TFun [i] o
(-:>) is o = TFun is o

main :: IO ()
main = defaultMain $ testGroup "Tests"
    [ testGroup "Success"
        [ testTypecheck "id" "x -> x"                          (qt 0 --> qt 0, Lam ["x"] (Var "x"))
        , testTypecheck "let" "x -> Let(y, x, y)"              (qt 0 --> qt 0, Lam ["x"] (Let "y" (Var "x") (Var "y")))
        , testTypecheck "prec" "1+2*3-4"
              (int, App (Op Times) [App (Op Plus) [Lit 1, App (Op Times) [Lit 2, Lit 3]], Lit 4])
        , testTypecheck "intfun" "x -> Let(y, x, y(1))"
              ((int --> qt 2) --> qt 2, Lam ["x"] $ Let "y" (Var "x") $ App (Var "y") [Lit 1])
        , testTypecheck "unify" "(x, y) -> z -> z(x(1), x(y))"
              ( TFun [int --> qt 4, int] $ ([qt 4, qt 4] -:> qt 5) --> qt 5
              , Lam ["x", "y"] $ Lam ["z"] $ App (Var "z") [App (Var "x") [Lit 1], App (Var "x") [Var "y"]]
              )
        , testTypecheck "asc" "x -> (x : Int)"
              (int --> int, Lam ["x"] (Var "x"))
        , testTypecheck "list1" "[1,2,3]"                      (list int, List $ Lit <$> [1,2,3])
        , testTypecheck "list2" "[1,2,3] : List(Int)"          (list int, List $ Lit <$> [1,2,3])
        , testTypecheck "hof1"  "Map(x->x, [1,2,3])"
            (list int, App (Var "Map") [Lam ["x"] (Var "x"), List $ Lit <$> [1,2,3]])
        , testTypecheck "hof2"  "Map(x->Add(x,1), [1,2,3])"
            (list int, App (Var "Map") [Lam ["x"] (App (Var "Add") [Var "x", Lit 1]), List $ Lit <$> [1,2,3]])
        , testTypecheck "hof3"  "f -> Map(f, [1,2,3])"
            ((int --> int) --> list int, Lam ["f"] $ App (Var "Map") [Var "f", List $ Lit <$> [1,2,3]])
        -- below from https://okmij.org/ftp/ML/generalization/unsound.ml
        , testTypecheck "gen1" "(x, y) -> Let(x, x(y), x -> y(x))"
            ( [(qt 4 --> qt 6) --> qt 3, qt 4 --> qt 6] -:> (qt 4 --> qt 6)
            , Lam ["x", "y"] $ Let "x" (App (Var "x") [Var "y"]) $ Lam ["x"] $ App (Var "y") [Var "x"]
            )
        , testTypecheck "gen2" "Let(id, x->x, x -> Let(y, Let(z, x(id), z), y))"
            ( ((qt 4 --> qt 4) --> qt 3) --> qt 3
            , Let "id" (Lam ["x"] $ Var "x") $ Lam ["x"] $ Let "y" (Let "z" (App (Var "x") [Var "id"]) (Var "z")) (Var "y")
            )
        ]
    , testGroup "Fail"
        [ testTypecheck "occur" "x -> x(x)"
            ((qt 1 --> qt 2) --> qt 2, Lam ["x"] (App (Var "x") [Deferred OccursError]))
        , testTypecheck "name" "x -> y"
            (qt 0 --> qt 1, Lam ["x"] (Deferred (UnknownName "y")))
        , testTypecheck "unify" "Let(id, x->x, (x, z) -> z(x(id), x(1)))"
            ( [(qt 7 --> qt 7) --> qt 4, [qt 4, qt 4] -:> qt 5] -:> qt 5
            , Let "id" (Lam ["x"] (Var "x")) $ Lam ["x","z"] $ App (Var "z")
                [ App (Var "x") [Var "id"]
                , App (Var "x") [Deferred $ CannotUnify int (qt_ 7 --> qt_ 7)]
                ]
            )
        , testTypecheck "bidi" "Let(id, x->x, ((x, z) -> z(x(id), x(1))) : ((Int -> a), (a, a) -> b) -> b)"
            ( [int --> TCon "a" [], [TCon "a" [], TCon "a" []] -:> TCon "b" []] -:> TCon "b" []
            , Let "id" (Lam ["x"] (Var "x")) $ Lam ["x","z"] $ App (Var "z")
                [ App (Var "x") [Deferred $ CannotUnify int (qt_ 3 --> qt_ 3)]
                , App (Var "x") [Lit 1]
                ]
            )
        , testTypecheck "lamnotfun" "(x -> x) : Int"
            (int, Deferred $ CannotUnify int (qt_ 0 --> qt_ 1))
        , testTypecheck "list" "[1,2,x->x]"
            (list int, List [Lit 1, Lit 2, Deferred $ CannotUnify int (qt_ 0 --> qt_ 1)])
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
