{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module Typecheck where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Primitive
import Control.Monad.Reader
import Control.Monad.ST
import Data.Bifunctor
import Data.Foldable (traverse_, for_)
import Data.Map.Strict (Map)
import Data.Primitive.MutVar
import Data.Text (Text)
import Data.Traversable (for)
import Data.Void

import qualified Data.Map.Strict as M
import qualified Data.Text as T

import Expr

data InferError
    = OccursError
    | CannotUnify (Type Void) (Type Void)
    | UnknownName Text
    | LamNotFun
    | ListNotList
    deriving (Eq, Show)

type Env v = Map Text (Type v)

newtype Infer s a = Infer { getInfer :: ReaderT (MutVar s Int, Env (Var s)) (ExceptT InferError (ST s)) a }
    deriving (Functor, Applicative, Monad, MonadError InferError, MonadReader (MutVar s Int, Env (Var s)))

instance PrimMonad (Infer s) where
    type PrimState (Infer s) = s
    primitive = Infer . lift . primitive
    {-# INLINE primitive #-}

traceVars :: Type (Var s) -> Infer s (Type Void)
traceVars (TVar v) = readMutVar v >>= \case
    Unbound t -> pure (TQVar $ "__" <> t)
    Link t -> traceVars t
traceVars (TCon t ats) = TCon t <$> traverse traceVars ats
traceVars (TRigid t) = pure $ TRigid t
traceVars (TQVar t) = pure $ TQVar t
traceVars (TFun ats rt) = TFun <$> traverse traceVars ats <*> traceVars rt

rigidify :: Type (Var s) -> Infer s (Type (Var s))
rigidify (TQVar v) = pure $ TRigid v
rigidify t@(TVar v) = readMutVar v >>= \case
    Unbound _ -> pure t
    Link t' -> rigidify t'
rigidify (TFun ats rt) = TFun <$> traverse rigidify ats <*> rigidify rt
rigidify t = pure t

lookupVar :: Text -> Infer s (Maybe (Type (Var s)))
lookupVar t = asks $ M.lookup t . snd

withEnv :: (Env (Var s) -> Env (Var s)) -> Infer s a -> Infer s a
withEnv = local . second

fresh :: Infer s Int
fresh = do
    v <- asks fst
    !i <- readMutVar v
    writeMutVar v (i+1)
    pure i

gensym :: Infer s Text
gensym = ("t"<>) . T.pack . show <$> fresh

newvar :: Infer s (Type (Var s))
newvar = do
    v <- gensym
    TVar <$> newMutVar (Unbound v)

concatTraverse :: Applicative m => (a -> m [b]) -> [a] -> m [b]
concatTraverse f xs = concat <$> traverse f xs

free :: Type (Var s) -> Infer s [Var s]
free (TVar v) = readMutVar v >>= \case
    Unbound _ -> pure [v]
    Link t -> free t
free (TFun ats rt) = (++) <$> concatTraverse free ats <*> free rt
free _ = pure []

allFree :: Infer s [Var s]
allFree = concatTraverse free =<< asks (M.elems . snd)

occurs :: Var s -> Type (Var s) -> Infer s ()
occurs v = \case
    TVar w
      | v == w -> throwError OccursError
      | otherwise -> readMutVar w >>= \case
        Link t -> occurs v t
        _ -> pure ()
    TFun ats rt -> traverse_ (occurs v) ats >> occurs v rt
    _ -> pure ()
 
instantiate :: Type (Var s) -> Infer s (Type (Var s))
instantiate = fmap fst . go M.empty
  where
    go :: Map Text (Type (Var s))
        -> Type (Var s)
        -> Infer s (Type (Var s), Map Text (Type (Var s)))
    go subst (TCon t ats) = do
        (ats', subst') <- goMany subst ats
        pure (TCon t ats', subst')
    go subst (TVar v) = readMutVar v >>= \case
        Unbound _ -> pure (TVar v, subst)
        Link t -> go subst t
    go subst (TRigid v) = pure (TRigid v, subst)
    go subst (TQVar v) =
        case M.lookup v subst of
            Just v' -> pure (v', subst)
            Nothing -> do
                v' <- newvar
                pure (v', M.insert v v' subst)
    go subst (TFun ats rt) = do
        (ats', subst') <- goMany subst ats
        (rt', subst'') <- go subst' rt
        pure (TFun ats' rt', subst'')

    goMany subst [] = pure ([], subst)
    goMany subst (t:ts) = do
        (t', subst') <- go subst t
        (ts', subst'') <- goMany subst' ts
        pure (t':ts', subst'')

generalise :: Type (Var s) -> Infer s (Type (Var s))
generalise = \t -> allFree >>= \fs -> go fs t
  where
    go :: [Var s] -> Type (Var s) -> Infer s (Type (Var s))
    go fs (TCon t ats) = TCon t <$> traverse (go fs) ats
    go fs (TVar v) = readMutVar v >>= \case
        Unbound v'
            | v `elem` fs -> pure $ TVar v
            | otherwise -> pure $ TQVar v'
        Link t -> go fs t
    go _fs (TRigid v) = pure $ TQVar v
    go _fs (TQVar v) = pure $ TQVar v
    go fs (TFun ats rt) = TFun <$> traverse (go fs) ats <*> go fs rt

generaliseAll :: Type (Var s) -> Infer s (Type Void)
generaliseAll = \t -> allFree >>= \fs -> go fs t
  where
    go :: [Var s] -> Type (Var s) -> Infer s (Type Void)
    go fs (TCon t ats) = TCon t <$> traverse (go fs) ats
    go fs (TVar v) = readMutVar v >>= \case
        Unbound v'
            | v `elem` fs -> do
                  fs' <- traverse (traceVars . TVar) fs
                  error $ "generaliseAll: extra free! " ++ show (v', fs')
            | otherwise -> pure $ TQVar v'
        Link t -> go fs t
    go _fs (TRigid v) = pure $ TQVar v
    go _fs (TQVar v) = pure $ TQVar v
    go fs (TFun ats rt) = TFun <$> traverse (go fs) ats <*> go fs rt

unify :: Type (Var s) -> Type (Var s) -> Infer s ()
unify t1 t2 | t1 == t2 = pure ()
unify (TVar v1) t2 = readMutVar v1 >>= \case
    Unbound _ -> occurs v1 t2 >> writeMutVar v1 (Link t2)
    Link t1' -> unify t1' t2
unify t1 (TVar v2) = readMutVar v2 >>= \case
    Unbound _ -> occurs v2 t1 >> writeMutVar v2 (Link t1)
    Link t2' -> unify t1 t2'
unify (TFun at1s rt1) (TFun at2s rt2) = do
    zipWithM_ unify at1s at2s
    unify rt1 rt2
unify t1 t2 = do
    t1' <- traceVars t1
    t2' <- traceVars t2
    throwError $ CannotUnify t1' t2'

check :: Expr -> Type Void -> Infer s (Type (Var s))
check = \x t -> do
    t' <- rigidify $ vacuous t
    t' <$ check' x t'
  where
    check' (App f as) t = do
        tf <- infer f
        atas <- for as $ \a -> (a,) <$> newvar
        let tas = snd <$> atas
        unify tf (TFun tas t)
        for_ atas $ \(a, ta) -> do
            ta' <- infer a
            unify ta' ta
    check' (Lam vs x) t = case t of
        TFun ats rt ->
            withEnv (foldr (.) id $ zipWith M.insert vs ats) $ check' x rt
        _ -> throwError LamNotFun
    check' (Let v x y) t = do
        tv <- generalise =<< infer x
        withEnv (M.insert v tv) $ check' y t
    check' (List xs) t = case t of
        TCon "List" [rt] -> traverse_ (flip check' rt) xs
        _ -> throwError ListNotList
    check' x t = do
        tx <- infer x
        unify tx t

infer :: Expr -> Infer s (Type (Var s))
infer (Lit _) = pure $ TCon "Int" []
infer (Var v) = lookupVar v >>= \case
    Nothing -> throwError $ UnknownName v
    Just t -> instantiate t
infer (App f as) = do
    tf <- infer f
    tas <- traverse infer as
    tr <- newvar
    unify tf (TFun tas tr)
    pure tr
infer (Lam vs x) = do
    vtvs <- for vs $ \v -> (v,) <$> newvar
    let tvs = snd <$> vtvs
    tx <- withEnv (foldr (.) id $ uncurry M.insert <$> vtvs) $ infer x
    pure $ TFun tvs tx
infer (Let v x y) = do
    tv' <- infer x
    tv <- generalise tv' -- =<< infer x
    withEnv (M.insert v tv) $ infer y
infer (List xs) = do
    tr <- newvar
    traverse_ (unify tr <=< infer) xs
    pure $ TCon "List" [tr]
infer (Asc x t) = check x t

runInfer :: (forall s. Infer s a) -> Env Void -> Either InferError a
runInfer i e = runST $ do
    v <- newMutVar 0
    runExceptT $ flip runReaderT (v, M.map vacuous e) $ getInfer i

testInfer :: Expr -> Either InferError (Type Void)
testInfer x = runInfer (infer x >>= generaliseAll) M.empty
