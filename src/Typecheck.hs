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
import Data.Map.Strict (Map)
import Data.Monoid (First(..))
import Data.Primitive.MutVar
import Data.Text (Text)
import Data.Traversable (for)
import Data.Void

import qualified Data.Map.Strict as M
import qualified Data.Text as T

import Expr hiding (Type(..))
import qualified Expr
import Core (Var, Type(..), TV(..), InferError(..))
import qualified Core

type Env t = Map Text t

data InferContext s = InferContext
    { inferCounter :: MutVar s Int
    , inferGlobalExpr :: Env Expr.Type
    , inferLocalExpr :: Env (Type (Var s))
    }

modifyLocalExpr :: (Env (Type (Var s)) -> Env (Type (Var s))) -> InferContext s -> InferContext s
modifyLocalExpr f = \i -> i { inferLocalExpr = f $ inferLocalExpr i }

newtype Infer s a = Infer { getInfer :: ReaderT (InferContext s) (ST s) a }
    deriving (Functor, Applicative, Monad, MonadReader (InferContext s))

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
traceVars (TError err) = pure $ TError err

rigidify :: Expr.Type -> Infer s (Type (Var s))
rigidify (Expr.TQVar v) = pure $ TRigid v
rigidify (Expr.TFun ats rt) = TFun <$> traverse rigidify ats <*> rigidify rt
rigidify (Expr.TCon t ts) = TCon t <$> traverse rigidify ts

lookupVar :: Text -> Infer s (Maybe (Either Expr.Type (Type (Var s))))
lookupVar t = asks $ \c ->
    case M.lookup t (inferLocalExpr c) of
        Just v -> Just $ Right v
        Nothing ->
            case M.lookup t (inferGlobalExpr c) of
                Just v -> Just $ Left v
                Nothing -> Nothing

withEnv :: (Env (Type (Var s)) -> Env (Type (Var s))) -> Infer s a -> Infer s a
withEnv = local . modifyLocalExpr

fresh :: Infer s Int
fresh = do
    v <- asks inferCounter
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
allFree = concatTraverse free =<< asks (M.elems . inferLocalExpr)

occurs :: Var s -> Type (Var s) -> Infer s a -> Infer s (Maybe InferError)
occurs = \v t m -> occurs' v t >>= \case
    Nothing -> Nothing <$ m
    err -> pure err
  where
    occurs' :: Var s -> Type (Var s) -> Infer s (Maybe InferError)
    occurs' v = \case
        TVar w
          | v == w -> pure $ Just OccursError
          | otherwise -> readMutVar w >>= \case
            Link t -> occurs' v t
            _ -> pure Nothing
        TFun ats rt -> do
            os <- traverse (occurs' v) ats
            case foldMap First os of
                First Nothing -> occurs' v rt
                First err -> pure err
        _ -> pure Nothing
 
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
    go subst (TError err) = pure (TError err, subst)

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
    go _fs (TError err) = pure $ TError err

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
    go _fs (TError _err) = TQVar <$> gensym

-- @t1 `unify` t2@ means that t1 can be used anywhere t2 can
unify
    :: Type (Var s)
    -> Type (Var s)
    -> (InferError -> a)
    -> Infer s a
    -> Infer s a
unify = \t1 t2 f cont -> t1 `unify'` t2 >>= \case
    Nothing -> cont
    Just err -> pure $ f err
  where
    unify' :: Type (Var s) -> Type (Var s) -> Infer s (Maybe InferError)
    unify' t1 t2 | t1 == t2 = pure Nothing
    unify' (TVar v1) t2 = readMutVar v1 >>= \case
        Unbound _ -> occurs v1 t2 $ writeMutVar v1 (Link t2)
        Link t1' -> t1' `unify'` t2
    unify' t1 (TVar v2) = readMutVar v2 >>= \case
        Unbound _ -> occurs v2 t1 $ writeMutVar v2 (Link t1)
        Link t2' -> t1 `unify'` t2'
    unify' (TFun at1s rt1) (TFun at2s rt2) = do
        os <- zipWithM unify' at2s at1s  -- note arguments flipped!
        case foldMap First os of
            First Nothing -> rt1 `unify'` rt2
            First err -> pure err
    unify' (TError _) _ = pure Nothing
    unify' t1 t2 = do
        t1' <- traceVars t1
        t2' <- traceVars t2
        pure $ Just $ CannotUnify t1' t2'

deferError :: InferError -> (Type v, Core.Expr)
deferError e = (TError e, Core.Deferred e)

check :: Expr -> Type (Var s) -> Infer s Core.Expr
check (App f as) t = do
    (tf, xf) <- infer f
    atas <- for as $ \a -> (a,) <$> newvar
    let tas = snd <$> atas
    (tf `unify` TFun tas t) Core.Deferred $ do  -- check function returns specified type
        xas <- for atas $ \(a_given, ta) -> do
            (ta_given, xa_given) <- infer a_given
            (ta_given `unify` ta) Core.Deferred $  -- then check function accepts given arguments
                pure xa_given
        pure (Core.App xf xas)
check (Lam vs x) (TFun ats rt) =
    withEnv (foldr (.) id $ zipWith M.insert vs ats) $
        Core.Lam vs <$> check x rt
check (Let v x y) t = do
    (tx', xx) <- infer x
    tx <- generalise tx'
    withEnv (M.insert v tx) $ do
        xy <- check y t
        pure $ Core.Let v xx xy
check (List xs) (TCon "List" [rt]) =
    Core.List <$> traverse (flip check rt) xs
check x t = do
    (tx, xx) <- infer x
    (t `unify` tx) Core.Deferred $
        pure xx
    
infer :: Expr -> Infer s (Type (Var s), Core.Expr)
infer (Lit n) = pure (TCon "Int" [], Core.Lit n)
infer (Var v) = lookupVar v >>= \case
    Nothing -> pure $ deferError $ UnknownName v
    Just t -> (,Core.Var v) <$> instantiate (either (vacuous . Core.exprToCore) id t)
infer (App f as) = do
    (tf, xf) <- infer f
    _as <- traverse infer as
    let (tas, xas) = unzip _as
    tr <- newvar
    (tf `unify` TFun tas tr) deferError $ do
        pure (tr, Core.App xf xas)
infer (Lam vs x) = do
    vtvs <- for vs $ \v -> (v,) <$> newvar
    let tvs = snd <$> vtvs
    (tx, xx) <- withEnv (foldr (.) id $ uncurry M.insert <$> vtvs) $ infer x
    pure (TFun tvs tx, Core.Lam vs xx)
infer (Let v x y) = do
    (tx', xx) <- infer x
    tx <- generalise tx'
    withEnv (M.insert v tx) $ do
        (ty, xy) <- infer y
        pure (ty, Core.Let v xx xy)
infer (List xs) = do
    tr <- newvar
    xxs <- for xs $ \x -> do
        txx@(tx, _xx) <- infer x
        fmap snd $  -- can discard type returned from @unify@
                    -- as only @tr@ is actually used in the end
            (tx `unify` tr) deferError $ pure txx
    pure (TCon "List" [tr], Core.List xxs)
infer (Asc x t) = do
    t' <- rigidify t
    x' <- check x t'
    pure (t', x')

runInfer :: (forall s. Infer s a) -> Env Expr.Type -> a
runInfer i e = runST $ do
    v <- newMutVar 0
    let initContext = InferContext
            { inferCounter = v
            , inferGlobalExpr = e
            , inferLocalExpr = M.empty
            }
    flip runReaderT initContext $ getInfer i

testInfer :: Env Expr.Type -> Expr -> (Type Void, Core.Expr)
testInfer env x = runInfer (infer x >>= firstF generaliseAll) env
  where
    firstF :: Functor f => (a -> f b) -> (a, c) -> f (b, c)
    firstF f (a, c) = (,c) <$> f a
