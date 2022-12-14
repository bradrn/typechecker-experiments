{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module Typecheck where

import Control.Monad
import Control.Monad.Reader
import Data.Map.Strict (Map)
import Data.Monoid (First(..))
import Data.Text (Text)
import Data.Traversable (for)

import qualified Data.Map.Strict as M
import qualified Data.Text as T

import Expr hiding (Type(..))
import qualified Expr
import Core (Var(..), Type(..), InferError(..))
import qualified Core
import UnionFind

type Env t = Map Text t

data InferContext = InferContext
    { inferGlobalEnv :: Env Expr.Type
    , inferLocalEnv :: Env Type
    } deriving (Eq, Show)

modifyLocalEnv :: (Env Type -> Env Type) -> InferContext -> InferContext
modifyLocalEnv f = \i -> i { inferLocalEnv = f $ inferLocalEnv i }

newtype Infer a = Infer { getInfer :: ReaderT InferContext (UnionFind Type) a }
    deriving (Functor, Applicative, Monad, MonadReader InferContext, MonadUnionFind Type)

rigidify :: Expr.Type -> Infer Type
rigidify (Expr.TQVar v) = pure $ TRigid $ WrapVar v
rigidify (Expr.TFun ats rt) = TFun <$> traverse rigidify ats <*> rigidify rt
rigidify (Expr.TCon t ts) = TCon t <$> traverse rigidify ts

lookupVar :: Text -> Infer (Maybe (Either Expr.Type Type))
lookupVar t = asks $ \c ->
    case M.lookup t (inferLocalEnv c) of
        Just v -> Just $ Right v
        Nothing ->
            case M.lookup t (inferGlobalEnv c) of
                Just v -> Just $ Left v
                Nothing -> Nothing

withEnv :: (Env Type -> Env Type) -> Infer a -> Infer a
withEnv = local . modifyLocalEnv

toVar :: Int -> Var
toVar = WrapVar . ("t"<>) . T.pack . show

gensym :: Infer Var
gensym = toVar <$> newCount

concatTraverse :: Applicative m => (a -> m [b]) -> [a] -> m [b]
concatTraverse f xs = concat <$> traverse f xs

zonk :: Type -> Infer Type
zonk (TCon t ts) = TCon t <$> traverse zonk ts
zonk (TMeta v) = readLink v >>= \case
    Unbound -> pure $ TMeta v
    Link t -> do
        t' <- zonk t
        writeLink v t'
        pure t'
zonk (TRigid v) = pure $ TRigid v
zonk (TQVar v) = pure $ TQVar v
zonk (TFun ats rt) = TFun <$> traverse zonk ats <*> zonk rt
zonk (TError e) = pure $ TError e

free :: Type -> Infer [Uniq]
free = zonk >=> go  -- need to zonk to get rid of duplicate vars
  where
    go (TMeta v) = readLink v >>= \case
        Unbound -> pure [v]
        Link t ->  go t
    go (TFun ats rt) = (++) <$> concatTraverse go ats <*> go rt
    go (TCon _ ts) = concatTraverse go ts
    go _ = pure []

allFree :: Infer [Uniq]
allFree = concatTraverse free =<< asks (M.elems . inferLocalEnv)

occurs :: Uniq -> Type -> Infer a -> Infer (Maybe InferError)
occurs = \v t m -> occurs' v t >>= \case
    Nothing -> Nothing <$ m
    err -> pure err
  where
    occurs' :: Uniq -> Type -> Infer (Maybe InferError)
    occurs' v t = do
        vs <- free t
        pure $ if v `elem` vs
           then Just OccursError
           else Nothing
 
instantiate :: Type -> Infer Type
instantiate = fmap fst . go M.empty
  where
    go :: Map Var Type
        -> Type
        -> Infer (Type, Map Var Type)
    go subst (TCon t ats) = do
        (ats', subst') <- goMany subst ats
        pure (TCon t ats', subst')
    go subst (TMeta v) = readLink v >>= \case
        Unbound -> pure (TMeta v, subst)
        Link t -> go subst t
    go subst (TRigid v) = pure (TRigid v, subst)
    go subst (TQVar v) =
        case M.lookup v subst of
            Just v' -> pure (v', subst)
            Nothing -> do
                v' <- TMeta <$> newVar
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

generalise :: Type -> Infer Type
generalise = \t -> allFree >>= \fs -> go fs t
  where
    go :: [Uniq] -> Type -> Infer Type
    go fs (TCon t ats) = TCon t <$> traverse (go fs) ats
    go fs (TMeta v) = readLink v >>= \case
        Unbound
            | v `elem` fs -> pure $ TMeta v
            | otherwise -> pure $ TQVar $ toVar $ label v
        Link t -> go fs t
    go _fs (TRigid v) = pure $ TQVar v
    go _fs (TQVar v) = pure $ TQVar v
    go fs (TFun ats rt) = TFun <$> traverse (go fs) ats <*> go fs rt
    go _fs (TError err) = pure $ TError err

generaliseAll :: Type -> Infer Type
generaliseAll = \t -> allFree >>= \fs -> go fs t
  where
    go :: [Uniq] -> Type -> Infer Type
    go fs (TCon t ats) = TCon t <$> traverse (go fs) ats
    go fs (TMeta v) = readLink v >>= \case
        Unbound
            | v `elem` fs -> do
                  let fs' = TMeta <$> fs
                  error $ "generaliseAll: extra free! " ++ show (v, fs')
            | otherwise -> pure $ TQVar $ toVar $ label v
        Link t -> go fs t
    go _fs (TRigid v) = pure $ TQVar v
    go _fs (TQVar v) = pure $ TQVar v
    go fs (TFun ats rt) = TFun <$> traverse (go fs) ats <*> go fs rt
    go _fs (TError _err) = TQVar <$> gensym

-- @t1 `subtype` t2@ means that t1 can be used anywhere t2 can
subtype
    :: Type
    -> Type
    -> (InferError -> a)
    -> Infer a
    -> Infer a
subtype = \t1 t2 f cont -> t1 `subtype'` t2 >>= \case
    Nothing -> cont
    Just err -> pure $ f err
  where
    subtype' :: Type -> Type -> Infer (Maybe InferError)
    subtype' t1 t2 | t1 == t2 = pure Nothing
    subtype' (TMeta v1) (TMeta v2) = do
        v1' <- readLink v1
        v2' <- readLink v2
        case (v1', v2') of
            (Unbound, Unbound) -> Nothing <$ writeLink v1 (TMeta v2)
            (Link t1, Unbound) -> t1 `subtype'` TMeta v2
            (Unbound, Link t2) -> TMeta v1 `subtype'` t2
            (Link t1, Link t2) -> t1 `subtype'` t2
    subtype' (TMeta v1) t2 = readLink v1 >>= \case
        Unbound -> occurs v1 t2 $ writeLink v1 t2
        Link t1' -> t1' `subtype'` t2
    subtype' t1 (TMeta v2) = readLink v2 >>= \case
        Unbound -> occurs v2 t1 $ writeLink v2 t1
        Link t2' -> t1 `subtype'` t2'
    subtype' (TFun at1s rt1) (TFun at2s rt2) = do
        os <- zipWithM subtype' at2s at1s  -- note arguments flipped!
        case foldMap First os of
            First Nothing -> rt1 `subtype'` rt2
            First err -> pure err
    subtype' (TCon t1 ts1) (TCon t2 ts2) | t1 == t2 =
        getFirst . foldMap First <$> zipWithM subtype' ts1 ts2
    subtype' (TError _) _ = pure Nothing
    subtype' t1 t2 = do
        t1' <- zonk t1
        t2' <- zonk t2
        pure $ Just $ CannotUnify t1' t2'

deferError :: InferError -> (Type, Core.Expr)
deferError e = (TError e, Core.Deferred e)

splitFunction :: Int -> Type -> Infer (Either InferError ([Type], Type))
splitFunction _ (TFun ats rt) = pure $ Right (ats, rt)
splitFunction n t = do
    ats <- replicateM n $ TMeta <$> newVar
    rt <- TMeta <$> newVar
    (t `subtype` TFun ats rt) Left $
        pure $ Right (ats, rt)
    
check :: Expr -> Type -> Infer Core.Expr
check (App f as) t = do
    (tf, xf) <- infer f
    atas <- for as $ \a -> (a,) . TMeta <$> newVar
    let tas = snd <$> atas
    (tf `subtype` TFun tas t) Core.Deferred $ do  -- check function returns specified type
        xas <- for atas $ \(a_given, ta) -> do
            (ta_given, xa_given) <- infer a_given
            (ta_given `subtype` ta) Core.Deferred $  -- then check function accepts given arguments
                pure xa_given
        pure (Core.App xf xas)
check (Lam vs x) t = splitFunction (length vs) t >>= \case
    Left err -> pure $ Core.Deferred err
    Right (ats, rt) -> do
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
    (t `subtype` tx) Core.Deferred $
        pure xx
    
infer :: Expr -> Infer (Type, Core.Expr)
infer (Lit n) = pure (TCon "Int" [], Core.Lit n)
infer (Var v) = lookupVar v >>= \case
    Nothing -> pure $ deferError $ UnknownName v
    Just t -> (,Core.Var v) <$> instantiate (either Core.exprToCore id t)
infer (Op o) = pure (TFun [TCon "Int" [], TCon "Int" []] (TCon "Int" []), Core.Op o)
infer (App f as) = do
    (tf, xf) <- infer f
    splitFunction (length as) tf >>= \case
        Left err -> pure (tf, Core.Deferred err)
        Right (ats, rt) ->
            (rt,) . Core.App xf <$> zipWithM check as ats
infer (Lam vs x) = do
    vtvs <- for vs $ \v -> (v,) . TMeta <$> newVar
    let tvs = snd <$> vtvs
    (tx, xx) <- withEnv (foldr (.) id $ uncurry M.insert <$> vtvs) $ infer x
    pure (TFun tvs tx, Core.Lam vs xx)
infer (Let v x y) = do
    (tx', xx) <- infer x
    tx <- generalise tx'
    withEnv (M.insert v tx) $ do
        (ty, xy) <- infer y
        pure (ty, Core.Let v xx xy)
infer (List []) = (,Core.List []) . TCon "List" . pure . TMeta <$> newVar
infer (List (x0:xs)) = do
    (tr, xx0) <- infer x0
    xxs <- for xs $ \x -> check x tr
    pure (TCon "List" [tr], Core.List $ xx0:xxs)
infer (Asc x t) = do
    t' <- rigidify t
    x' <- check x t'
    pure (t', x')

runInfer :: Infer a -> Env Expr.Type -> a
runInfer i e =
    evalUnionFind $ flip runReaderT initContext $ getInfer i
  where
    initContext = InferContext
        { inferGlobalEnv = e
        , inferLocalEnv = M.empty
        }

testInfer :: Env Expr.Type -> Expr -> (Type, Core.Expr)
testInfer env x = runInfer (infer x >>= firstF generaliseAll) env
  where
    firstF :: Functor f => (a -> f b) -> (a, c) -> f (b, c)
    firstF f (a, c) = (,c) <$> f a
