{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module Typecheck where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Map.Strict (Map)
import Data.Monoid (First(..))
import Data.Text (Text)
import Data.Traversable (for)

import qualified Data.Map.Strict as M
import qualified Data.Text as T

import Expr hiding (Type(..))
import qualified Expr
import Core (Var(..), Type(..), TV(..), InferError(..))
import qualified Core

type Env t = Map Text t

data InferContext = InferContext
    { inferGlobalExpr :: Env Expr.Type
    , inferLocalExpr :: Env Type
    } deriving (Eq, Show)

data InferState = InferState
    { inferCounter :: Int
    , inferSubst   :: Map Var Type
    } deriving (Eq, Show)

modifyLocalExpr :: (Env Type -> Env Type) -> InferContext -> InferContext
modifyLocalExpr f = \i -> i { inferLocalExpr = f $ inferLocalExpr i }

newtype Infer a = Infer { getInfer :: ReaderT InferContext (State InferState) a }
    deriving (Functor, Applicative, Monad, MonadReader InferContext, MonadState InferState)

rigidify :: Expr.Type -> Infer Type
rigidify (Expr.TQVar v) = pure $ TRigid $ WrapVar v
rigidify (Expr.TFun ats rt) = TFun <$> traverse rigidify ats <*> rigidify rt
rigidify (Expr.TCon t ts) = TCon t <$> traverse rigidify ts

lookupVar :: Text -> Infer (Maybe (Either Expr.Type Type))
lookupVar t = asks $ \c ->
    case M.lookup t (inferLocalExpr c) of
        Just v -> Just $ Right v
        Nothing ->
            case M.lookup t (inferGlobalExpr c) of
                Just v -> Just $ Left v
                Nothing -> Nothing

getLink :: Var -> Infer TV
getLink v = gets $ \s ->
    maybe Unbound Link $ M.lookup v (inferSubst s)

writeLink :: Var -> Type -> Infer ()
writeLink v t = modify $ \s ->
    s { inferSubst = M.insert v t $ inferSubst s }
    
withEnv :: (Env Type -> Env Type) -> Infer a -> Infer a
withEnv = local . modifyLocalExpr

fresh :: Infer Int
fresh = do
    i <- gets inferCounter
    modify $ \s -> s { inferCounter = i+1 }
    pure i

gensym :: Infer Var
gensym = WrapVar . ("t"<>) . T.pack . show <$> fresh

newvar :: Infer Type
newvar = TVar <$> gensym

concatTraverse :: Applicative m => (a -> m [b]) -> [a] -> m [b]
concatTraverse f xs = concat <$> traverse f xs

free :: Type -> Infer [Var]
free (TVar v) = getLink v >>= \case
    Unbound -> pure [v]
    Link t ->  free t
free (TFun ats rt) = (++) <$> concatTraverse free ats <*> free rt
free _ = pure []

allFree :: Infer [Var]
allFree = concatTraverse free =<< asks (M.elems . inferLocalExpr)

occurs :: Var -> Type -> Infer a -> Infer (Maybe InferError)
occurs = \v t m -> occurs' v t >>= \case
    Nothing -> Nothing <$ m
    err -> pure err
  where
    occurs' :: Var -> Type -> Infer (Maybe InferError)
    occurs' v = \case
        TVar w
          | v == w -> pure $ Just OccursError
          | otherwise -> getLink w >>= \case
            Link t -> occurs' v t
            _ -> pure Nothing
        TFun ats rt -> do
            os <- traverse (occurs' v) ats
            case foldMap First os of
                First Nothing -> occurs' v rt
                First err -> pure err
        _ -> pure Nothing
 
instantiate :: Type -> Infer Type
instantiate = fmap fst . go M.empty
  where
    go :: Map Var Type
        -> Type
        -> Infer (Type, Map Var Type)
    go subst (TCon t ats) = do
        (ats', subst') <- goMany subst ats
        pure (TCon t ats', subst')
    go subst (TVar v) = getLink v >>= \case
        Unbound -> pure (TVar v, subst)
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

generalise :: Type -> Infer Type
generalise = \t -> allFree >>= \fs -> go fs t
  where
    go :: [Var] -> Type -> Infer Type
    go fs (TCon t ats) = TCon t <$> traverse (go fs) ats
    go fs (TVar v) = getLink v >>= \case
        Unbound
            | v `elem` fs -> pure $ TVar v
            | otherwise -> pure $ TQVar v
        Link t -> go fs t
    go _fs (TRigid v) = pure $ TQVar v
    go _fs (TQVar v) = pure $ TQVar v
    go fs (TFun ats rt) = TFun <$> traverse (go fs) ats <*> go fs rt
    go _fs (TError err) = pure $ TError err

generaliseAll :: Type -> Infer Type
generaliseAll = \t -> allFree >>= \fs -> go fs t
  where
    go :: [Var] -> Type -> Infer Type
    go fs (TCon t ats) = TCon t <$> traverse (go fs) ats
    go fs (TVar v) = getLink v >>= \case
        Unbound
            | v `elem` fs -> do
                  let fs' = TVar <$> fs
                  error $ "generaliseAll: extra free! " ++ show (v, fs')
            | otherwise -> pure $ TQVar v
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
    subtype' (TVar v1) t2 = getLink v1 >>= \case
        Unbound -> occurs v1 t2 $ writeLink v1 t2
        Link t1' -> t1' `subtype'` t2
    subtype' t1 (TVar v2) = getLink v2 >>= \case
        Unbound -> occurs v2 t1 $ writeLink v2 t1
        Link t2' -> t1 `subtype'` t2'
    subtype' (TFun at1s rt1) (TFun at2s rt2) = do
        os <- zipWithM subtype' at2s at1s  -- note arguments flipped!
        case foldMap First os of
            First Nothing -> rt1 `subtype'` rt2
            First err -> pure err
    subtype' (TError _) _ = pure Nothing
    subtype' t1 t2 = pure $ Just $ CannotUnify t1 t2

deferError :: InferError -> (Type, Core.Expr)
deferError e = (TError e, Core.Deferred e)

check :: Expr -> Type -> Infer Core.Expr
check (App f as) t = do
    (tf, xf) <- infer f
    atas <- for as $ \a -> (a,) <$> newvar
    let tas = snd <$> atas
    (tf `subtype` TFun tas t) Core.Deferred $ do  -- check function returns specified type
        xas <- for atas $ \(a_given, ta) -> do
            (ta_given, xa_given) <- infer a_given
            (ta_given `subtype` ta) Core.Deferred $  -- then check function accepts given arguments
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
    (t `subtype` tx) Core.Deferred $
        pure xx
    
infer :: Expr -> Infer (Type, Core.Expr)
infer (Lit n) = pure (TCon "Int" [], Core.Lit n)
infer (Var v) = lookupVar v >>= \case
    Nothing -> pure $ deferError $ UnknownName v
    Just t -> (,Core.Var v) <$> instantiate (either Core.exprToCore id t)
infer (App f as) = do
    (tf, xf) <- infer f
    _as <- traverse infer as
    let (tas, xas) = unzip _as
    tr <- newvar
    (tf `subtype` TFun tas tr) deferError $ do
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
        fmap snd $  -- can discard type returned from @subtype@
                    -- as only @tr@ is actually used in the end
            (tx `subtype` tr) deferError $ pure txx
    pure (TCon "List" [tr], Core.List xxs)
infer (Asc x t) = do
    t' <- rigidify t
    x' <- check x t'
    pure (t', x')

runInfer :: Infer a -> Env Expr.Type -> a
runInfer i e =
    flip evalState initState $ flip runReaderT initContext $ getInfer i
  where
    initContext = InferContext
        { inferGlobalExpr = e
        , inferLocalExpr = M.empty
        }
    initState = InferState
        { inferCounter = 0
        , inferSubst = M.empty
        }

testInfer :: Env Expr.Type -> Expr -> (Type, Core.Expr)
testInfer env x = runInfer (infer x >>= firstF generaliseAll) env
  where
    firstF :: Functor f => (a -> f b) -> (a, c) -> f (b, c)
    firstF f (a, c) = (,c) <$> f a
