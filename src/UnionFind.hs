{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module UnionFind
       ( UnionFind
       , evalUnionFind
       , UnionFindT
       , evalUnionFindT
       , Uniq(..)
       , Link(..)
       , MonadUnionFind(..)
       ) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict (StateT(..))
import Control.Monad.Writer.Class (MonadWriter)
import Data.Functor.Identity
import Data.IntMap.Strict (IntMap)

import qualified Data.IntMap.Strict as IM

type UnionFind t = UnionFindT t Identity

newtype UnionFindT t m a = UnionFindT ((IntMap t, Int) -> m (a, (IntMap t, Int)))
    deriving (Functor, Applicative, Monad) via (StateT (IntMap t, Int) m)

deriving via (StateT (IntMap t, Int)) instance MonadTrans (UnionFindT t)
deriving via (StateT (IntMap t, Int) m) instance MonadReader r m => MonadReader r (UnionFindT t m)
deriving via (StateT (IntMap t, Int) m) instance MonadWriter w m => MonadWriter w (UnionFindT t m)
deriving via (StateT (IntMap t, Int) m) instance MonadError e m => MonadError e (UnionFindT t m)
    
evalUnionFindT :: Functor m => UnionFindT t m a -> m a
evalUnionFindT (UnionFindT u) = fst <$> u (IM.empty, 0)

evalUnionFind :: UnionFind t a -> a
evalUnionFind = runIdentity . evalUnionFindT

newtype Uniq = Uniq { label :: Int }
    deriving (Eq, Show, Ord)

data Link t = Unbound | Link t
    deriving (Eq, Show)

class Monad m => MonadUnionFind t m | m -> t where
    newCount :: m Int
    newVar :: m Uniq
    readLink :: Uniq -> m (Link t)
    writeLink :: Uniq -> t -> m ()

instance Monad m => MonadUnionFind t (UnionFindT t m) where
    newCount = UnionFindT $ \(m, c) -> pure (c, (m, c+1))
    newVar = UnionFindT $ \(m, c) -> pure (Uniq c, (m, c+1))
    readLink (Uniq i) = UnionFindT $ \s@(m,_) -> pure (maybe Unbound Link $ IM.lookup i m, s)
    writeLink (Uniq i) t = UnionFindT $ \(m,c) -> pure ((), (IM.insert i t m, c))

instance MonadUnionFind t m => MonadUnionFind t (ReaderT r m) where
    newCount = lift newCount
    newVar = lift newVar
    readLink = lift . readLink
    writeLink = (lift .) . writeLink

instance MonadUnionFind t m => MonadUnionFind t (StateT s m) where
    newVar = lift newVar
    newCount = lift newCount
    readLink = lift . readLink
    writeLink = (lift .) . writeLink

instance MonadUnionFind t m => MonadUnionFind t (ExceptT e m) where
    newCount = lift newCount
    newVar = lift newVar
    readLink = lift . readLink
    writeLink = (lift .) . writeLink
