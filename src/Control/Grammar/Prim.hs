{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-
Module      :  Control.Grammar.Prim
Copyright   :  (c) Christian Gram Kalhauge 2020
License     :  BSD3
Maintainer  :  christian@kalhauge.dk

This module contains grammars.
-}
module Control.Grammar.Prim
  where

-- base
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Maybe
import Data.Void
import Data.Monoid
import Control.Applicative
import Data.Functor.Contravariant

import Control.Monad.State
import Control.Monad.Writer

-- grammar
import Control.Grammar.Limits

-- | A Patial Isomorphism Description
newtype Desc t f g a = Desc
  { (<:) :: t a -> f (g a) }

type SumCon t l =
  (forall f g. Applicative f => l (Desc t f g) -> f (l g))

data SumG t a = HasCoLimit a => SumG (SumCon t (CoLimit a))

sumDesc :: forall a t. SumG t a -> CoLimit a t
sumDesc (SumG runSum) =
  runIdentity $ runSum
    (natmap (const $ Desc (\ta -> Identity ta)) (construct @a))

sumOrder :: forall f a t. Alternative f => SumG t a -> CoLimit a f -> f a
sumOrder (SumG runSum) clim =
  getAlt . getConst $ runSum (natcomp comp clim construct)
 where comp a (Op op) = Desc . const . Const . Alt $ op <$> a

foldSumG   :: (forall b. t b -> b ->  m) -> SumG t a -> a -> m
foldSumG compress s@(SumG _) =
  interpret $ natmap (Op . compress) (sumDesc s)

unfoldSumG :: Alternative f => (forall b. t b -> m -> f b) -> SumG t a -> m -> f a
unfoldSumG expand s@(SumG _) m =
  sumOrder s (natmap (\tb -> expand tb m) (sumDesc s))

inspectSumG :: (forall b. t b -> m) -> SumG t a -> [m]
inspectSumG inspect s@(SumG _) =
  getOver $ (sumOrder s) (natmap (Over . (:[]) . inspect) (sumDesc s))

type ProdCon t l =
  (forall f g. Applicative f => (t () -> f ()) -> l (Desc t f g) -> f (l g))

data ProdG t a = HasLimit a => ProdG (ProdCon t (Limit a))

prodDesc :: forall a t. ProdG t a -> Limit a t
prodDesc (ProdG runProd) =
  runIdentity $ runProd (\_ -> Identity ())
    (natmap (const $ Desc (\ta -> Identity ta)) (extract @a))

foldProdG :: forall a t m. Monoid m
  => (forall b. t b -> b -> m)
  -> ProdG t a
  -> a -> m
foldProdG compress (ProdG runProd) a =
  getConst $ runProd include' (natmap toM extract)

 where
   include' :: t () -> Const m ()
   include' t' = Const $ compress t' ()

   toM :: (a -> b) -> Desc t (Const m) g b
   toM getb = Desc (\t -> Const $ compress t (getb a))

unfoldProdG :: forall a t f m. Applicative f
  => (forall b. t b -> m -> f b)
  -> ProdG t a
  -> m
  -> f a
unfoldProdG expand (ProdG runProd) m = do
  x <- runProd (\t' -> expand t' m)
    (natmap (\_ -> Desc \tb -> const <$> expand tb m) (extract @a))
  pure $ inject x ()

inspectProdG :: forall a t m.
  (forall b. t b -> m)
  -> ProdG t a
  -> [m]
inspectProdG inspect (ProdG runProd) = do
  getConst $ runProd (Const . (:[]) . inspect)
    (natmap (\_ -> Desc \tb -> Const $ [inspect tb]) (extract @a))


class HasIso g where
  iso :: (a -> b) -> (b -> a) -> g b -> g a

class HasSumG t g | g -> t where
  sumG :: HasCoLimit a => SumCon t (CoLimit a) -> g a

instance HasSumG t (SumG t) where
  sumG = SumG

class HasProdG t g | g -> t where
  prodG :: HasLimit a => ProdCon t (Limit a) -> g a

instance HasProdG t (ProdG t) where
  prodG = ProdG

-- | Helper overapproximation
newtype Over m b = Over { getOver :: m }
  deriving Functor

instance Monoid m => Applicative (Over m) where
  pure a = Over mempty
  Over a <*> Over b = Over (a <> b)

instance Monoid m => Alternative (Over m) where
  empty = Over mempty
  Over a <|> Over b = Over (a <> b)
