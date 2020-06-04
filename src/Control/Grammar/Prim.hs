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
import Data.Maybe
import Data.Void
import Data.Monoid
import Control.Applicative
import Data.Functor.Contravariant

-- grammar
import Control.Grammar.Limits

-- | A sum grammar
data SumG t a = HasCoLimit a => SumG
  { sumDesc  :: CoLimit a t
    -- ^ The description of the sum.
  , sumOrder :: forall f. Alternative f => CoLimit a f -> f a
    -- ^ The order of the sum; not all grammars are commutative.
  }

foldSumG   :: (forall b. t b -> b ->  m) -> SumG t a -> a -> m
foldSumG compress (SumG {..}) =
  interpret $ natmap (Op . compress) sumDesc

unfoldSumG :: Alternative f => (forall b. t b -> m -> f b) -> SumG t a -> m -> f a
unfoldSumG expand (SumG {..}) m =
  sumOrder (natmap (\tb -> expand tb m) sumDesc)

inspectSumG :: (forall b. t b -> m) -> SumG t a -> [m]
inspectSumG inspect (SumG {..}) =
  getOver $ sumOrder (natmap (Over . (:[]) . inspect) sumDesc)

defaultSumOrder :: (HasCoLimit a, NatFoldable (CoLimit a), Alternative f) => CoLimit a f -> f a
defaultSumOrder =
  getAlt . natfold . natcomp (\(Op op) -> Const . Alt . fmap op) construct

class HasSumG t g | g -> t where
  sumG :: HasCoLimit a
    => CoLimit a t
    -> (forall f. Alternative f => CoLimit a f -> f a)
    -> g a

instance HasSumG t (SumG t) where
  sumG = SumG


-- | A simple sum without explicit order
simpleSumG :: (HasSumG t g, NatFoldable (CoLimit a), HasCoLimit a) => CoLimit a t -> g a
simpleSumG colim = sumG colim defaultSumOrder

-- | A product grammar
data ProdG t a = HasLimit a => ProdG
  { prodDesc  :: Limit a t
    -- ^ The description of the product.
  , prodOrder :: forall f. Applicative f => Limit a f -> f a
    -- ^ The order of the product; not all grammars are commutative.
  }

foldProdG :: Monoid m => (forall b. t b -> b -> m) -> ProdG t a -> a -> m
foldProdG compress (ProdG {..}) =
  getConst . prodOrder $ natcomp (\fa gm -> Const $ compress gm <$> fa) extract prodDesc

unfoldProdG :: Applicative f => (forall b. t b -> m -> f b) -> ProdG t a -> m -> f a
unfoldProdG expand (ProdG {..}) m =
  prodOrder (natmap (\tb -> expand tb m) prodDesc)


inspectProdG :: (forall b. t b -> m) -> ProdG t a -> [m]
inspectProdG inspect (ProdG {..}) =
  getOver $ prodOrder (natmap (Over . (:[]) . inspect) prodDesc)

defaultProdOrder :: (HasLimit a, NatTraversable (Limit a), Applicative f) => Limit a f -> f a
defaultProdOrder lim =
  ($ ()). inject . natmap (const . runIdentity) <$> natseq lim

class HasProdG t g | g -> t where
  prodG :: HasLimit a
    => Limit a t
    -> (forall f. Applicative f => Limit a f -> f a)
    -> g a

instance HasProdG t (ProdG t) where
  prodG = ProdG

-- | A simple sum without explicit order
simpleProdG :: (HasProdG t g, NatTraversable (Limit a), HasLimit a) => Limit a t -> g a
simpleProdG lim = prodG lim defaultProdOrder

oneG :: HasProdG t g => g ()
oneG = prodG Terminal (\Terminal -> pure ())

zeroG :: HasSumG t g => g Void
zeroG = sumG Terminal (const empty)

tupleG :: HasProdG t g => t a -> t b -> g (a, b)
tupleG ag bg = simpleProdG (Two ag bg)

maybeG :: HasSumG t g => t a -> t () -> g (Maybe a)
maybeG as bs = simpleSumG (CoMaybe as bs)
--
-- emptyG :: Grammar t ()
-- emptyG = ProdG (\(Terminal ()) -> pure (Terminal ())) (Terminal ())
--
-- simpleProdG ::
--     (HasLimit a, NatTraversable (Limit a))
--     => Limit a (Grammar t)
--     -> Grammar t a
-- simpleProdG = ProdG natseq
--
-- withDefaultG :: a -> Grammar t (Maybe a) -> Grammar t a
-- withDefaultG a = IsoG (fromMaybe a) Just
--
-- foldGrammar :: forall t m a. Monoid m => (forall a. t a -> a -> m) -> Grammar t a -> a -> m
-- foldGrammar ta = go where
--   go :: forall a. Grammar t a -> a -> m
--   go = \case
--     Prim t ->
--       ta t
--     IsoG a2b b2a t ->
--       foldGrammar ta t . b2a
--     SumG _ co ->
--       interpret $ natmap (Op . go) co
--     ProdG fold co ->
--       getConst . fold $ natcomp (\fa gm -> Const $ go gm <$> fa) extract co
--
--
-- unfoldGrammar :: Alternative g => (forall a. t a -> g a) -> Grammar t a -> g a
-- unfoldGrammar ta = \case
--   Prim t ->
--     ta t
--   IsoG a2b b2a t ->
--     a2b <$> unfoldGrammar ta t
--   SumG fold co ->
--     getAlt . getConst $ fold
--        (natcomp (\op grm -> Const . Alt $ getOp op <$> unfoldGrammar ta grm)
--          construct co
--        )
--   ProdG unfold co -> do
--     x <- unfold (natmap (unfoldGrammar ta) co)
--     pure $ inject (natmap (const . runIdentity) x) ()

--
--   ProdG unfold co -> do
--     x <- unfold (natmap gFromJSON co)
--     pure $ inject (natmap (const . runIdentity) x) ()

-- | Helper overapproximation
newtype Over m b = Over { getOver :: m }
  deriving Functor

instance Monoid m => Applicative (Over m) where
  pure a = Over mempty
  Over a <*> Over b = Over (a <> b)

instance Monoid m => Alternative (Over m) where
  empty = Over mempty
  Over a <|> Over b = Over (a <> b)
