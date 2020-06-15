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
Module      :  Control.Grammar.Builder
Copyright   :  (c) Christian Gram Kalhauge 2020
License     :  BSD3
Maintainer  :  christian@kalhauge.dk

This module contains grammar builders.
-}
module Control.Grammar.Builder
  where

-- base
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Maybe
import Data.Void
import Data.Monoid
import Data.Foldable
import Control.Applicative
import Data.Functor.Contravariant


-- grammar
import Control.Grammar.Limits
import Control.Grammar.Prim


data family Accessor (f :: * -> *) (g :: (* -> *) -> *) (k :: * -> *) a
data instance Accessor f l g a =
  Accessor ((g a -> f (g a)) -> l g -> f (l g))

class Accessible (g :: (* -> *) -> *) where
  -- | Each item contains a lens that can update the current item
  accessors :: forall f k. Functor f => g (Accessor f g k)

type Collect l g = Endo (l (Compose Maybe g))

newtype StateCon l t f g a = StateCon
  { (=:) :: t a -> f (Collect l g) }

infix 2 =:


createStateCon :: forall l t f g.
  (Accessible l, NatComposable l, Functor f)
  => l (Desc t f g)
  -> l (StateCon l t f g)
createStateCon = natcomp mapper accessors
 where
  mapper :: forall b.
    Accessor Identity l (Compose Maybe g) b
    -> Desc t f g b
    -> StateCon l t f g b
  mapper (Accessor lens) (Desc fn) = StateCon \ta ->
    (\lig' -> Endo \lg -> runIdentity $ lens (\case
          Compose Nothing  -> Identity (Compose (Just lig'))
          Compose (Just _) -> error "Already set"
        ) lg
    ) <$> fn ta

buildSum :: forall t g a.
  (HasSumG t g, HasCoLimit a, NatTraversable (CoLimit a), Accessible (CoLimit a))
  => (forall k f. CoLimit a (StateCon (CoLimit a) t f k) -> [f (Collect (CoLimit a) k)])
  -> g a
buildSum fn = sumG \colim -> do
  actions :: [Collect (CoLimit a) k]
    <- sequenceA (fn $ createStateCon colim)
  pure $ case (natseq $ appEndo (fold actions) (emptyC colim)) of
    Just res -> res
    Nothing -> error "Missing variables"
 where
   emptyC = natmap (const $ Compose Nothing)

buildProd :: forall t g a.
  (HasProdG t g, HasLimit a, NatTraversable (Limit a), Accessible (Limit a))
  => (forall k f.
      (t () -> f (Collect (Limit a) k))
      -> Limit a (StateCon (Limit a) t f k)
      -> [f (Collect (Limit a) k)]
      )
  -> g a
buildProd fn = prodG \cnt colim -> do
  actions :: [Collect (Limit a) k]
    <- sequenceA (fn (\ta -> Endo id <$ cnt ta) (createStateCon colim))
  pure $ case (natseq $ appEndo (fold actions) (emptyC colim)) of
    Just res -> res
    Nothing -> error "Missing variables"
 where
   emptyC = natmap (const $ Compose Nothing)

(=*) ::
  (HasProdG t t, HasLimit a, NatTraversable (Limit a), Accessible (Limit a))
  => StateCon l t f g a
  -> (forall k f.
      (t () -> f (Collect (Limit a) k))
      -> Limit a (StateCon (Limit a) t f k)
      -> [f (Collect (Limit a) k)]
      )
  -> f (Collect l g)
(=*) ta fn = ta =: buildProd fn
infix 2 =*

(=*!) ::
  (HasProdG t t, HasIso t)
  => StateCon l t f g a
  -> (forall k f.
      (t () -> f (Collect (One a) k))
      -> One a (StateCon (One a) t f k)
      -> [f (Collect (One a) k)]
      )
  -> f (Collect l g)
(=*!) ta fn =
  ta =: iso Single unSingle (buildProd fn)
infix 2 =*!

(=+) ::
  (HasSumG t t, HasCoLimit a, NatTraversable (CoLimit a), Accessible (CoLimit a))
  => StateCon l t f g a
  -> (forall k f. CoLimit a (StateCon (CoLimit a) t f k) -> [f (Collect (CoLimit a) k)])
  -> f (Collect l g)
(=+) ta fn = ta =: buildSum fn
infix 2 =+






instance Accessible (CoMaybe a) where
  accessors = CoMaybe
    { ifJust    = Accessor $ \fn s -> (\a -> s { ifJust    = a}) <$> fn (ifJust s)
    , ifNothing = Accessor $ \fn s -> (\a -> s { ifNothing = a}) <$> fn (ifNothing s)
    }

instance Accessible (Two a b) where
  accessors = Two
    { onOne = Accessor $ \fn s -> (\a -> s { onOne = a}) <$> fn (onOne s)
    , onTwo = Accessor $ \fn s -> (\a -> s { onTwo = a}) <$> fn (onTwo s)
    }

instance Accessible (One a) where
  accessors = One
    { onEvery = Accessor $ \fn s -> (\a -> s { onEvery = a }) <$> fn (onEvery s)
    }

maybeG' :: HasSumG t g => t a -> t () -> g (Maybe a)
maybeG' as bs = buildSum \CoMaybe {..} ->
  [ ifJust    =: as
  , ifNothing =: bs
  ]



