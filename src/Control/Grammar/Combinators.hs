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
Module      :  Control.Grammar.Combinators
Copyright   :  (c) Christian Gram Kalhauge 2020
License     :  BSD3
Maintainer  :  christian@kalhauge.dk

This module contains grammars.
-}
module Control.Grammar.Combinators
  where

-- base
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Foldable
import Data.Maybe
import Data.Void
import Data.Monoid
import Control.Applicative (Const (..))
import Data.Functor.Contravariant

-- grammar
import Control.Grammar.Limits
import Control.Grammar.Prim

-- | A simple product without explicit order
defP :: (HasProdG t g, NatTraversable (Limit a), HasLimit a) => Limit a t -> g a
defP lim = prodG $ \fn s ->
  natseq (natcomp (\t c -> Compose $ t <: c) s lim)

-- | A simple sum without explicit order
defS :: (HasSumG t g, NatTraversable (CoLimit a), HasCoLimit a) => CoLimit a t -> g a
defS colim = sumG $ \s ->
  natseq (natcomp (\t c -> Compose $ t <: c) s colim)

elimRight :: HasIso g => g (a, ()) -> g a
elimRight = iso (\a -> (a, ())) (\(a,()) -> a)

introRight :: HasIso g => g a -> g (a, ())
introRight = iso (\(a,()) -> a) (\a -> (a, ()))

elimLeft :: HasIso g => g ((), a) -> g a
elimLeft = iso (\a -> ((),a)) (\((), a) -> a)

introLeft :: HasIso g => g a -> g ((), a)
introLeft = iso (\((), a) -> a) (\a -> ((),a))

(<**) :: (HasProdG t g, HasIso g) => t a -> t () -> g a
(<**) ta tm = elimRight $ ta <**> tm

(**>) :: (HasProdG t g, HasIso g) => t () -> t a -> g a
(**>) tm ta = elimLeft $ tm <**> ta

(<**>) :: (HasProdG t g) => t a -> t b -> g (a, b)
(<**>) tm ta = defP $ Two tm ta

maybeG :: HasSumG t g => t a -> t () -> g (Maybe a)
maybeG as bs = defS (CoMaybe as bs)

eitherG :: HasSumG t g => t a -> t b -> g (Either a b)
eitherG as bs = defS (CoEither as bs)

oneG :: HasProdG t g => g ()
oneG = prodG \fn Terminal -> pure Terminal

zeroG :: HasSumG t g => g Void
zeroG = sumG \Terminal -> pure Terminal


