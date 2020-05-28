{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-
Module      :  Control.Grammar.Limits
Copyright   :  (c) Christian Gram Kalhauge 2020
License     :  BSD3
Maintainer  :  christian@kalhauge.dk

This module contains grammars.
-}
module Control.Grammar.Limits
  where

-- base
import Data.Semigroup
import Data.Monoid
import Data.Functor.Compose
import Data.Functor.Identity
import Control.Applicative
import Data.Functor.Contravariant

-- aeson
import Data.Aeson       as J
import Data.Aeson.Types as J

-- adjunctions
import Data.Functor.Contravariant.Rep 

class NatTransformable n where
  natmap :: (forall b. f b -> g b) -> n f -> n g

class NatComposeable n where
  natcomp :: (forall b. f b -> g b -> h b) -> n f -> n g -> n h
  -- natcomp :: n f -> n g -> n (Product f g)

class (NatTransformable (CoLimit a), NatComposeable (CoLimit a)) => HasCoLimit a where
  type CoLimit a :: (* -> *) -> *
  interpret  :: CoLimit a (Op b) -> a -> b
  construct  :: CoLimit a (Op a)

class (NatTransformable (Limit a), NatComposeable (Limit a)) => HasLimit a where
  type Limit a :: (* -> *) -> *
  extract :: Limit a ((->) a) 
  inject  :: Limit a ((->) b) -> b -> a

data Two a b f = Two 
  { noOne :: f a 
  , noTwo :: f b
  }

instance NatTransformable (Two a b) where
  natmap nat Two {..} = Two
    { noOne = nat noOne
    , noTwo = nat noTwo
    }

instance NatComposeable (Two a b) where
  natcomp comp a b  = Two
    { noOne = noOne a `comp` noOne b
    , noTwo = noTwo a `comp` noTwo b
    }

instance HasLimit (a, b) where
  type Limit (a, b) = Two a b
  extract = Two fst snd 
  inject Two {..} b = (noOne b, noTwo b)

data CoEither a b f = CoEither
  { ifLeft  :: f a
  , ifRight :: f b
  }

instance NatTransformable (CoEither a b) where
  natmap nat CoEither {..} = CoEither 
    { ifLeft = nat ifLeft
    , ifRight = nat ifRight 
    }
instance NatComposeable (CoEither a b) where
  natcomp comp a b = CoEither
    { ifLeft  = ifLeft a  `comp` ifLeft b
    , ifRight = ifRight a `comp` ifRight b
    }

instance HasCoLimit (Either a b) where
  type CoLimit (Either a b) = CoEither a b

  interpret CoEither {..} = \case
    Left  a -> index ifLeft  a
    Right b -> index ifRight b

  construct = CoEither 
    { ifLeft  = Op Left 
    , ifRight = Op Right
    }

data CoMaybe a f = CoMaybe 
  { ifJust :: f a
  , ifNothing :: f ()
  }

instance NatTransformable (CoMaybe a) where
  natmap nat CoMaybe {..} = CoMaybe 
    { ifJust = nat ifJust
    , ifNothing = nat ifNothing 
    }

instance NatComposeable (CoMaybe a) where
  natcomp comp a b = CoMaybe
    { ifJust    = ifJust a    `comp` ifJust b
    , ifNothing = ifNothing a `comp` ifNothing b
    }

instance HasCoLimit (Maybe a) where
  type CoLimit (Maybe a) = CoMaybe a

  interpret CoMaybe {..} = \case
    Just a  -> index ifJust    a
    Nothing -> index ifNothing ()

  construct = CoMaybe 
    { ifJust    = Op Just 
    , ifNothing = Op (const Nothing)
    }
