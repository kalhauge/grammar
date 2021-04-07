{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-
Module      :  Control.Grammar.Natural
Copyright   :  (c) Christian Gram Kalhauge 2020
License     :  BSD3
Maintainer  :  christian@kalhauge.dk

In this module we define the bare minimum of constructs that we are going
to use later.

-}
module Control.Grammar.Natural
  where

-- base
import Data.Proxy
import Data.Functor.Compose
import Data.Functor.Product
import Data.Functor.Identity


-- | A natural tranformation (informally) is a function that can convert
-- a type 'f a' to 'g a', regardless of the 'a'. For example, there exist
-- a natural tranformation from lists '[a]' to 'Set a' called 'fromList'.
type (~>) f g = (forall a. f a -> g a)

-- | Natural tranformation identity
natId :: f ~> f
natId fa = fa

-- | Natural tranformation composition
natComp ::
  g ~> h
  -> f ~> g
  -> f ~> h
natComp ngh nfg = \fa -> ngh (nfg fa)

{-| Let 'n' be a functor in the category of functors.
The morphisms in that category is a natural transformation.

[Identity] @'natMap' 'natId' == 'id'@
[Composition] @'natMap' ('natComp' f g) == 'natMap' f . 'natMap' g

-}
class NatFunctor (n :: (* -> *) -> *) where
  natMap :: (f ~> g) -> n f -> n g


{-| We also have an applicative in that category.

Well actually, it's not applicative as it is only a semigroup. (It does not have pure)

-}
class NatFunctor n => NatApplicative n where
  natPure :: (forall a. f a) -> n f
  natAp :: n f -> n g -> n (Product f g)

unProduct :: (forall a. f a -> g a -> h a) -> Product f g ~> h
unProduct fgha (Pair fa ga) = fgha fa ga

-- | Equivilent to liftA2
liftNat2 :: NatApplicative n => (forall a. f a -> g a -> h a) -> n f -> n g -> n h
liftNat2 fgha nf ng = natMap (unProduct fgha) (natAp nf ng)

-- | REMOVE? If n is a functor of functors, and we can run some part of
-- the functor outside the structure. then we call it natural traversable.
class NatFunctor n => NatTraversable n where
  natSeq :: Applicative f => n (Compose f g) -> f (n g)


{-| Most of the natural functors we are looking at are also
    representable.

    (https://hackage.haskell.org/package/adjunctions-4.4/docs/Data-Functor-Rep.html)
-}
class NatFunctor n => NatRepresentable n where
  type NRep n :: * -> *
  natTabulate :: (forall x. NRep n x -> f x) -> n f
  natIndex :: n f -> NRep n x -> f x


-- | None is a very simple Natural Applicative.
data None (f :: * -> *) = None

instance NatFunctor None where
  natMap nat None = None

instance NatApplicative None where
  natPure fa = None
  natAp None None = None

instance NatTraversable None where
  natSeq None = pure None

data IxNone x

instance NatRepresentable None where
  type NRep None = IxNone
  natTabulate f = None
  natIndex None = \case


-- | One is a relatively simple Natural Applicative
data One a f = One
  { onOneOfOne :: f a
  }

instance NatFunctor (One a) where
  natMap nat (One fa) = One (nat fa)

instance NatApplicative (One a) where
  natPure pf = One pf
  natAp (One fa) (One ga) = One (Pair fa ga)

instance NatTraversable (One a) where
  natSeq (One (Compose fga)) = One <$> fga

data IxOne a x where
  OneOfOne :: IxOne a a

instance NatRepresentable (One a) where
  type NRep (One a) = IxOne a
  natTabulate fn = One (fn OneOfOne)
  natIndex (One a) OneOfOne = a


-- | Two is a more interesting Natural Applicative
data Two a b f = Two
  { onOneOfTwo :: f a
  , onTwoOfTwo :: f b
  }

instance NatFunctor (Two a b) where
  natMap nat (Two fa fb) = Two (nat fa) (nat fb)

instance NatApplicative (Two a b) where
  natPure pf = Two pf pf
  natAp (Two fa fb) (Two ga gb) = Two (Pair fa ga) (Pair fb gb)

instance NatTraversable (Two a b) where
  natSeq (Two (Compose fga) (Compose fgb)) = Two <$> fga <*> fgb

instance NatRepresentable (Two a b) where
  type NRep (Two a b) = IxTwo a b
  natTabulate fn = Two (fn OneOfTwo) (fn TwoOfTwo)
  natIndex Two {..} = \case
    OneOfTwo -> onOneOfTwo
    TwoOfTwo -> onTwoOfTwo

data IxTwo a b x where
  OneOfTwo :: IxTwo a b a
  TwoOfTwo :: IxTwo a b b


