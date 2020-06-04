{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DerivingVia #-}
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
import Data.Monoid
import Control.Applicative
import Data.Functor.Contravariant

-- grammar
import Control.Grammar.Limits



-- | A grammar, has a type t and goes from a to b, and backwards from b to
-- a.
data Grammar t a where
  -- | A Primitive Grammar, defined by `t`
  Prim ::
    t a
    -> Grammar t a

  -- | Iso-morphisms are always welcome, and should be transparent
  -- to the end user.
  IsoG ::
    (a -> b)
    -> (b -> a)
    -> Grammar t a
    -> Grammar t b

  -- | A sum type defined with CoLimit
  SumG ::
    HasCoLimit a
    => (forall m. Monoid m => CoLimit a (Const m) -> Const m b)
    -> CoLimit a (Grammar t)
    -> Grammar t a

  -- | A product type defined with Limits
  ProdG ::
    HasLimit a
    => (forall f. Applicative f => Limit a f -> f (Limit a Identity))
    -> Limit a (Grammar t)
    -> Grammar t a


--   -- | Introduce a scope, this is usefull for recursive defintions
--   -- and to create contexts for grammars.
--   ScopeG ::
--     Applicative m
--     => ((String -> (s -> Grammar t a) -> m (Key a)) -> m (Key b, s))
--     -> Grammar t b
--
--   -- | We can lookup keys in the grammar.
--   LookupG ::
--     Key a
--     -> Grammar t a
--
-- newtype Key a = Key String
--
-- recG :: String -> (Grammar t a -> Grammar t a) -> Grammar t a
-- recG name rec = ScopeG $ \keyfn ->
--   let k = keyfn name \s -> rec (LookupG s)
--   in (k, k)

(<.>) :: Semigroup m => Const m b -> Const m c -> Const m c
b <.> c = phantom b <> c

idF :: Functor f => f a -> f (Identity a)
idF = fmap Identity

tupleG :: Grammar t a -> Grammar t b -> Grammar t (a, b)
tupleG ag bg = ProdG
  (\Two {..} -> Two <$> idF noOne <*> idF noTwo)
  (Two ag bg)

maybeG :: Grammar t a -> Grammar t () -> Grammar t (Maybe a)
maybeG as bs = SumG
  (\CoMaybe {..} -> phantom ifJust <> ifNothing)
  (CoMaybe as bs)

emptyG :: Grammar t ()
emptyG = ProdG (\(Terminal ()) -> pure (Terminal ())) (Terminal ())

simpleProdG ::
    (HasLimit a, NatTraversable (Limit a))
    => Limit a (Grammar t)
    -> Grammar t a
simpleProdG = ProdG natseq

withDefaultG :: a -> Grammar t (Maybe a) -> Grammar t a
withDefaultG a = IsoG (fromMaybe a) Just

foldGrammar :: forall t m a. Monoid m => (forall a. t a -> a -> m) -> Grammar t a -> a -> m
foldGrammar ta = go where
  go :: forall a. Grammar t a -> a -> m
  go = \case
    Prim t ->
      ta t
    IsoG a2b b2a t ->
      foldGrammar ta t . b2a
    SumG _ co ->
      interpret $ natmap (Op . go) co
    ProdG fold co ->
      getConst . fold $ natcomp (\fa gm -> Const $ go gm <$> fa) extract co


unfoldGrammar :: Alternative g => (forall a. t a -> g a) -> Grammar t a -> g a
unfoldGrammar ta = \case
  Prim t ->
    ta t
  IsoG a2b b2a t ->
    a2b <$> unfoldGrammar ta t
  SumG fold co ->
    getAlt . getConst $ fold
       (natcomp (\op grm -> Const . Alt $ getOp op <$> unfoldGrammar ta grm)
         construct co
       )
  ProdG unfold co -> do
    x <- unfold (natmap (unfoldGrammar ta) co)
    pure $ inject (natmap (const . runIdentity) x) ()

--
--   ProdG unfold co -> do
--     x <- unfold (natmap gFromJSON co)
--     pure $ inject (natmap (const . runIdentity) x) ()


