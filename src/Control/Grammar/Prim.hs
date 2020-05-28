{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DerivingVia #-}
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

-- control
import Control.Grammar.Limits

-- | A grammar, has a type t and goes from a to b, and backwards from b to
-- a.
data Grammar t a where
  Prim :: t a -> Grammar t a

  SumG ::
    HasCoLimit a
    => (forall m. Monoid m => CoLimit a (Const m) -> Const m b)
    -> CoLimit a (Grammar t)
    -> Grammar t a
  -- ^ A sum type encoding

  ProdG ::
    HasLimit a
    => (forall f. Applicative f => Limit a f -> f (Limit a Identity))
    -> Limit a (Grammar t)
    -> Grammar t a

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

-- JSON
data JsonG a = JsonG
  { aFromJSON  :: J.Value -> J.Parser a
  , aToJSON    :: a -> J.Encoding
  }

gToJSON :: Grammar JsonG a -> a -> J.Encoding
gToJSON = \case
  Prim t -> aToJSON t
  SumG _ co ->
    interpret $ natmap (Op . gToJSON) co
  -- ProdG fold co ->
  --   getConst . fold $ natcomp (\fa gm -> Const $ gToJSON gm <$> fa) extract co
     -- fold . distribute (natmap (Op . gToJSON) co)

newtype JsonParser a = JsonParser { unJsonParser :: J.Value -> J.Parser a }
  deriving Functor
  deriving Applicative via Compose ((->) J.Value) J.Parser
  deriving (Semigroup, Monoid) via (J.Value -> Alt J.Parser a)

instance Alternative JsonParser where
  empty = JsonParser (\v -> empty)
  JsonParser x <|> JsonParser y = JsonParser (\v -> x v <|> y v)

gFromJSON :: Grammar JsonG a -> JsonParser a
gFromJSON = \case
  Prim t -> JsonParser $ aFromJSON t
  SumG fold co ->
    getConst $ fold 
      (natcomp (\op grm -> Const $ getOp op <$> gFromJSON grm) 
        construct co
      )
  ProdG unfold co -> do
    x <- unfold (natmap gFromJSON co)
    pure $ inject (natmap (const . runIdentity) x) ()

     -- getConst . fold $ natcomp (\fa gm -> Const $ gFromJSON gm <$> fa) extract co

