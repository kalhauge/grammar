{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
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
module Control.Grammar.Json
  where

-- base
-- import Control.Applicative
import Data.Functor.Contravariant
import Control.Applicative
import Data.Functor.Compose
import Data.Monoid

-- mtl
import Control.Monad.Reader
import Control.Monad.State

-- vector
import qualified Data.Vector as V

-- bytestring
import qualified Data.ByteString.Lazy as BL

-- text
import Data.Text (Text)
import qualified Data.Text as Text

-- aeson
import Data.Aeson as J
import Data.Aeson.Types as J
import Data.Aeson.Encoding as J
import Data.Aeson.Parser as J
import Data.Aeson.Parser.Internal as J
import Data.Aeson.Internal as J

-- unordered-containers
import qualified Data.HashMap.Strict as HM

-- grammar
import Control.Grammar.Prim
-- import Control.Grammar.Limits

newtype JsonDecoder a = JsonDecoder { unJsonDecoder :: J.Value -> J.Parser a }
  deriving Functor
  deriving Applicative via Compose ((->) J.Value) J.Parser
  deriving (Semigroup, Monoid) via (J.Value -> Alt J.Parser a)

newtype JsonEncoder a = JsonEncoder { unJsonEncoder :: a -> J.Encoding}
  deriving Contravariant via Op J.Encoding

data JsonG a where
  JsonObjectG :: String -> Grammar JsonKeyG a -> JsonG a
  JsonArrayG  :: String -> Grammar JsonG a -> JsonG a
  JsonPrim    :: JsonDecoder a -> JsonEncoder a -> JsonG a

data JsonKeyG a = JsonKeyG
  { gJsonKey     :: Text
  , gJsonKeyGrammar :: JsonG a
  }

newtype JsonItemG a = JsonItemG
  { gJsonItemGrammar :: JsonG a
  }

(|=) :: Text -> JsonG a -> Grammar JsonKeyG a
(|=) t j = Prim $ JsonKeyG t j

encodeJsonG :: JsonG a -> a -> Encoding
encodeJsonG = \case
  JsonObjectG _ grm -> J.pairs . grammarToSeries grm
  JsonArrayG _ grm -> J.list id . grammarToArray grm
  JsonPrim _ encoder -> unJsonEncoder encoder

jsonGToLazyByteString :: JsonG a -> a -> BL.ByteString
jsonGToLazyByteString jg =
  J.encodingToLazyByteString . encodeJsonG jg

grammarToSeries :: Grammar JsonKeyG a -> a -> J.Series
grammarToSeries = foldGrammar \t a ->
  J.pair (gJsonKey t) (encodeJsonG (gJsonKeyGrammar t) a)

grammarToArray :: Grammar JsonG a -> a -> [J.Encoding]
grammarToArray = foldGrammar \t a ->
  [encodeJsonG t a]

nullG :: Grammar JsonG ()
nullG = Prim $ JsonPrim
  (JsonDecoder \v ->
    if v == J.Null then return () else fail "expected null"
  )
  (JsonEncoder $ const J.null_)

orNullG :: Grammar JsonG a -> Grammar JsonG (Maybe a)
orNullG t =
  maybeG t nullG

orNothingG :: Grammar JsonKeyG a -> Grammar JsonKeyG (Maybe a)
orNothingG t = maybeG t emptyG

jsonGFromLazyByteString :: JsonG a -> BL.ByteString -> Either String a
jsonGFromLazyByteString jg =
  eitherFormatError . J.eitherDecodeWith J.json (J.iparse $ decodeJsonG jg)
 where
  eitherFormatError :: Either (JSONPath, String) a -> Either String a
  eitherFormatError = either (Left . uncurry formatError) Right


decodeJsonG :: JsonG a -> J.Value -> J.Parser a
decodeJsonG = \case
  JsonPrim decoder _ -> unJsonDecoder decoder
  JsonObjectG name g -> J.withObject name (grammarFromObject g)
  JsonArrayG name g -> J.withArray name (grammarFromArray g)

grammarFromObject :: Grammar JsonKeyG a -> J.Object -> J.Parser a
grammarFromObject = runReaderT . unfoldGrammar \(JsonKeyG key p) ->
  ReaderT $ maybe empty (decodeJsonG p) . HM.lookup key

newtype StackM a = State [a]

grammarFromArray :: Grammar JsonG a -> J.Array -> J.Parser a
grammarFromArray grm arr = do
  (a, s) <- runStateT (run grm) (V.toList arr)
  case s of
    [] -> return a
    _ -> fail "too many items"
 where
  run = unfoldGrammar \jg -> StateT $ \case
    a:as -> (,as) <$> decodeJsonG jg a
    [] -> fail "too few items"

anyG :: (ToJSON a, FromJSON a) => JsonG a
anyG = JsonPrim
  (JsonDecoder $ J.parseJSON)
  (JsonEncoder $ J.toEncoding)

intG :: JsonG Int
intG = anyG

stringG :: JsonG String
stringG = anyG

textG :: JsonG Text
textG = anyG
