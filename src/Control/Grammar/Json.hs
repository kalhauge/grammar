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
import Control.Grammar.Limits

newtype JsonDecoder a = JsonDecoder { unJsonDecoder :: J.Value -> J.Parser a }
  deriving Functor
  deriving Applicative via Compose ((->) J.Value) J.Parser
  deriving (Semigroup, Monoid) via (J.Value -> Alt J.Parser a)

newtype JsonEncoder a = JsonEncoder { unJsonEncoder :: a -> J.Encoding}
  deriving Contravariant via Op J.Encoding

data JsonG a where
  JsonPrim ::
    JsonDecoder a -> JsonEncoder a -> JsonG a
  JsonSumG ::
    SumG JsonG a -> JsonG a
  JsonObjectG ::
    String -> ProdG JsonKeyG a -> JsonG a
  JsonArrayG  ::
    String -> ProdG JsonG a -> JsonG a

data JsonKeyG a where
  JsonKeyG :: Text -> JsonG a -> JsonKeyG a
  RemovableJsonKeyG :: Text -> JsonG a -> JsonKeyG (Maybe a)

(|=) :: Text -> JsonG a -> JsonKeyG a
(|=) = JsonKeyG

(?=) :: Text -> JsonG a -> JsonKeyG (Maybe a)
(?=) = RemovableJsonKeyG

encodeJsonG :: JsonG a -> a -> Encoding
encodeJsonG = \case
  JsonSumG sum -> foldSumG encodeJsonG sum
    -- J.pairs . grammarToSeries grm
  JsonObjectG _ prod ->
    J.pairs <$>
      foldProdG (\case
        JsonKeyG key g -> J.pair key . encodeJsonG g
        RemovableJsonKeyG key g -> maybe mempty (J.pair key . encodeJsonG g)
      ) prod
  JsonArrayG _ prod ->
    J.list id <$> foldProdG
      (\t -> (:[]) . encodeJsonG t )
      prod
  JsonPrim _ encoder ->
    unJsonEncoder encoder

decodeJsonG :: JsonG a -> J.Value -> J.Parser a
decodeJsonG = \case
  JsonSumG sum -> unfoldSumG decodeJsonG sum
  JsonPrim decoder _ -> unJsonDecoder decoder
  JsonObjectG name g -> J.withObject name $ unfoldProdG unObject g
  JsonArrayG name g -> J.withArray name $ \arr -> do
    (a, s) <- runStateT (unfoldProdG unArray g ()) (V.toList arr)
    case s of
      [] -> return a
      a -> fail ("too many items")

 where
  unObject :: JsonKeyG a -> J.Object -> J.Parser a
  unObject = \case
    JsonKeyG key p ->
      maybe empty (decodeJsonG p) . HM.lookup key
    RemovableJsonKeyG key p ->
      maybe (pure Nothing) (fmap Just . decodeJsonG p) . HM.lookup key

  unArray :: JsonG a -> () -> StateT [J.Value] J.Parser a
  unArray jg () = StateT $ \case
      a:as -> (,as) <$> decodeJsonG jg a
      [] -> fail "too few items"


jsonGToLazyByteString :: JsonG a -> a -> BL.ByteString
jsonGToLazyByteString jg =
  J.encodingToLazyByteString . encodeJsonG jg

objectG :: (NatTraversable (Limit a), HasLimit a) => String -> Limit a JsonKeyG -> JsonG a
objectG name = JsonObjectG name . simpleProdG

arrayG :: (NatTraversable (Limit a), HasLimit a) => String -> Limit a JsonG -> JsonG a
arrayG name = JsonArrayG name . simpleProdG

nullG :: JsonG ()
nullG = JsonPrim
  (JsonDecoder \v ->
    if v == J.Null then return () else fail "expected null"
  )
  (JsonEncoder $ const J.null_)

jsonGFromLazyByteString :: JsonG a -> BL.ByteString -> Either String a
jsonGFromLazyByteString jg =
  eitherFormatError . J.eitherDecodeWith J.json (J.iparse $ decodeJsonG jg)
 where
  eitherFormatError :: Either (JSONPath, String) a -> Either String a
  eitherFormatError = either (Left . uncurry formatError) Right

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
