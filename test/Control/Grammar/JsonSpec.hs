{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
module Control.Grammar.JsonSpec
  where

import Test.Hspec

-- data
import Data.Functor.Identity

-- text
import Data.Text (Text)
import qualified Data.Text as Text

-- aeson
import Data.Aeson

-- grammar
import Control.Grammar.Json as J
import Control.Grammar
import Control.Grammar.TH

data Person = Person
  { personName   :: Text
  , personAge    :: Int
  , personPhone  :: Maybe Text
  , personParent :: Maybe Person
  } deriving (Show, Eq)

$(makeLimit ''Person)

personG :: JsonG Person
personG = objectG "Person" PersonLim
  { onPersonName =
      "name"   |= textG
  , onPersonAge =
      "age"    |= intG
  , onPersonPhone =
      "phone"  ?= textG
  , onPersonParent =
      "parent" ?= personG
  }

spec :: Spec
spec = do
  describe "encodeJsonG" do
    it "should be able to encode a person" do
      jsonGToLazyByteString personG
        (Person "Peter" 34 Nothing (Just $ Person "Else" 64 Nothing Nothing))
        `shouldBe` "{\"name\":\"Peter\",\"age\":34,\"parent\":{\"name\":\"Else\",\"age\":64}}"

      jsonGToLazyByteString personG
        (Person "Peter" 34 (Just "203-201-9923") Nothing)
        `shouldBe` "{\"name\":\"Peter\",\"age\":34,\"phone\":\"203-201-9923\"}"

    it "should be able to decode a person" do
      jsonGFromLazyByteString personG
        "{\"name\":\"Peter\",\"age\":34}"
        `shouldBe` Right (Person "Peter" 34 Nothing Nothing)

      jsonGFromLazyByteString personG
        "{\"name\":\"Peter\",\"age\":34,\"phone\":\"203-201-9923\"}"
        `shouldBe` Right (Person "Peter" 34 (Just "203-201-9923") Nothing)

      jsonGFromLazyByteString personG
        "{\"name\":\"Peter\",\"age\":34}"
        `shouldBe` Right (Person "Peter" 34 Nothing Nothing)

    it "should be able to decode a tuple" do
      let grm = arrayG "tuple" $ Two anyG anyG

      jsonGToLazyByteString grm (1 :: Int, "String" :: String)
        `shouldBe` "[1,\"String\"]"
      jsonGFromLazyByteString grm "[1,\"Hello\"]"
        `shouldBe` Right (1,"Hello")
      jsonGFromLazyByteString grm "[1,\"Hello\",2]"
        `shouldBe` Left "Error in $: too many items"
      jsonGFromLazyByteString grm "[1]"
        `shouldBe` Left "Error in $: too few items"




