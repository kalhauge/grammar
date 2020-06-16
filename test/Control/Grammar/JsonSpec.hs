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
personG = objectG "Person" personKG

personKG :: JsonKeyG Person
personKG = defP PersonLim
  { onPersonName =
      "name"   |= textG
  , onPersonAge =
      "age"    |= intG
  , onPersonPhone =
      "phone"  ?= textG
  , onPersonParent =
      "parent" ?= personG
  }

data Personel
  = Boss Int Person
  | Employee Person
  | Plant
  deriving (Show, Eq)

$(makeCoLimit ''Personel)

personelG :: JsonG Personel
personelG = buildSum \PersonelCoLim {..} ->
  [ ifBoss =: objectG "Boss"
    (("golden" |= intG)
      <**> ("boss" |= personG)
    )
  , ifEmployee =: objectG "Employee"
    ( "employee" |= personG )
  , ifPlant =: objectG "Employee"
    ( "plant" |= nullG )
  ]

embPersonelG :: JsonG Personel
embPersonelG = objectG "Personel" $ buildSum \PersonelCoLim {..} ->
  [ ifBoss =* \s Two {..} ->
    [ s $ "dtype" |= val "boss"
    , onOne =: "golden" |= intG
    , onTwo =: personKG
    ]
  , ifEmployee =*! \s (One onEvery) ->
    [ s $ "dtype" |= val "employee"
    , onEvery =: personKG
    ]
  , ifPlant =: "dtype" |= val "plant"
  ]

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

      jsonGToLazyByteString personelG
        (Boss 10 (Person "Peter" 34 Nothing Nothing))
        `shouldBe` "{\"golden\":10,\"boss\":{\"name\":\"Peter\",\"age\":34}}"

      jsonGToLazyByteString embPersonelG
        (Employee (Person "Peter" 34 Nothing Nothing))
        `shouldBe` "{\"dtype\":\"employee\",\"name\":\"Peter\",\"age\":34}"

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

      jsonGFromLazyByteString personelG
        "{\"employee\":{\"name\":\"Peter\",\"age\":34}}"
        `shouldBe` Right (Employee (Person "Peter" 34 Nothing Nothing))

      jsonGFromLazyByteString embPersonelG
        "{\"dtype\":\"employee\",\"name\":\"Peter\",\"age\":34}"
        `shouldBe` Right (Employee (Person "Peter" 34 Nothing Nothing))

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




