{-
Module      :  Control.Grammar
Copyright   :  (c) Christian Gram Kalhauge 2020
License     :  BSD3
Maintainer  :  christian@kalhauge.dk

This module contains grammars.

In contrast to [boomerang], this library tries
* to make the grammar interpretable
* to make sum-typing efficient.

-}
module Control.Grammar
  ( module Control.Grammar.Prim
  , module Control.Grammar.Json
  , module Control.Grammar.Limits
  ) where

import Control.Grammar.Prim
import Control.Grammar.Json
import Control.Grammar.Limits
