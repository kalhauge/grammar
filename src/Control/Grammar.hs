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
  , module Control.Grammar.Limits
  , module Control.Grammar.Combinators
  , module Control.Grammar.Builder
  ) where

import Control.Grammar.Prim
import Control.Grammar.Limits
import Control.Grammar.Combinators
import Control.Grammar.Builder
