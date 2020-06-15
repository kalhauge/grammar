{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-
Module      :  Control.Grammar.TH
Copyright   :  (c) Christian Gram Kalhauge 2020
License     :  BSD3
Maintainer  :  christian@kalhauge.dk

This module contains grammars.
-}
module Control.Grammar.TH where

-- base
import Control.Applicative
import Control.Monad
import Data.Char
import Data.Functor
import Data.Functor.Compose
import Data.Foldable
import Data.Functor.Contravariant
import Data.Functor.Identity

-- adjunctions
import Data.Functor.Contravariant.Rep

-- template-haskell
import Language.Haskell.TH

-- grammar
import Control.Grammar.Limits
import Control.Grammar.Builder

makeLimit :: Name -> DecsQ
makeLimit ty = do
  t <- reify ty
  case t of
    TyConI (DataD _ dn tp mk cn _) -> do
      fmap concat . forM cn $ \case
        RecC n vt -> do
          let nsf = NatSimpleForm
                { nsfName = limName
                , nsfType1 = limType1
                , nsfRecords = [  limOnName n | (n, _, t)  <- vt ]
                }
          sequence
            [ mkData n vt
            , mkHasLimit n vt
            , mkNatTransformable nsf
            , mkNatTraversable nsf
            , mkNatComposable nsf
            , mkNatFoldable nsf
            , mkAccessible nsf
            ]
        where
          mkData cn vt = do
            f' <- newName "f"
            return $ DataD [] limName (tp ++ [PlainTV f']) mk
              [ RecC (mkName (nameBase cn ++ "Lim"))
                [ ( limOnName rn
                  , Bang NoSourceUnpackedness NoSourceStrictness
                  , AppT (VarT f') t
                  )
                | (rn, b, t) <- vt
                ]
              ] []
          mkHasLimit cn vt = do
            l <- newName "l"
            b <- newName "b"
            return $ InstanceD Nothing [] (AppT (ConT ''HasLimit) (ConT dn))
              [ TySynInstD (TySynEqn Nothing (AppT (ConT ''Limit) (ConT dn)) limType1)
              , FunD 'extract
                [ Clause
                  []
                  ( NormalB
                    $ RecConE (limConName cn)
                      [ ( limOnName n, VarE n)
                      | (n, _, _) <- vt
                      ]
                  )
                  []
                ]
              , FunD 'inject
                [ Clause
                  [ VarP l, VarP b]
                  ( NormalB
                    $ RecConE cn
                      [ ( n, (AppE (AppE (VarE (limOnName n)) (VarE l)) (VarE b)) )
                      | (n, _, _) <- vt
                      ]
                  )
                  []
                ]
              ]
          limOnName n = mkName ("on" ++ capitalize (nameBase n))
          limConName cn = mkName (nameBase cn ++ "Lim")
          limName = mkName (nameBase dn ++ "Lim")
          limType1 = ConT limName
    _ ->
      fail "expected type constructor"

 where
  capitalize (a:as) = toUpper a : as

makeCoLimit :: Name -> DecsQ
makeCoLimit ty = do
  t <- reify ty
  case t of
    TyConI (DataD _ dn tp mk cn _) -> do
      let nsf = NatSimpleForm
            { nsfName = colimName
            , nsfType1 = colimType1
            , nsfRecords = [ mkName ("if" ++ nameBase n) | NormalC n _  <- cn ]
            }
      sequence
        [ mkData cn
        , mkHasCoLimit cn
        , mkNatTransformable nsf
        , mkNatTraversable nsf
        , mkNatComposable nsf
        , mkNatFoldable nsf
        , mkAccessible nsf
        ]
      where
        mkData cns = do
          f' <- newName "f"
          return $ DataD [] colimName (tp ++ [PlainTV f']) mk
            [ RecC (colimName)
              [ ( colimIfName cn
                , Bang NoSourceUnpackedness NoSourceStrictness
                , case x of
                    []   -> AppT (VarT f') (VarT '())
                    (_,a):[] -> AppT (VarT f') a
                    _ -> error "not suported yet"
                )
              | NormalC cn x <- cns
              ]
            ] []

        mkHasCoLimit cns = do
          cl <- newName "cl"
          a <- newName "a"
          r <- newName "r"
          return $ InstanceD Nothing [] (AppT (ConT ''HasCoLimit) (ConT dn))
            [ TySynInstD (TySynEqn Nothing (AppT (ConT ''CoLimit) (ConT dn)) colimType1)
            , FunD 'interpret
              [ Clause
                [ VarP cl, VarP a]
                ( NormalB
                  $ CaseE (VarE a)
                    [ Match
                        (ConP cn [VarP r])
                        (NormalB (AppE
                          (AppE (VarE 'index) (AppE (VarE (colimIfName cn)) (VarE cl)))
                          (VarE r)))
                        []
                    | NormalC cn x <- cns
                    ]
                )
                []
              ]
            , FunD 'construct
              [ Clause
                []
                ( NormalB
                  $ RecConE colimName
                    [ ( colimIfName cn, (AppE (ConE 'Op) (ConE cn)) )
                    | NormalC cn t <- cns
                    ]
                )
                []
              ]
            ]


        colimIfName n = mkName ("if" ++ nameBase n)
        colimName = mkName (nameBase dn ++ "CoLim")
        colimType1 = ConT colimName


data NatSimpleForm = NatSimpleForm
  { nsfName :: Name
  , nsfType1 :: Type
  , nsfRecords :: [Name]
  }


mkNatFoldable :: NatSimpleForm -> Q Dec
mkNatFoldable NatSimpleForm {..} = do
  a <- newName "a"
  return $ InstanceD
    Nothing
    []
    (AppT (ConT ''NatFoldable) nsfType1)
    [ FunD
        'natfold
        [ Clause
            [VarP a]
            (NormalB $ foldl'
              (\a b -> InfixE (Just a) (VarE '(<>)) (Just b))
              (VarE 'mempty)
              [ AppE (VarE 'getConst) (AppE (VarE cn) (VarE a))
              | cn <- nsfRecords
              ]
            )
            []
        ]
    ]

mkNatTransformable NatSimpleForm {..} = do
  a <- newName "a"
  nat <- newName "nat"
  return $ InstanceD Nothing [] (AppT (ConT ''NatTransformable) nsfType1)
    [ FunD 'natmap
      [ Clause
        [ VarP nat, VarP a]
        ( NormalB
          $ RecConE nsfName
            [ ( cn
              , (AppE (VarE nat) (AppE (VarE cn) (VarE a)))
              )
            | cn <- nsfRecords
            ]
        )
        []
      ]
    ]

mkNatComposable NatSimpleForm {..} = do
  a <- newName "a"
  b <- newName "b"
  comp <- newName "comp"
  return $ InstanceD Nothing [] (AppT (ConT ''NatComposable) nsfType1)
    [ FunD 'natcomp
      [ Clause
        [ VarP comp, VarP a, VarP b ]
        ( NormalB
          $ RecConE nsfName
            [ ( cn
              , AppE (AppE (VarE comp) (AppE (VarE cn) (VarE a)))
                  (AppE (VarE cn) (VarE b))
              )
            | cn <- nsfRecords
            ]
        )
        []
      ]
    ]

mkNatTraversable NatSimpleForm {..} = do
  a <- newName "a"
  b <- newName "b"
  comp <- newName "comp"
  return $ InstanceD Nothing [] (AppT (ConT ''NatTraversable) nsfType1)
    [ FunD 'natseq
      [ Clause
          [VarP a]
          (NormalB $ foldl'
            (\a b -> InfixE (Just a) (VarE '(<*>)) (Just b))
            (AppE (VarE 'pure) (ConE nsfName))
            [ AppE (VarE 'getCompose) (AppE (VarE cn) (VarE a))
            | cn <- nsfRecords
            ]
          )
          []
      ]
    ]

mkAccessible NatSimpleForm {..} = do
  a <- newName "a"
  b <- newName "b"
  fn <- newName "fn"
  s <- newName "s"
  comp <- newName "comp"
  return $ InstanceD Nothing [] (AppT (ConT ''Accessible) nsfType1)
    [ FunD 'accessors
      [ Clause
        [ ]
        ( NormalB
          $ RecConE nsfName
            [ (cn
              , AppE (ConE 'Accessor)
              . LamE [VarP  fn, VarP s]
              $ AppE
                (AppE (VarE 'fmap)
                  (LamE [VarP (mkName "a")]
                    ( RecUpdE (VarE s)
                      [ (cn, VarE (mkName ("a"))) ]
                    )
                  )
                )
                (AppE (VarE fn) (AppE (VarE cn) (VarE s)))
              )
              | cn <- nsfRecords
            ]
        )
        []
      ]
    ]
