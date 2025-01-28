----------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Maintainer  :  Felix Klein
--
-- Prints the symboltable of a TSL specification.
--
-----------------------------------------------------------------------------

{-# LANGUAGE NamedFieldPuns #-}

-----------------------------------------------------------------------------

module Main
  ( main
  ) where

-----------------------------------------------------------------------------

import EncodingUtils (initEncoding)

import PrintUtils (Color(..), ColorIntensity(..), cPutOut, cPutOutLn)

import FileUtils (loadTSL)

import TSL (Specification(..), toCSV)

import Config (Configuration(..), parseArguments)

import Data.List.NonEmpty (NonEmpty(..))

import qualified Data.List.NonEmpty as NonEmpty (head, toList, zipWith)

import qualified Data.Functor as Functor (unzip)

import Data.List (isInfixOf, partition)

import Control.Monad (when)

-----------------------------------------------------------------------------

main
  :: IO ()

main = do
  initEncoding

  Configuration{input, fullTable, noPositions} <- parseArguments

  spec <- loadTSL input
  let
    table = toCSV $ symboltable spec
    (is,ts') = partition (isInfixOf "internal") es
    (h', es) = case lines table of
      [] -> error "empty symbol table"
      h':es -> (h', es)

    (h, ts, upd)
      | fullTable =
          (h', ts', if noPositions then rmSLast else id)
      | otherwise =
          let h'' :| ts'' = rmSpaces [] (h' :| ts')
          in (h'',ts'', if noPositions then rmLast . rmLast else rmLast)

  header $ upd h
  sep $ upd h
  mapM_ (entries . upd) ts

  when fullTable $ do
    sep $ upd h
    mapM_ (entries . upd) is

  where
    rmSpaces a xs =
      let
        (is, rs) = Functor.unzip $ break (== ';') <$> xs
        is'' = NonEmpty.toList is
        n = minimum $ map (length . takeWhile (== ' ') . reverse) is''
      in case NonEmpty.head rs of
        "" ->
          let
            is' =
              if n > 0
              then take (length (NonEmpty.head is) - n + 1) <$> is
              else is

          in
            foldl (NonEmpty.zipWith (\x y -> y ++ ';' : x)) is' a
        _  ->
          let
            is' =
              if n > 1
              then take (length (NonEmpty.head is) - n + 1) <$> is
              else is
            rmSemi (';':zs) = zs
            rmSemi zs = zs
          in
            rmSpaces (is' : a) $ rmSemi <$> rs

    rmLast xs = reverse
      $ case break (== ';') $ reverse xs of
          (_, ';':_:xr) -> xr
          (_, _       ) -> []

    rmSLast xs =
      let
        (l, xr) = case break (== ';') $ reverse xs of
          (l, ';':xr) -> (l, xr)
          (l, _     ) -> (l, [])
        yr = case break (== ';') xr of
          (_, ';':yr) -> yr
          (_, _     ) -> []
      in
        reverse $ l ++ ';' : yr

    header h = case span (/= ';') h of
      ([], [])     -> return ()
      (rs, [])     -> cPutOutLn Vivid Yellow rs
      (xs, ';':rs) -> cPutOut Vivid Yellow xs >> cPutOut Vivid White ";" >> header rs
      _            -> undefined

    sep h = cPutOutLn Vivid White $ map (\x -> if x == ';' then ';' else '-') h

    entries es = case span (/= ';') es of
      ([], [])     -> return ()
      (rs, [])     -> cPutOutLn Dull White rs
      (xs, ';':rs) -> cPutOut Dull White xs >> cPutOut Vivid White ";" >>
                     entries rs
      _            -> undefined

-----------------------------------------------------------------------------
