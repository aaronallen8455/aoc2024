{-# OPTIONS --guardedness #-}

module Main where

open import IO
open import Data.List hiding (_++_)
open import Data.String.Base
open import Function.Base
open import System.Environment

open import Days.D1 as D1
open import Days.D2 as D2

day : String → (String → String) → IO _
day inpFile solve = do
  inp ← readFiniteFile ("input/" ++ inpFile)
  putStrLn (solve inp)

main : Main
main = run $ do
  args ← getArgs
  case args of λ where
    ( "1" ∷ "a" ∷ [] ) → day "1" D1.partA
    ( "1" ∷ "b" ∷ [] ) → day "1" D1.partB
    ( "2" ∷ "a" ∷ [] ) → day "2" D2.partA
    ( "2" ∷ "b" ∷ [] ) → day "2" D2.partB
    _ → putStrLn "not found"