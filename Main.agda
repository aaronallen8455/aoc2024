{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

module Main where

open import IO
open import Data.List hiding (_++_)
open import Data.String.Base
open import Function.Base
open import System.Environment

open import Days.D1 as D1
open import Days.D2 as D2
open import Days.D3 as D3
open import Days.D4 as D4
open import Days.D5 as D5
open import Days.D6 as D6
open import Days.D7 as D7
open import Days.D8 as D8
open import Days.D9 as D9
open import Days.D10 as D10

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
    ( "3" ∷ "a" ∷ [] ) → day "3" D3.partA
    ( "3" ∷ "b" ∷ [] ) → day "3" D3.partB
    ( "4" ∷ "a" ∷ [] ) → day "4" D4.partA
    ( "4" ∷ "b" ∷ [] ) → day "4" D4.partB
    ( "5" ∷ "a" ∷ [] ) → day "5" D5.partA
    ( "5" ∷ "b" ∷ [] ) → day "5" D5.partB
    ( "6" ∷ "a" ∷ [] ) → day "6" D6.partA
    ( "6" ∷ "b" ∷ [] ) → day "6" D6.partB
    ( "7" ∷ "a" ∷ [] ) → day "7" D7.partA
    ( "7" ∷ "b" ∷ [] ) → day "7" D7.partB
    ( "8" ∷ "a" ∷ [] ) → day "8" D8.partA
    ( "8" ∷ "b" ∷ [] ) → day "8" D8.partB
    ( "9" ∷ "a" ∷ [] ) → day "9" D9.partA
    ( "9" ∷ "b" ∷ [] ) → day "9" D9.partB
    ( "10" ∷ "a" ∷ [] ) → day "10" D10.partA
    ( "10" ∷ "b" ∷ [] ) → day "10" D10.partB
    _ → putStrLn "not found"