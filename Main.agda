{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --sized-types #-}

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
open import Days.D11 as D11
open import Days.D12 as D12
open import Days.D13 as D13
open import Days.D14 as D14
open import Days.D15 as D15
open import Days.D16 as D16
open import Days.D17 as D17
open import Days.D18 as D18
open import Days.D19 as D19
open import Days.D20 as D20
open import Days.D21 as D21
open import Days.D22 as D22
open import Days.D23 as D23

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
    ( "11" ∷ "a" ∷ [] ) → day "11" D11.partA
    ( "11" ∷ "b" ∷ [] ) → day "11" D11.partB
    ( "12" ∷ "a" ∷ [] ) → day "12" D12.partA
    ( "12" ∷ "b" ∷ [] ) → day "12" D12.partB
    ( "13" ∷ "a" ∷ [] ) → day "13" D13.partA
    ( "13" ∷ "b" ∷ [] ) → day "13" D13.partB
    ( "14" ∷ "a" ∷ [] ) → day "14" D14.partA
    ( "14" ∷ "b" ∷ [] ) → day "14" D14.partB
    ( "15" ∷ "a" ∷ [] ) → day "15" D15.partA
    ( "15" ∷ "b" ∷ [] ) → day "15" D15.partB
    ( "16" ∷ "a" ∷ [] ) → day "16" D16.partA
    ( "16" ∷ "b" ∷ [] ) → day "16" D16.partB
    ( "17" ∷ "a" ∷ [] ) → day "17" D17.partA
    ( "17" ∷ "b" ∷ [] ) → day "17" D17.partB
    ( "18" ∷ "a" ∷ [] ) → day "18" D18.partA
    ( "18" ∷ "b" ∷ [] ) → day "18" D18.partB
    ( "19" ∷ "a" ∷ [] ) → day "19" D19.partA
    ( "19" ∷ "b" ∷ [] ) → day "19" D19.partB
    ( "20" ∷ "a" ∷ [] ) → day "20" D20.partA
    ( "20" ∷ "b" ∷ [] ) → day "20" D20.partB
    ( "21" ∷ "a" ∷ [] ) → day "21" D21.partA
    ( "21" ∷ "b" ∷ [] ) → day "21" D21.partB
    ( "22" ∷ "a" ∷ [] ) → day "22" D22.partA
    ( "22" ∷ "b" ∷ [] ) → day "22" D22.partB
    ( "23" ∷ "a" ∷ [] ) → day "23" D23.partA
    ( "23" ∷ "b" ∷ [] ) → day "23" D23.partB
    _ → putStrLn "not found"