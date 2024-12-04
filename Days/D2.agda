module Days.D2 where

open import Data.String using (String; lines; words)
open import Data.List using (mapMaybe; map; List; all; drop; zip; reverse; length; filterᵇ; foldl; _∷_; inits; tails; _++_; any)
open import Data.Nat
open import Data.Nat.Show
open import Data.Bool
open import Function
open import Data.Product using (_,_; _×_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Maybe hiding (zip; map)

isSafe : List ℕ → Bool
isSafe xs =
  let z i = all (λ (a , b) → ⌊ ∣ a - b ∣ Data.Nat.<? 4 ⌋ ∧ ⌊ a Data.Nat.<? b ⌋) (zip i (drop 1 i))
  in z xs ∨ z (reverse xs)

partA : String → String
partA inp =
  let lns = map (mapMaybe (readMaybe 10) ∘ words) (lines inp)
  in show (length (filterᵇ isSafe lns))

splits : List ℕ → List (List ℕ)
splits xs = xs ∷
  (Data.List.zipWith _++_ (inits xs) (drop 1 (tails xs)))

partB : String → String
partB inp =
  let lns = map (mapMaybe (readMaybe 10) ∘ words) (lines inp)
  in show (length (filterᵇ (any isSafe ∘ splits) lns))