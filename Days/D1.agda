module Days.D1 where

open import Data.String
open import Data.Maybe
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.List
open import Data.List.Sort
open import Data.Nat
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Nat.Show

splitLn : String → Maybe (ℕ × ℕ)
splitLn l with words l
... | (a ∷ b ∷ []) = do
        aN ← readMaybe 10 a
        bN ← readMaybe 10 b
        just ⟨ aN , bN ⟩
... | _ = nothing

partA : String → String
partA inp =
  let ⟨ l1 , l2 ⟩ = unzip (mapMaybe splitLn (lines inp))
      l1s = sort ≤-decTotalOrder l1
      l2s = sort ≤-decTotalOrder l2
      rs = sum (Data.List.zipWith ∣_-_∣ l1s l2s)
  in Data.Nat.Show.show rs
   
simScore : List ℕ → List ℕ → ℕ
simScore (x ∷ xs) ys =
  let yss = dropWhile (Data.Nat._<? x) ys
      ⟨ r , ysss ⟩ = span (Data.Nat._≟ x) yss
  in Data.List.length r * x + simScore xs ysss
simScore _ _ = 0
   
partB : String → String
partB inp =
  let ⟨ l1 , l2 ⟩ = unzip (mapMaybe splitLn (lines inp))
      l1s = sort ≤-decTotalOrder l1
      l2s = sort ≤-decTotalOrder l2
  in Data.Nat.Show.show (simScore l1s l2s)
