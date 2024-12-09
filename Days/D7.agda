module Days.D7 where

open import Data.String hiding (concat; map)
open import Data.List
open import Data.Nat
open import Data.Nat.Show renaming (show to showNat)
open import Function
open import Data.Char
open import Data.Maybe hiding (map)
open import Data.Product hiding (map)
open import Data.Bool
open import Relation.Nullary.Decidable using (⌊_⌋)

parseLn : String → Maybe (ℕ × List ℕ)
parseLn l with words l
... | (x ∷ xs) = do
  xn ← readMaybe 10 (fromList $ takeWhileᵇ isDigit $ toList x)
  just (xn , mapMaybe (readMaybe 10) xs)
... | [] = nothing

test : ℕ → List ℕ → Bool
test _ [] = false
test n (x ∷ xs) =
  let go acc a = concat $ map (λ z → z * a ∷ z + a ∷ []) acc
      ps = foldl go [ x ] xs
  in any (λ k → ⌊ k Data.Nat.≟ n ⌋) ps

partA : String → String
partA inp =
  let lns = mapMaybe parseLn $ lines inp
      rs = filterᵇ (λ ( x , xs ) → test x xs) lns
  in Data.Nat.Show.show $ sum $ map proj₁ rs

test2 : ℕ → List ℕ → Bool
test2 _ [] = false
test2 n (x ∷ xs) =
  let conc a b = Data.Maybe.fromMaybe 0 $ readMaybe 10 $ showNat a Data.String.++ showNat b
      go acc a = filterᵇ (λ k → ⌊ k Data.Nat.≤? n ⌋)
               $ concat $ map (λ z → z * a ∷ z + a ∷ conc z a ∷ []) acc
      ps = foldl go [ x ] xs
  in any (λ k → ⌊ k Data.Nat.≟ n ⌋) ps

partB : String → String
partB inp =
  let lns = mapMaybe parseLn $ lines inp
      rs = filterᵇ (λ ( x , xs ) → test2 x xs) lns
  in showNat $ sum $ map proj₁ rs