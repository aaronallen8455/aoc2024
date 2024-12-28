module Days.D25 where

open import Data.String as Str
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Nat as N
open import Data.Nat.Properties using (<-strictTotalOrder ; ≤-decTotalOrder)
open import Data.Integer as I
open import Data.Integer.Show as IS
open import Data.Nat.Show as NS
import Data.Tree.AVL.Map
open Data.Tree.AVL.Map <-strictTotalOrder-≈ renaming (toList to mapToList; map to mapMap; foldr to mapFoldr; fromList to mapFromList; lookup to mapLookup; insert to mapInsert ; empty to emptyMap)
open import Data.Char as C
open import Function
open import Data.Product
open import Data.Sum
open import Data.Maybe as M renaming (_>>=_ to _M>>=_)
open import Data.Maybe.Effectful as ME
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Bool
open import Data.List as L
open import Data.List.Effectful as LE
open import Effect.Monad
open import Data.Unit
open import Effect.Monad
open import Effect.Monad.State as MS

Doors : Set
Doors = Map ℕ

isDoor : List String → Bool
isDoor = any (any (C._== '#') ∘ L.take 1 ∘ Str.toList) ∘ take 1

transpose : ∀ {a : Set} → List (List a) → List (List a)
transpose [] = []
transpose (x ∷ []) = L.map [_] x
transpose (x ∷ xs) = L.zipWith _∷_ x $ transpose xs

cols : List String → List ℕ
cols = L.map (L.length ∘ L.filterᵇ (C._== '#')) ∘ transpose ∘ L.map Str.toList

keyFits : List ℕ → List ℕ → Bool
keyFits xs = and ∘ L.zipWith (λ a b → ⌊ a N.+ b N.≤? 7 ⌋) xs

partA : String → String
partA inp =
  let lns = L.partitionᵇ isDoor ∘ L.wordsByᵇ (Str._== "") $ lines inp
      r = sum ∘ L.map (λ k → L.length ∘ filterᵇ (keyFits k) $ L.map cols $ proj₁ lns) ∘ L.map cols $ proj₂ lns
  in NS.show r