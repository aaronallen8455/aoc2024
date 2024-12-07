module Days.D5 where

open import Data.String
open import Data.Product
open import Function
open import Data.List hiding (lookup)
open import Data.Char
open import Data.Maybe
open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Show
open import Data.Nat.Properties using (<-strictTotalOrder)
import Data.Tree.AVL
import Data.Tree.AVL.Value
open Data.Tree.AVL <-strictTotalOrder
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (¬_)

data K : ∀ (a : Set) → ℕ → Set₁ where
  MkK : ∀ {a : Set} {n : ℕ} → a → K a n

Map : Set₁
Map = Tree (MkValue (K (List ℕ)) (subst (K (List ℕ))))

parsePair : String → Maybe (ℕ × ℕ)
parsePair i = case spanᵇ isDigit (Data.String.toList i) of λ where
  ( a , '|' ∷ b ) → do
    an ← readMaybe 10 (Data.String.fromList a)
    bn ← readMaybe 10 (Data.String.fromList b)
    just ( an , bn )
  _ → nothing

checkOrder : Map → List ℕ → Bool
checkOrder _ [] = true
checkOrder m (x ∷ xs) =
  case lookup m x of λ where
    nothing → checkOrder m xs
    (just (MkK ys)) →
      if (any (λ y → any (λ x → ⌊ (x Data.Nat.≟ y) ⌋) xs) ys)
      then false
      else checkOrder m xs

pairsToMap : List (ℕ × ℕ) → Map
pairsToMap = Data.List.foldr go empty
  where
  go : ℕ × ℕ → Map → Map
  go (a , b) m = insertWith b (λ { nothing → MkK [ a ]; (just (MkK xs)) → MkK (a ∷ xs) }) m

parseInstr : String → List ℕ
parseInstr = mapMaybe (readMaybe 10) ∘ Data.String.wordsByᵇ (λ x -> ⌊ x Data.Char.≟ ',' ⌋)

mid : List ℕ → ℕ
mid xs = go xs xs
  where
  go : List ℕ → List ℕ → ℕ
  go (_ ∷ xs) (_ ∷ _ ∷ ys) = go xs ys
  go (x ∷ xs) _ = x
  go _ _ = 0

partA : String → String
partA inp =
  let lns = lines inp
      ( ps , instr ) = break (Data.String._≟ "") lns
      pairs = mapMaybe parsePair ps
      m = pairsToMap pairs
      r = filterᵇ (checkOrder m) (Data.List.map parseInstr (drop 1 instr))
  in Data.Nat.Show.show (sum (Data.List.map mid r))

{-# NON_TERMINATING  #-}
correct : Map → List ℕ → List ℕ
correct _ [] = []
correct m (x ∷ xs) =
  let deps = case lookup m x of λ where
        nothing → []
        (just (MkK ys)) → ys
      ( b , g ) = partitionᵇ (λ y → is-just (find (Data.Nat._≟ y) deps)) xs
  in (correct m b) Data.List.++ x ∷ (correct m g)

partB : String → String
partB inp =
  let lns = lines inp
      ( ps , instr ) = break (Data.String._≟ "") lns
      pairs = mapMaybe parsePair ps
      m = pairsToMap pairs
      r = Data.List.map (correct m)
        $ filterᵇ (not ∘ checkOrder m) (Data.List.map parseInstr (drop 1 instr))
  in Data.Nat.Show.show (sum (Data.List.map mid r))