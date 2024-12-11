module Days.D8 where

open import Data.String as Str
import Data.Tree.AVL.Map
open import Data.Char
open import Data.Char.Properties using (<-strictTotalOrder)
open Data.Tree.AVL.Map <-strictTotalOrder renaming (foldr to mapFold)
open import Data.Nat as N
open import Data.Nat.Properties renaming (<-strictTotalOrder to natOrder)
open import Data.Nat.Show as NS
open import Data.Product
open import Data.List as L
open import Function
open import Data.Maybe as M
open import Data.Bool
open import Relation.Nullary.Decidable using (⌊_⌋)
import Data.Tree.AVL.Sets hiding (delete)
open Data.Tree.AVL.Sets natOrder renaming (fromList to setFromList; toList to setToList; size to setSize; union to setUnion; empty to emptySet)

Towers : Set
Towers = Map (List (ℕ × ℕ))

enum : ∀ {a : Set} → List a → List (ℕ × a)
enum xs = L.zip (upTo (L.length xs)) xs

mkTowers : List (ℕ × List (ℕ × Char)) → Towers
mkTowers xs = delete '.' $ L.foldr go empty xs
  where
  go : ℕ × List (ℕ × Char) → Towers → Towers
  go x acc = L.foldr (λ (col , c) → insertWith c (λ { nothing → [ (proj₁ x , col) ] ; (just ls) → (proj₁ x , col) ∷ ls } ) ) acc (proj₂ x)

antinode : ℕ → ℕ × ℕ → ℕ × ℕ → List (ℕ × ℕ)
antinode sz (r1 , c1) (r2 , c2) = maybe′ [_] [] a1 L.++ maybe′ [_] [] a2
  where
  grr =
    if ⌊ r1 N.<? r2 ⌋
    then ((r1 , c1) , (r2 , c2))
    else ((r2 , c2) , (r1 , c1))
  rr1 = proj₁ (proj₁ grr)
  cc1 = proj₂ (proj₁ grr)
  rr2 = proj₁ (proj₂ grr)
  cc2 = proj₂ (proj₂ grr)
  rise = ∣ r1 - r2 ∣
  run = ∣ c1 - c2 ∣
  rn1 =
    if ⌊ rr1 N.<? rise ⌋
    then nothing
    else just ∣ rr1 - rise ∣

  rn2 =
    if ⌊ rr2 + rise ≥? sz ⌋
    then nothing
    else just (rr2 + rise)

  cn1 =
    if ⌊ cc1 N.<? cc2 ⌋
    then if ⌊ cc1 N.<? run ⌋
         then nothing
         else just ∣ cc1 - run ∣
    else if ⌊ cc1 + run N.≥? sz ⌋
         then nothing
         else just (cc1 + run)

  cn2 =
    if ⌊ cc1 N.<? cc2 ⌋
    then if ⌊ cc2 + run N.≥? sz ⌋
         then nothing
         else just (cc2 + run)
    else if ⌊ cc2 N.<? run ⌋
         then nothing
         else just ∣ cc2 - run ∣

  a1 = do
    r ← rn1
    c ← cn1
    just (r , c)
  a2 = do
    r ← rn2
    c ← cn2
    just (r , c)

antinodes : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
antinodes _ [] = []
antinodes sz (x ∷ xs) = L.concat (L.map (antinode sz x) xs) L.++ antinodes sz xs

count : List (ℕ × ℕ) → ⟨Set⟩
count = setFromList ∘ L.map (λ (r , c) → r * 100000 + c)

partA : String → String
partA inp =
  let lns = enum ∘ L.map (enum ∘ Str.toList) $ lines inp
      tws = mkTowers lns
      sz = L.length lns
      r = setSize $ mapFold (λ _ xs acc → setUnion acc ( count (antinodes sz xs))) emptySet tws
  in NS.show r

{-# NON_TERMINATING #-}
until : (ℕ → Maybe ℕ) → (ℕ → Maybe ℕ) → ℕ × ℕ → List (ℕ × ℕ)
until fr fc (r , c) = (r , c) ∷ nxt
  where
  nxt = M.fromMaybe [] $ do
    nr ← fr r
    nc ← fc c
    just (until fr fc (nr , nc))

antinode' : ℕ → ℕ × ℕ → ℕ × ℕ → List (ℕ × ℕ)
antinode' sz (r1 , c1) (r2 , c2) = until rn1 cn1 (rr1 , cc1) L.++ until rn2 cn2 (rr2 , cc2)
  where
  grr =
    if ⌊ r1 N.<? r2 ⌋
    then ((r1 , c1) , (r2 , c2))
    else ((r2 , c2) , (r1 , c1))
  rr1 = proj₁ (proj₁ grr)
  cc1 = proj₂ (proj₁ grr)
  rr2 = proj₁ (proj₂ grr)
  cc2 = proj₂ (proj₂ grr)
  rise = ∣ r1 - r2 ∣
  run = ∣ c1 - c2 ∣
  rn1 rn2 cn1 cn2 : ℕ → Maybe ℕ
  rn1 z =
    if ⌊ z N.<? rise ⌋
    then nothing
    else just ∣ z - rise ∣

  rn2 z =
    if ⌊ z + rise ≥? sz ⌋
    then nothing
    else just (z + rise)

  cn1 z =
    if ⌊ cc1 N.<? cc2 ⌋
    then if ⌊ z N.<? run ⌋
         then nothing
         else just ∣ z - run ∣
    else if ⌊ z + run N.≥? sz ⌋
         then nothing
         else just (z + run)

  cn2 z =
    if ⌊ cc1 N.<? cc2 ⌋
    then if ⌊ z + run N.≥? sz ⌋
         then nothing
         else just (z + run)
    else if ⌊ z N.<? run ⌋
         then nothing
         else just ∣ z - run ∣

antinodes' : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
antinodes' _ [] = []
antinodes' sz (x ∷ xs) = L.concat (L.map (antinode' sz x) xs) L.++ antinodes' sz xs

partB : String → String
partB inp =
  let lns = enum ∘ L.map (enum ∘ Str.toList) $ lines inp
      tws = mkTowers lns
      sz = L.length lns
      r = setSize $ mapFold (λ _ xs acc → setUnion acc ( count (antinodes' sz xs))) emptySet tws
  in NS.show r