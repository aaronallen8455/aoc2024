module Days.D13 where

open import Data.String as Str
open import Data.Nat as N
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Nat.Show as NS
open import Data.Char as C
open import Function
open import Data.Product
open import Data.Maybe as M
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Bool
open import Data.List as L

div : ℕ → ℕ → Maybe ℕ
div a 0 = nothing
div a (suc b) = do
  0 ← just (a % suc b)
    where _ → nothing
  just (a / suc b)

nA : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Maybe ℕ
nA y1 y2 x1 x2 ry rx = do
  let t1 = ry * x2
  let t2 = y2 * rx
  let t3 = y1 * x2
  let t4 = y2 * x1
  let n1 = ⌊ t1 N.<? t2 ⌋
  let n2 = ⌊ t3 N.<? t4 ⌋
  true ← just ( (n1 ∧ n2) ∨ not (n1 ∨ n2))
    where false → nothing
  div ∣ t1 - t2 ∣′ ∣ t3 - t4 ∣′

sameSlope : ℕ → ℕ → ℕ → ℕ → Bool
sameSlope y1 y2 x1 x2 = false -- M.fromMaybe false $
  --(div y1 y2 >>= λ z → div x1 x2 >>= λ zz → just ⌊ z N.≟ zz ⌋ )
  --M.<∣>
  --(div y2 y1 >>= λ z → div x2 x1 >>= λ zz → just ⌊ z N.≟ zz ⌋ )

-- {-# NON_TERMINATING #-}
-- choose : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Maybe ℕ
-- choose ca cb a ax b bx r rx = go 0 nothing
  -- where
  -- go : ℕ → Maybe ℕ → Maybe ℕ
  -- go n mr = do
    -- true ← just ⌊ n N.≤? 100 ⌋
      -- where _ → mr
    -- let c = n * a
    -- true ← just ⌊ c N.≤? r ⌋
      -- where _ → mr
    -- let x = ∣ r - (n * a) ∣
    -- let md = div x b
    -- let cur = do
          -- d ← md
          -- true ← just ⌊ d * bx + n * ax N.≟ rx ⌋
            -- where _ → nothing
          -- just (d * cb + n * ca)
    -- case mr of λ where
      -- nothing → go (n + 1) cur
      -- (just old) → case cur of λ where
        -- nothing → go (n + 1) mr
        -- (just new) →
          -- if ⌊ new N.>? old ⌋
          -- then just old
          -- else go (n + 1) cur

cost : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Maybe ℕ
cost ca cb y1 y2 x1 x2 ry rx =
  if sameSlope y1 y2 x1 x2
  then nothing -- choose ca cb y1 y2 x1 x2 ry rx -- this doesn't happen :/
  else ( do
    pa ← nA y1 y2 x1 x2 ry rx
    pb ← div (∣ ry - (pa * y1) ∣′) y2
    just $ pa * ca + pb * cb
  )

parseN : String → Maybe ℕ
parseN = readMaybe 10 ∘ Str.fromList ∘ L.filterᵇ isDigit ∘ Str.toList

parse : List String → Maybe (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)
parse (l1 ∷ l2 ∷ l3 ∷ []) = do
  _ ∷ _ ∷ x1 ∷ y1 ∷ [] ← just (words l1)
    where _ → nothing
  _ ∷ _ ∷ x2 ∷ y2 ∷ [] ← just (words l2)
    where _ → nothing
  _ ∷ rx ∷ ry ∷ [] ← just (words l3)
    where _ → nothing
  x1n ← parseN x1
  x2n ← parseN x2
  y1n ← parseN y1
  y2n ← parseN y2
  rxn ← parseN rx
  ryn ← parseN ry
  just (y1n , y2n , x1n , x2n , ryn , rxn)
parse _ = nothing

partA : String → String
partA inp =
  let lns = mapMaybe parse $ L.linesByᵇ (Str._== "") (lines inp)
      rs = mapMaybe (λ (y1 , y2 , x1 , x2 , ry , rx) → cost 3 1 y1 y2 x1 x2 ry rx) lns
  in NS.show $ sum rs

partB : String → String
partB inp =
  let lns = mapMaybe parse $ L.linesByᵇ (Str._== "") (lines inp)
      rs = mapMaybe (λ (y1 , y2 , x1 , x2 , ry , rx) → cost 3 1 y1 y2 x1 x2 (ry + 10000000000000) (rx + 10000000000000)) lns
  in NS.show $ sum rs