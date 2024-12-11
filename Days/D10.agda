module Days.D10 where

open import Data.String as Str
open import Data.Nat as N
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Nat.Show as NS
import Data.Tree.AVL.Map
open Data.Tree.AVL.Map <-strictTotalOrder renaming (toList to mapToList; map to mapMap; foldr to mapFoldr; fromList to mapFromList; lookup to mapLookup; insert to mapInsert)
import Data.Tree.AVL.Sets renaming (empty to emptySet; singleton to singletonSet; unions to setUnions; insert to setInsert; size to setSize; fromList to setFromList; toList to setToList)
open Data.Tree.AVL.Sets <-strictTotalOrder
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List as L
open import Function
open import Data.Product
open import Data.Bool
open import Data.Maybe as M renaming (_>>=_ to _M>>=_)
open import Effect.Monad
open import Effect.Monad.State

Top : Set
Top = Map (Map ℕ)

DP : Set
DP = Map (Map ⟨Set⟩)

mkTop : List (List ℕ) → Top
mkTop [] = empty
mkTop xs@(x ∷ _) =
    mapFromList ∘ L.zip (upTo nrows)
    $ L.map (λ r → mapFromList (L.zip (upTo ncols) r)) xs
  where
  nrows = L.length xs
  ncols = L.length x

findTrailHeads : Top → List (ℕ × ℕ)
findTrailHeads = L.concat ∘ L.map (λ ( ri , x ) → mapMaybe (λ (ci , c) →
                  if ⌊ c N.≟ 0 ⌋ then (just (ri , ci)) else nothing)
                  (mapToList x))
            ∘ mapToList

lookupC : ℕ × ℕ → Top → Maybe ℕ
lookupC (r , c) dp = mapLookup dp r M.>>= λ m → mapLookup m c

lookupDP : ℕ × ℕ → DP → Maybe ⟨Set⟩
lookupDP (r , c) dp = mapLookup dp r M.>>= λ m → mapLookup m c

for : ∀ {a b s : Set} → List a → (a → State s b) → State s (List b)
for [] _ = pure []
  where open RawMonad monad
for (x ∷ xs) f = do
  b ← f x
  bs ← for xs f
  pure $ b ∷ bs
  where open RawMonad monad

minus1 : ℕ → ℕ
minus1 0 = 0
minus1 a = ∣ a - 1 ∣

cands : Top → ℕ × ℕ → List (ℕ × ℕ)
cands top coord@(r , c) with lookupC coord top
... | nothing = []
... | (just h) = filterᵇ good $ (minus1 r , c) ∷ (r + 1 , c) ∷ (r , minus1 c) ∷ (r , c + 1) ∷ []
  where
  good : ℕ × ℕ → Bool
  good ca with lookupC ca top
  ... | nothing = false
  ... | (just hh) =
          ⌊ ∣ r - proj₁ ca ∣ + ∣ c - proj₂ ca ∣ N.>? 0 ⌋
          ∧ ⌊ hh N.>? h ⌋
          ∧ ⌊ ∣ hh - h ∣ N.≟ 1 ⌋

insertDP : ℕ × ℕ → ⟨Set⟩ → DP → DP
insertDP (r , c) x dp = insertWith r (λ { nothing → singleton c x ; (just cur) → mapInsert c x cur }) dp

{-# NON_TERMINATING #-}
explore : Top → ℕ × ℕ → State DP ⟨Set⟩
explore top coord@(r , c) = do
  just h ← pure $ lookupC coord top
    where nothing → pure empty
  nothing ← gets (lookupDP coord)
    where (just n) → pure n
  rs ← for (cands top coord) (explore top)
  let s = setUnions rs
      ss = if ⌊ h N.≟ 9 ⌋ then setInsert (r * 10000000 + c) s else s
  modify $ insertDP coord ss
  pure ss
  where open RawMonad monad
        open RawMonadState monadState

partA : String → String
partA inp =
  let top = mkTop $ L.map (L.mapMaybe (readMaybe 10 ∘ Str.fromChar) ∘ Str.toList) $ Str.lines inp
      r = evalState (for (findTrailHeads top) (explore top)) empty
  in NS.show ∘ sum $ L.map setSize r

insertC : ℕ × ℕ → ℕ → Top → Top
insertC (r , c) x dp = insertWith r (λ { nothing → singleton c x ; (just cur) → mapInsert c x cur }) dp

{-# NON_TERMINATING #-}
explore' : Top → ℕ × ℕ → State Top ℕ
explore' top coord@(r , c) = do
  nothing ← gets (lookupC coord)
    where (just n) → pure n
  just h ← pure $ lookupC coord top
    where nothing → pure 0
  rs ← for (cands top coord) (explore' top)
  let s = sum rs
      ss = if ⌊ h N.≟ 9 ⌋ then 1 else s
  modify $ insertC coord ss
  pure ss
  where open RawMonad monad
        open RawMonadState monadState

partB : String → String
partB inp =
  let top = mkTop $ L.map (L.mapMaybe (readMaybe 10 ∘ Str.fromChar) ∘ Str.toList) $ Str.lines inp
      r = evalState (for (findTrailHeads top) (explore' top)) empty
  in NS.show $ sum r