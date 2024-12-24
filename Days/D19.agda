{-# OPTIONS --sized-types #-}
module Days.D19 where

open import Data.String as Str
open import Data.Nat as N
open import Data.Nat.Properties using (<-strictTotalOrder ; ≤-decTotalOrder)
open import Data.Nat.Show as NS
import Data.Tree.AVL.Map
open Data.Tree.AVL.Map <-strictTotalOrder renaming (toList to mapToList; map to mapMap; foldr to mapFoldr; fromList to mapFromList; lookup to mapLookup; insert to mapInsert ; empty to emptyMap)
open import Data.Char as C
open import Data.Char.Properties as C
open import Function hiding (const)
open import Data.Product
open import Data.Maybe as M renaming (_>>=_ to _M>>=_)
open import Data.Maybe.Effectful as ME
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Bool
open import Data.List as L
open import Data.List.NonEmpty as NE using (toList)
open import Effect.Monad
open import Data.Unit
open import Effect.Monad
open import Effect.Monad.State as MS

open import Data.Trie C.<-strictTotalOrder as T
open import Data.Trie.NonEmpty C.<-strictTotalOrder as TE
open import Data.Tree.AVL.Value
open import Data.These
open import Data.Tree.AVL.NonEmpty C.<-strictTotalOrder as AN

Tss : Set
Tss = TE.Trie⁺ (const _ ⊤) _

compact : TE.Tries⁺ (const _ ⊤) _ → Tss
compact ts = TE.node (that ts)

parseTs : String → List (List Char)
parseTs = L.map (dropWhileᵇ (C._== ' ') ∘ Str.toList) ∘ Str.wordsByᵇ (C._== ',')

isPrefix : List Char → List Char → Maybe (List Char)
isPrefix [] bs = just bs
isPrefix _ [] = nothing
isPrefix (a ∷ as) (b ∷ bs) = if (a C.== b) then (isPrefix as bs) else nothing

check : Tss → List Char → Bool
check full = go [ full ] where

  prog : Char → Tss → Maybe (Bool × Maybe Tss)
  prog c t = case TE.lookup t [ c ] of λ where
    (just (this tt)) → just ( true , nothing )
    (just (that x)) → just ( false , just (compact x))
    (just (these x x₁)) → just (true , just (compact x₁))
    nothing → nothing

  go : List Tss → List Char → Bool
  go [] _ = false
  go _ [] = true
  go ts (c ∷ xs) =
    let tsp = L.mapMaybe (prog c) ts
        nt = L.mapMaybe proj₂ tsp
    in if L.any proj₁ tsp
        then go (full ∷ nt) xs
        else go nt xs

parseT : String → Maybe Tss
parseT = T.fromList ∘ L.map ((_, tt) ∘ L.dropWhileᵇ (C._== ' ') ∘ Str.toList) ∘ Str.wordsByᵇ (C._== ',')

partA : String → String
partA inp =
  let lns = L.wordsByᵇ (Str._== "") $ lines inp
      mtow = L.head lns M.>>= L.head M.>>= parseT
      req = L.map Str.toList ∘ M.fromMaybe [] $ L.last lns
  in case mtow of λ where
    (just tow) →
      let rs = L.map (check tow) req
      in NS.show (L.length $ L.filterᵇ id rs)
    nothing → "no"

{-# NON_TERMINATING #-}
count : Tss → Maybe Tss → ℕ → List Char → State (Map ℕ) ℕ
count full nothing n cs = do
  nothing ← gets (λ m → mapLookup m n)
    where (just v) → pure v
  r ← count full (just full) n cs
  modify (mapInsert n r)
  pure r
  where open RawMonad MS.monad
        open RawMonadState MS.monadState
count _ (just t) n (c ∷ []) = pure $ if exact c t then 1 else 0 where
  open RawMonad MS.monad
  exact : Char → Tss → Bool
  exact c t = case TE.lookup t [ c ] of λ where
    (just (this tt)) → true
    (just (that x)) → false
    (just (these x x₁)) → true
    nothing → false
count full (just t) n (c ∷ cs) =
  case TE.lookup t [ c ] of λ where
    (just (this tt)) → count full nothing (n + 1) cs
    (just (that x)) → count full (just $ compact x) (n + 1) cs
    (just (these tt x₁)) → do
      r1 ← count full nothing (n + 1) cs
      r2 ← count full (just $ compact x₁) (n + 1) cs
      pure $ r1 + r2
    nothing → pure 0
  where open RawMonad MS.monad
count _ _ _ [] = pure 0
  where open RawMonad MS.monad

partB : String → String
partB inp =
  let lns = L.wordsByᵇ (Str._== "") $ lines inp
      mtow = L.head lns M.>>= L.head M.>>= parseT
      req = L.map Str.toList ∘ M.fromMaybe [] $ L.last lns
  in case mtow of λ where
    (just tow) →
      let rs = L.map (λ x → evalState (count tow nothing 0 x) emptyMap) req
      in NS.show (sum rs)
    nothing → "no"