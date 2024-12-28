module Days.D23 where

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

Edges : Set
Edges = Map ⊤

Graph : Set
Graph = Map Edges

edge : String → Graph
edge = unions ∘ (λ { (a ∷ b ∷ []) → singleton a (singleton b _) ∷ singleton b (singleton a _) ∷ []
                   ; _ → [] }) ∘ Str.wordsByᵇ (C._== '-')

{-# NON_TERMINATING #-}
wcc : Graph → List Edges
wcc g = L.deduplicateᵇ same ∘ L.foldr go [] $ mapToList g where
  same : Edges → Edges → Bool
  same a b = ⌊ size a N.≟ size b ⌋ ∧ ⌊ size (union a b) N.≟ size b ⌋

  inter : Edges → Edges
  inter = intersections ∘ L.mapMaybe (λ (k , _) → M.map (mapInsert k _) $ mapLookup g k) ∘ mapToList

  collect : String → Edges → List Edges
  collect s e =
    mapFoldr
      (λ k _ acc →  
        if any (member k) acc
          then acc
          else maybe (λ x → let ne = inter $ intersection (mapInsert s _ e) (mapInsert k _ x)
                             in ne ∷ acc
                     ) acc (mapLookup g k)
      )
      []
      e

  go : String × Edges → List Edges → List Edges
  go (k , e) es = collect k e L.++ es

hasT : String → Bool
hasT = L.any (C._== 't') ∘ take 1 ∘ Str.toList

fac : ℕ → ℕ
fac zero = 1
fac s@(suc n) = s N.* fac n 

nCk : ℕ → ℕ → ℕ
nCk n k = if ⌊ n N.<? k ⌋ then 0 else
  let d = fac k N.* fac ∣ n - k ∣′
  in case d of λ where
      zero → 0
      d@(suc _) → fac n  N./ d

targets : List Edges → ℤ
targets = combos ∘ filterᵇ (λ g → ⌊ size g N.≥? 3 ⌋ ∧ any (hasT ∘ proj₁) (mapToList g))
  where
  open RawMonad LE.monad
  combos : List Edges → ℤ
  combos [] = + 0
  combos (es ∷ rest) =
    let ts = filterᵇ hasT ∘ L.map proj₁ $ mapToList es
        oT = L.map (intersection es) $ filterᵇ (λ g → any (λ k → member k g) ts) rest
        oTo = do
          x ∷ xs ← inits oT
            where [] → []
          y ← xs
          [ intersection x y ]
        nC e =
          let ti = L.length ∘ filterᵇ hasT ∘ L.map proj₁ $ mapToList e
          in ∣ nCk (size e) 3 - nCk ∣ size e - ti ∣′ 3 ∣′
        ol = sum $ L.map nC oT
    in (+ (nC es) - + ol) I.+ + (sum (L.map nC oTo)) I.+ combos rest 

showGraph : Graph → String
showGraph = unlines ∘ L.map (λ (k , e) → k Str.++ " -> " Str.++ unwords (L.map proj₁ $ mapToList e)) ∘ mapToList

partA : String → String
partA inp =
  let g = unionsWith (λ m → maybe (union m) m) ∘ L.map edge $ lines inp
      wccs = wcc g
      ts = targets wccs
  in IS.show ts

partB : String → String
partB inp =
  let g = unionsWith (λ m → maybe (union m) m) ∘ L.map edge $ lines inp
      wccs = wcc g
      r = L.foldr (λ x acc → if ⌊ proj₁ acc N.>? size x ⌋ then acc else ( size x , x )) (0 , emptyMap) wccs
  in Str.intersperse "," ∘ L.map proj₁ ∘ mapToList $ proj₂ r