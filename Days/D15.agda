module Days.D15 where

open import Data.String as Str
open import Data.Nat as N
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Nat.Show as NS
import Data.Tree.AVL.Map
open Data.Tree.AVL.Map <-strictTotalOrder renaming (toList to mapToList; map to mapMap; foldr to mapFoldr; fromList to mapFromList; lookup to mapLookup; insert to mapInsert)
open import Data.Char as C
open import Function
open import Data.Product
open import Data.Maybe as M
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Bool
open import Data.List as L

G : Set
G = Map (Map Char)

mkG : List (List Char) → G
mkG [] = empty
mkG xs@(x ∷ _) =
    mapFromList ∘ L.zip (upTo nrows)
    $ L.map (λ r → mapFromList (L.zip (upTo ncols) r)) xs
  where
  nrows = L.length xs
  ncols = L.length x

lookupC : ∀ {a : Set} → ℕ × ℕ → Map (Map a) → Maybe a
lookupC (r , c) dp = mapLookup dp r M.>>= λ m → mapLookup m c

insertC : ∀ {a : Set} → ℕ × ℕ → a → Map (Map a) → Map (Map a)
insertC (r , c) a = insertWith r (λ { nothing → singleton c a ; (just k) → mapInsert c a k })

findRobot : G → Maybe (ℕ × ℕ)
findRobot = L.head ∘ L.concat ∘ L.map (λ ( ri , x ) → mapMaybe (λ (ci , c) →
                  if c C.== '@' then (just (ri , ci)) else nothing)
                  (mapToList x))
            ∘ mapToList

moveC : ℕ × ℕ → Char → ℕ × ℕ
moveC coord@(r , c) = λ where
  '>' → (r , c + 1)
  '<' → (r , pred c)
  '^' → (pred r , c)
  'v' → (r + 1 , c)
  _ → coord

{-# NON_TERMINATING #-}
shift : ℕ × ℕ → Bool → Bool → Bool → (ℕ × ℕ → ℕ × ℕ) → Char → G → Maybe G
shift coord@(r , c) vert noLeft noRight nxt pc g = lookupC coord g >>= λ where
  'O' → shift (nxt coord) vert noLeft noRight nxt 'O' (insertC coord pc g)
  '#' → nothing
  '[' →
    let nG = insertC coord pc g
    in if vert
    then (
      shift (nxt coord) true false true nxt '[' nG >>= λ nnG →
      if noRight
      then just nnG
      else shift (r , c + 1) true true false nxt '.' nnG
    )
    else shift (nxt coord) vert false false nxt '[' nG
  ']' →
    let nG = insertC coord pc g
    in if vert
    then (
      shift (nxt coord) true true false nxt ']' nG >>= λ nnG →
      if noLeft
      then just nnG
      else shift (r , pred c) true false true nxt '.' nnG
    )
    else shift (nxt coord) vert false false nxt ']' nG
  _ → just $ insertC coord pc g

move : G × (ℕ × ℕ) → Char → G × (ℕ × ℕ)
move (g , coord) dir =
  let newC = moveC coord dir
      vert = (dir C.== '^') ∨ (dir C.== 'v')
  in case lookupC newC g of λ where
      (just 'O') → case shift newC vert false false (λ c → moveC c dir) '@' g of λ where
        nothing → (g , coord)
        (just newG) → (insertC coord '.' newG , newC)
      (just '[') → case shift newC vert false false (λ c → moveC c dir) '@' g of λ where
        nothing → (g , coord)
        (just newG) → (insertC coord '.' newG , newC)
      (just ']') → case shift newC vert false false (λ c → moveC c dir) '@' g of λ where
        nothing → (g , coord)
        (just newG) → (insertC coord '.' newG , newC)
      (just '#') → (g , coord)
      _ → (insertC newC '@' (insertC coord '.' g) , newC)

coords : G → ℕ
coords g = sum ∘ L.concat ∘ L.map (λ (r , cols) → L.mapMaybe (λ (c , cell) →
  if (cell C.== 'O') ∨ (cell C.== '[') then just (100 * r + c) else nothing) $ mapToList cols) $ mapToList g

partA : String → String
partA inp =
  let lns = L.map (L.map Str.toList) ∘ L.linesByᵇ (Str._== "") $ lines inp
      g : G
      g = maybe mkG empty (L.head lns)
      instr : List Char
      instr = maybe L.concat [] $ L.last lns
      rob = M.fromMaybe (0 , 0) $ findRobot g
      gr = L.foldl move (g , rob) instr
  in NS.show $ coords $ proj₁ gr

widen : List Char → List Char
widen = L.concat ∘ L.map λ where
  'O' → '[' ∷ ']' ∷ []
  '@' → '@' ∷ '.' ∷ []
  c → c ∷ c ∷ []

showG : G → String
showG g = unlines ∘ L.map (λ r → Str.fromList $ L.map (λ c → M.fromMaybe ' ' $ lookupC (r , c) g) $ L.upTo 30) $ L.upTo 16

partB : String → String
partB inp =
  let lns = L.map (L.map Str.toList) ∘ L.linesByᵇ (Str._== "") $ lines inp
      g : G
      g = maybe (mkG ∘ L.map widen) empty (L.head lns)
      instr : List Char
      instr = maybe L.concat [] $ L.last lns
      rob = M.fromMaybe (0 , 0) $ findRobot g
      gr = L.foldl move (g , rob) instr
  in NS.show $ coords $ proj₁ gr