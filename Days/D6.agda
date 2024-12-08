module Days.D6 where

open import Data.String hiding (map; fromList)
open import Data.Product hiding (zip; map)
open import Function
open import Data.List hiding (lookup)
open import Data.Char
open import Data.Maybe hiding (zip; map)
open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Show
open import Data.Nat.Properties using (<-strictTotalOrder)
import Data.Tree.AVL.Map
open Data.Tree.AVL.Map <-strictTotalOrder renaming (toList to mapToList; map to mapMap; foldr to mapFoldr)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable using (⌊_⌋)

data Dir : Set where
  Up Down Left Right : Dir

eqDir : Dir → Dir → Bool
eqDir Up Up = true 
eqDir Down Down = true 
eqDir Left Left = true 
eqDir Right Right = true 
eqDir _ _ = false

data Cell : Set where
  Empty : Cell
  Block : Cell 
  Visited : Dir → Cell -- list?

eqCell : Cell → Cell → Bool
eqCell Empty Empty = true
eqCell Block Block = true
eqCell (Visited a) (Visited b) = eqDir a b
eqCell _ _ = false

Cols : Set
Cols = Map Cell

Rows : Set
Rows = Map Cols

toCell : Char → Cell
toCell '.' = Empty
toCell '#' = Block
toCell '^' = Visited Up
toCell _ = Empty

mkMap : List (List Cell) → Rows
mkMap [] = empty
mkMap xs@(x ∷ _) =
    fromList ∘ zip (upTo nrows)
    $ map (λ r → fromList (zip (upTo ncols) r)) xs
  where
  nrows = Data.List.length xs
  ncols = Data.List.length x

findStart : Rows → Maybe (ℕ × ℕ)
findStart = Data.List.head ∘ mapMaybe (λ ( ri , x ) → Data.List.head ∘ catMaybes $ mapMaybe (λ (ci , c) →
                  if (eqCell c (Visited Up)) then (just (just (ri , ci))) else nothing)
                  (mapToList x))
            ∘ mapToList

step : Dir → ℕ × ℕ → Maybe (ℕ × ℕ)
step d (r , c) with d
... | Up = if ⌊ r Data.Nat.≟ 0 ⌋ then nothing else (just (pred r , c))
... | Down = just (r + 1 , c)
... | Left = if ⌊ c Data.Nat.≟ 0 ⌋ then nothing else (just (r , pred c))
... | Right = just (r , c + 1)

turn : Dir → Dir
turn Up = Right
turn Right = Down
turn Down = Left
turn Left = Up

lookupCoord : ℕ × ℕ → Rows → Maybe Cell
lookupCoord (r , c) rows = do
  col ← lookup rows r
  lookup col c

setCell : ℕ × ℕ → Cell → Rows → Rows
setCell (r , c) cell rws with lookup rws r
... | nothing = rws
... | (just cls) = insert r (insert c cell cls) rws

{-# NON_TERMINATING #-}
move : Rows → Dir → ℕ × ℕ → Maybe (Rows × Dir × (ℕ × ℕ) × Bool)
move rs d coord with step d coord
... | nothing = nothing
... | (just (r , c)) = do
  cell ← lookupCoord (r , c) rs
  case cell of λ where
    Block → move rs (turn d) coord
    (Visited dir) →
      if eqDir d dir
        then just ( rs , d , (r , c) , true)
        else just ( setCell (r , c) (Visited d) rs , d , (r , c) , false)
    _ → just ( setCell (r , c) (Visited d) rs , d , (r , c) , false)

{-# NON_TERMINATING #-}
run' : Rows → Dir → ℕ × ℕ → Maybe (Rows × Dir × (ℕ × ℕ) × Bool)
run' rs d coord with move rs d coord
... | nothing = just (rs , d , coord , false)
... | x@(just (_ , _ , _ , true)) = x
... | (just (rs' , d' , coord' , false)) = run' rs' d' coord'

count : Rows → ℕ
count =
  let go _ v a = mapFoldr (λ {_ (Visited _) a → 1 + a ; _ _ a → a }) a v
  in mapFoldr go 0

partA : String → String
partA inp =
  let cells = map (λ l → map toCell $ Data.String.toList l) (lines inp)
      m = mkMap cells
      st = findStart m
      mr = st >>= run' m Up
  in case mr of λ where
      nothing → "oops"
      (just (r , _ , _)) → Data.Nat.Show.show (count r)

isVisited : Cell → Bool
isVisited (Visited _) = true
isVisited _ = false

visited : Rows → List (ℕ × ℕ)
visited = Data.List.concat ∘ map (λ ( ri , x ) → catMaybes $ mapMaybe (λ (ci , c) →
                  if (isVisited c) then (just (just (ri , ci))) else nothing)
                  (mapToList x))
            ∘ mapToList

eqCoord : ℕ × ℕ → ℕ × ℕ → Bool
eqCoord (r1 , c1) (r2 , c2) = ⌊ r1 Data.Nat.≟ r2 ⌋ ∧ ⌊ c1 Data.Nat.≟ c2 ⌋

checkLoop : Rows → ℕ × ℕ → ℕ × ℕ → Bool
checkLoop rs start c =
  case run' (setCell c Block rs) Up start of λ where
    (just (_ , _ , _ , true)) → true
    _ → false

showCoords : List (ℕ × ℕ) → String
showCoords [] = ""
showCoords ((r , c) ∷ xs) = "(" Data.String.++ (Data.Nat.Show.show r) Data.String.++ "," Data.String.++ (Data.Nat.Show.show c) Data.String.++ ")" Data.String.++ showCoords xs

partB : String → String
partB inp =
  let cells = map (λ l → map toCell $ Data.String.toList l) (lines inp)
      m = mkMap cells
      st = findStart m
      mr = st >>= run' m Up
  in case (mr , st) of λ where
      (just (r , _) , just st) →
        let vs = filterᵇ (not ∘ eqCoord st) $ visited r
            rs = filterᵇ (checkLoop m st) vs
        in Data.Nat.Show.show (Data.List.length rs)
      _ → "oops"