module Days.D17 where

open import Data.String as Str
open import Data.Nat as N
open import Data.Nat.Properties using (<-strictTotalOrder ; ≤-decTotalOrder)
open import Data.Nat.Show as NS
import Data.Tree.AVL.Map
open Data.Tree.AVL.Map <-strictTotalOrder renaming (toList to mapToList; map to mapMap; foldr to mapFoldr; fromList to mapFromList; lookup to mapLookup; insert to mapInsert)
open import Data.Char as C
open import Function
open import Data.Product
open import Data.Maybe as M renaming (_>>=_ to _M>>=_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Bool
open import Data.List as L
open import Data.List.Effectful as LE
open import Effect.Monad
open import Data.Maybe.Effectful as ME
open import Data.Unit
open import Data.List.Sort

data Instr : Set where
  ADV BXL BST JNZ BXC OUT BDV CDV : Instr

record ST : Set where
  field
    regA : ℕ
    regB : ℕ
    regC : ℕ
    ptr : ℕ
    out : List ℕ

toInstr : ℕ → Instr
toInstr = λ where
  0 → ADV
  1 → BXL
  2 → BST
  3 → JNZ
  4 → BXC
  5 → OUT
  6 → BDV
  7 → CDV
  _ → OUT

combo : ℕ → ST → ℕ
combo 4 st = ST.regA st
combo 5 st = ST.regB st
combo 6 st = ST.regC st
combo n _ = n

doDiv : ℕ → ℕ → ℕ
doDiv n 0 = n
doDiv n (suc d) = doDiv ( n / 2) d

odd : ℕ → Bool
odd x = ⌊ ∣ ((x / 2) * 2) - x ∣′ N.≟ 1 ⌋

{-# NON_TERMINATING #-}
xor : ℕ → ℕ → ℕ
xor = go 1 where
  go : ℕ → ℕ → ℕ → ℕ
  go x 0 b = b * x
  go x a 0 = a * x
  go x a b =
    let oddA = odd a
        oddB = odd b
    in if (oddA ∧ oddB) ∨ ((not oddA) ∧ (not oddB))
        then go (2 * x) (a / 2) (b / 2)
        else 1 * x + go (2 * x) (a / 2) (b / 2)

{-# NON_TERMINATING #-}
band : ℕ → ℕ → ℕ
band = go 1 where
  go : ℕ → ℕ → ℕ → ℕ
  go x 0 b = 0
  go x a 0 = 0
  go x a b =
    let oddA = odd a
        oddB = odd b
    in if (oddA ∧ oddB)
        then x + go (2 * x) (a / 2) (b / 2)
        else go (2 * x) (a / 2) (b / 2)

runOp : Instr → ℕ → ST → ST
runOp i o st = case i of λ where
  ADV → record st { regA = doDiv (ST.regA st) (combo o st) ; ptr = ST.ptr st + 2 }
  BXL → record st { regB = xor (ST.regB st) o ; ptr = ST.ptr st + 2 }
  BST → record st { regB = band (combo o st) 7 ; ptr = ST.ptr st + 2 }
  JNZ → if ⌊ ST.regA st N.≟ 0 ⌋
          then st
          else record st { ptr = o }
  BXC → record st { regB = xor (ST.regB st) (ST.regC st) ; ptr = ST.ptr st + 2}
  OUT → record st { out = band (combo o st) 7 ∷ ST.out st ; ptr = ST.ptr st + 2 }
  BDV → record st { regB = doDiv (ST.regA st) (combo o st) ; ptr = ST.ptr st + 2 }
  CDV → record st { regC = doDiv (ST.regA st) (combo o st) ; ptr = ST.ptr st + 2 }

stout : ST → String
stout st = Str.concat ∘ L.intersperse "," ∘ L.map NS.show $ L.reverse (ST.out st)

parsePgrm : String → List ℕ
parsePgrm = mapMaybe (readMaybe 10) ∘ Str.wordsByᵇ (C._== ',') ∘ M.fromMaybe "" ∘ L.last ∘ words

parseReg : String → ℕ
parseReg = maybe (M.fromMaybe 0) 0 ∘ M.map (readMaybe 10) ∘ L.last ∘ words

{-# NON_TERMINATING #-}
runPgrm : List ℕ → ST → ST
runPgrm pgrm = go 0 pgrm
  where
  go : ℕ → List ℕ → ST → ST
  go off xs st =
    if ⌊ ST.ptr st N.<? off ⌋
    then go 0 pgrm st
    else case L.drop ∣ ST.ptr st - off ∣ xs of λ where
      (i ∷ o ∷ rest) → go (off + 2) rest (runOp (toInstr i) o st)
      _ → st

partA : String → String
partA inp = case lines inp of λ where
  (ra ∷ rb ∷ rc ∷ _ ∷ p ∷ []) →
    let st = record { regA = parseReg ra ; regB = parseReg rb ; regC = parseReg rc ; ptr = 0 ; out = [] }
        r = runPgrm (parsePgrm p) st
    in stout r
  _ → "oops"

{-# NON_TERMINATING #-}
runPgrm' : List ℕ → ST → ST
runPgrm' pgrm = go 0 pgrm
  where
  go : ℕ → List ℕ → ST → ST
  go off xs st =
    if ⌊ ST.ptr st N.<? off ⌋
    then st
    else case L.drop ∣ ST.ptr st - off ∣′ xs of λ where
      (i ∷ o ∷ rest) → go (off + 2) rest (runOp (toInstr i) o st)
      _ → st

inv : List ℕ → List ℕ → Map (List ℕ)
inv pg pAs = unionsWith (λ l ml → maybe (l L.++_) l ml) ∘ L.concat $
  L.applyUpTo
    (λ a → do
      pA ← pAs
      let nA = (pA * 8) + a
          r = runPgrm' pg (record { regA = nA ; regB = 0; regC = 0; ptr = 0 ; out = [] })
          h = M.fromMaybe 0 (L.head (ST.out r)) 
      [ singleton h [ nA ] ] )
    8
  where open RawMonad LE.monad

showMap : Map ℕ → String
showMap = unlines ∘ L.map (λ (k , v) → NS.show k Str.++ "->" Str.++ NS.show v) ∘ mapToList

partB : String → String
partB inp = case lines inp of λ where
  (ra ∷ rb ∷ rc ∷ _ ∷ p ∷ []) →
    let pg = parsePgrm p
        r = L.foldr (λ x acc →
              let m = inv pg acc
              in M.fromMaybe [] $ mapLookup m x
              ) [ 0 ] pg
    in maybe NS.show "no" ∘ L.head $ sort ≤-decTotalOrder r
  _ → "oops"