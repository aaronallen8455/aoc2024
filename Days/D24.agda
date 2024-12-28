module Days.D24 where

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

{-# FOREIGN GHC
  import qualified Data.Bits as B
#-}

postulate
  xor    : ℕ → ℕ → ℕ
  shiftL : ℕ → ℕ → ℕ
  _&_ : ℕ → ℕ → ℕ
  _∣_ : ℕ → ℕ → ℕ
{-# COMPILE GHC xor    = B.xor #-}
{-# COMPILE GHC shiftL = (\ a b -> B.shiftL a (fromIntegral b)) #-}
{-# COMPILE GHC _&_ = (B..&.) #-}
{-# COMPILE GHC _∣_ = (B..|.) #-}

data Op : Set where
  And Or Xor : Op

Node : Set
Node = (Op × String × String) ⊎ ℕ 

G : Set
G = Map Node

parseOp : String → Op
parseOp = λ where
  "XOR" → Xor
  "AND" → And
  _ → Or

-- ntg XOR fgs -> mjb
parseLn : String → G
parseLn l = case words l of λ where
  (w ∷ c ∷ []) → singleton (Str.fromList ∘ L.reverse ∘ L.drop 1 ∘ L.reverse $ Str.toList w) (inj₂ $ M.fromMaybe 0 (readMaybe 10 c))
  (i1 ∷ op ∷ i2 ∷ _ ∷ o ∷ []) → singleton o (inj₁ $ parseOp op , i1 , i2)
  _ → emptyMap

{-# NON_TERMINATING #-}
out : G → (String → String) → String → State (Map ℕ) ℕ
out g s w = do
  nothing ← gets $ flip mapLookup w
    where (just r) → pure r
  r ← case mapLookup g (s w) of λ where
    (just (inj₁ (And , i1 , i2))) → do
      r1 ← out g s i1
      r2 ← out g s i2
      pure $ r1 & r2
    (just (inj₁ (Or , i1 , i2))) → do
      r1 ← out g s i1
      r2 ← out g s i2
      pure $ r1 ∣ r2
    (just (inj₁ (Xor , i1 , i2))) → do
      r1 ← out g s i1
      r2 ← out g s i2
      pure $ xor r1 r2
    (just (inj₂ y)) → pure y
    nothing → pure 0
  modify $ mapInsert w r
  pure r
  where open RawMonad MS.monad
        open RawMonadState MS.monadState

zNode : String → Bool
zNode = any (C._== 'z') ∘ L.take 1 ∘ Str.toList

getZs : G → List String
getZs = L.filterᵇ zNode ∘ L.map proj₁ ∘ mapToList

traverse : ∀ {a b s : Set} → (a → State s b) → List a → State s (List b)
traverse _ [] = pure []
  where open RawMonad MS.monad
traverse f (x ∷ xs) = do
  r ← f x
  rs ← traverse f xs
  pure $ r ∷ rs
  where open RawMonad MS.monad

partA : String → String
partA inp =
  let g = unions ∘ L.map parseLn $ lines inp
      zs = getZs g
      rs = evalState (traverse (out g id) zs) emptyMap
      r = sum $ L.zipWith shiftL rs (upTo $ L.length rs)
  in NS.show r

swapWire : String → String
swapWire = λ where
  "rpv" → "z11"
  "z11" → "rpv"
  "ctg" → "rpb"
  "rpb" → "ctg"
  "dvq" → "z38"
  "z38" → "dvq"
  "z31" → "dmh"
  "dmh" → "z31"
  x → x

-- ctg,dmh,dvq,rpb,rpv,z11,z31,z38

-- bad bits
-- 11 fixed
-- 15 fixed
-- 38 fixed
-- 31 fixed

partB : String → String
partB inp =
  let g = unions ∘ L.map parseLn $ lines inp
      zs = getZs g
      rs = evalState (traverse (out g swapWire) zs) emptyMap
      r = sum $ L.zipWith shiftL rs (upTo $ L.length rs)
  in NS.show r