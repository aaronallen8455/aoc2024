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
 
{-# NON_TERMINATING #-}
scc : G → List (Map ⊤)
scc g = mapFoldr go [] g where -- z nodes only
  collect : Node → Map ⊤ → Map ⊤
  descend : String → Map ⊤ → Map ⊤
  descend k acc =
    if member k acc
    then acc
    else case mapLookup g k of λ where
      nothing → acc
      (just n) → collect n (mapInsert k _ acc)
  collect (inj₁ (And , i1 , i2)) acc = descend i1 (descend i2 acc)
  collect (inj₁ (Or , i1 , i2)) acc = descend i1 (descend i2 acc)
  collect (inj₁ (Xor , i1 , i2)) acc = descend i1 (descend i2 acc)
  collect (inj₂ y) acc = acc

  go : String → Node → List (Map ⊤) → List (Map ⊤)
  go k n acc =
    if zNode k 
    then if any (member k) acc
         then acc
         else collect n (singleton k _) ∷ acc
    else acc

-- map from wires to the output wires that directly use that wire as an input
inv : G → Map (Map ⊤)
inv = unionsWith (λ m → maybe (union m) m) ∘ L.map proc ∘ mapToList where
  proc : String × Node → Map (Map ⊤)
  proc (k , inj₁ (And , i1 , i2)) = mapFromList $ (i1 , singleton k _) ∷ (i2 , singleton k _) ∷ (k , emptyMap) ∷ []
  proc (k , inj₁ (Or , i1 , i2)) = mapFromList $ (i1 , singleton k _) ∷ (i2 , singleton k _) ∷ (k , emptyMap) ∷ []
  proc (k , inj₁ (Xor , i1 , i2)) = mapFromList $ (i1 , singleton k _) ∷ (i2 , singleton k _) ∷ (k , emptyMap) ∷ []
  proc (k , inj₂ y) = singleton k emptyMap

noInp : G → List String
noInp = L.map proj₁ ∘ filterᵇ (λ (k , v) → ⌊ size v N.≟ 0 ⌋) ∘ mapToList ∘ inv

allWires : G → Map ⊤
allWires = unions ∘ L.map k ∘ mapToList where
  k : String × Node → Map ⊤
  k (s , inj₁ (And , i1 , i2)) = mapFromList $ (s , _) ∷ (i1 , _) ∷ (i2 , _) ∷ []
  k (s , inj₁ (Or , i1 , i2)) = mapFromList $ (s , _) ∷ (i1 , _) ∷ (i2 , _) ∷ []
  k (s , inj₁ (Xor , i1 , i2)) = mapFromList $ (s , _) ∷ (i1 , _) ∷ (i2 , _) ∷ []
  k (s , inj₂ y) = singleton s _

dead : G → List String
dead g =
  let ws = allWires g
  in L.map proj₁ ∘ mapToList $ mapFoldr (λ k _ → delete k) ws g

-- map from wires to set of transitive inputs for that wire. If a wire is in the transitive input of another, then they cannot be swapped.
--transInput : G → Map (Map ⊤) → Map (Map ⊤)
--transInput = {!   !}

{-# NON_TERMINATING #-}
allDesc : Map (Map ⊤) → String → List String
allDesc g s = case mapLookup g s of λ where
  nothing → []
  (just ds) → do
    d ← L.map proj₁ $ mapToList ds
    d ∷ allDesc g d
 where open RawMonad LE.monad

-- jdt is wrong. being used as an input to final XOR for bit 12 which should instead be
-- using the carry bit. No, it is supposed to be carry. other input to the OR is wrong?
-- rpv needs to be swapped with z11.
-- 

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