module Days.D22 where

open import Data.String as Str
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Integer as I
open import Data.Integer.Show as IS
open import Data.Nat as N
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

{-# FOREIGN GHC
  import qualified Data.Bits as B
#-}

postulate
  xor    : ℕ → ℕ → ℕ
  shiftL : ℕ → ℕ → ℕ
  shiftR : ℕ → ℕ → ℕ
  _&_ : ℕ → ℕ → ℕ
{-# COMPILE GHC xor    = B.xor #-}
{-# COMPILE GHC shiftL = (\ a b -> B.shiftL a (fromIntegral b)) #-}
{-# COMPILE GHC shiftR = (\ a b -> B.shiftR a (fromIntegral b)) #-}
{-# COMPILE GHC _&_ = (B..&.) #-}

prune : ℕ → ℕ
prune = _& N.pred 16777216

nxt : ℕ → ℕ
nxt n =
  let r1 = shiftL n 6
      r2 = xor r1 n
      r3 = prune r2

      r4 = shiftR r3 5
      r5 = xor r3 r4
      r6 = prune r5

      r7 = shiftL r6 11
      r8 = xor r6 r7
      r9 = prune r8
  in r9

apply : ℕ → (ℕ → ℕ) → ℕ → ℕ
apply zero _ a = a
apply (suc n) f a = apply n f (f a)

partA : String → String
partA inp =
  let lns = L.map (apply 2000 nxt)
          $ L.mapMaybe (readMaybe 10) (lines inp)
  in NS.show (sum lns)

mkKey : List ℤ → String
mkKey = Str.intersperse "," ∘ L.map IS.show

mkMap : List (String × ℕ) → Map ℕ
mkMap = unions ∘ L.map (λ (k , v) → singleton k v)

trunc : ℤ → ℕ
trunc = I._% (+ 10)

doLn : List ℕ → Map ℕ
doLn ln = mkMap $ L.zipWith (λ a (b , c , d , e) → ( mkKey (+ (trunc (+ b)) - + trunc (+ a) ∷ + trunc (+ c) - + trunc (+ b) ∷ + trunc (+ d) - + trunc (+ c) ∷ + trunc (+ e) - + trunc (+ d) ∷ []) , trunc (+ e) )) ln
        (L.zip (drop 1 ln) (L.zip (drop 2 ln) (L.zip (drop 3 ln) (drop 4 ln))))

findMax : Map ℕ → String × ℕ
findMax = L.foldr (λ x@( k , v ) a@( ka , va ) → if ⌊ v N.>? va ⌋ then x else a ) ("" , 0) ∘ mapToList

partB : String → String
partB inp =
  let lns = L.map (λ x → L.scanl (λ x _ → nxt x ) x (L.upTo 2000))
          $ L.mapMaybe (readMaybe 10) (lines inp)
      maps = L.map doLn lns
      m = unionsWith (λ n mn → maybe (N._+ n) n mn) maps
  in NS.show ∘ proj₂ $ findMax m