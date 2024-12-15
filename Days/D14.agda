module Days.D14 where

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
open import Data.Integer as I
open import Data.Integer.Properties as I
open import Data.Unit

rBound : ℕ
rBound = 103

cBound : ℕ
cBound = 101

record Robot : Set where
  field
    rPos : ℤ
    cPos : ℤ
    rV : ℤ
    cV : ℤ

parseInt : String → Maybe ℤ
parseInt l = case Str.toList l of λ where
  ('-' ∷ rest) → readMaybe 10 (Str.fromList rest) >>= (λ n → just $ I.- I.+ n)
  _ → readMaybe 10 l >>= (λ n → just $ I.+ n)

parseV : String → Maybe (ℤ × ℤ)
parseV = go ∘ L.wordsByᵇ (C._== ',') ∘ L.drop 2 ∘ Str.toList
  where
  go : List (List Char) → Maybe (ℤ × ℤ)
  go (a ∷ b ∷ []) = do
    ai ← parseInt (Str.fromList a)
    bi ← parseInt (Str.fromList b)
    just (ai , bi)
  go _ = nothing

parseRobot : String → Maybe Robot
parseRobot l = case words l of λ where
  (p ∷ v ∷ []) → do
    (pc , pr) ← parseV p
    (vc , vr) ← parseV v
    just record { rPos = pr ; cPos = pc ; rV = vr; cV = vc }
  _ → nothing

steps : ℤ → Robot → Robot
steps n rob =
  record rob
    { rPos = I.+ ((Robot.rPos rob I.+ n I.* Robot.rV rob) %ℕ rBound)
    ; cPos = I.+ ((Robot.cPos rob I.+ n I.* Robot.cV rob) %ℕ cBound)
    }

inQ : ℤ × ℤ → ℤ × ℤ → Robot → Bool
inQ (minR , minC) (maxR , maxC) rob =
  (minR I.≤ᵇ Robot.rPos rob)
  ∧
  (minC I.≤ᵇ Robot.cPos rob)
  ∧
  (Robot.rPos rob I.≤ᵇ maxR)
  ∧
  (Robot.cPos rob I.≤ᵇ maxC)

partA : String → String
partA inp =
  let robs = mapMaybe parseRobot $ lines inp
      r = L.map (steps (+ 100)) robs
      q1 = L.filterᵇ (inQ (+ 0 , + 0) (+ (N.pred (rBound N./ 2)) , + (N.pred (cBound N./ 2)))) r
      q2 = L.filterᵇ (inQ (+ 0 , + (N.suc (cBound N./ 2))) (+ (N.pred (rBound N./ 2)) , + cBound)) r
      q3 = L.filterᵇ (inQ (+ (N.suc (rBound N./ 2)) , + 0) (+ rBound , + (N.pred (cBound N./ 2)))) r
      q4 = L.filterᵇ (inQ (+ (N.suc (rBound N./ 2)) , + (N.suc (cBound N./ 2))) (+ rBound , + cBound)) r
  in NS.show $ product $ L.map L.length (q1 ∷ q2 ∷ q3 ∷ q4 ∷ [])

G : Set
G = Map (Map ⊤)

toG : List Robot → G
toG = L.foldr go empty
  where
  go : Robot → G → G
  go rob g = insertWith ∣ Robot.rPos rob ∣ (λ { nothing → singleton ∣ Robot.cPos rob ∣ _ ; (just cols) → mapInsert ∣ Robot.cPos rob ∣ _ cols}) g

lookupC : ∀ {a : Set} → ℕ × ℕ → Map (Map a) → Maybe a
lookupC (r , c) dp = mapLookup dp r M.>>= λ m → mapLookup m c

showG : G → String
showG g = unlines ∘ L.map (λ r → Str.fromList $ L.map (λ c → maybe (const '*') ' ' $ lookupC (r , c) g) $ L.upTo cBound) $ L.upTo (rBound N.+ 3)

{-# NON_TERMINATING #-}
findTree : List Robot → ℕ → Maybe (List Robot × ℕ)
findTree robs n =
  let new = L.map (steps ( + 1 )) robs
      mostInQ1 r = ⌊
                   L.length (L.filterᵇ (inQ (+ 0 , + 0) (+ (N.pred (rBound N./ 2)) , + (N.pred (cBound N./ 2)))) r)
                   >? (L.length r N./ 2)
                   ⌋
  in if mostInQ1 new 
     then just (new , n N.+ 1)
     else findTree new (n N.+ 1)

partB : String → String
partB inp =
  let robs = mapMaybe parseRobot $ lines inp
      mt = M.map (λ (r , n) → NS.show n Str.++ "\n" Str.++ showG (toG r)) $ findTree robs 0
  in M.fromMaybe "" mt