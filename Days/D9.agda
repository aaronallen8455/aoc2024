module Days.D9 where

open import Data.String as Str
open import Data.Nat as N
open import Data.Nat.Properties as N
open import Data.Nat.Show as NS
open import Data.List as L
open import Data.Maybe as M
open import Data.Product
open import Data.Bool
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function

label : ℕ → ℕ → List ℕ → List (ℕ × ℕ × Maybe ℕ)
label i bi (x ∷ y ∷ xs) = (bi , x , just i) ∷ (bi + x , y , nothing) ∷ label (i + 1) (bi + x + y) xs
label i bi (x ∷ []) = [ (bi , x , just i) ]
label _ _ [] = []

{-# NON_TERMINATING #-}
checkSum : List (ℕ × ℕ × Maybe ℕ) → ℕ
checkSum xs = go 0 xs (L.reverse xs)
  where
  go : ℕ → List (ℕ × ℕ × Maybe ℕ) → List (ℕ × ℕ × Maybe ℕ) → ℕ
  go _ _ [] = 0
  go _ [] _ = 0
  go ix xss@((xi , x , just fl) ∷ xs) yss@((yi , y , yf) ∷ ys) =
    if ⌊ xi N.≥? yi ⌋
    then if ⌊ y N.>? 0 ⌋
         then ix * fl + go (ix + 1) xss ((yi , ∣ y - 1 ∣ , yf) ∷ ys)
         else 0
    else if ⌊ x N.>? 0 ⌋
         then fl * ix + go (ix + 1) ((xi , ∣ x - 1 ∣ , just fl) ∷ xs) yss
         else go ix xs yss
  go ix xs@((xi , _ , nothing) ∷ _) ((yi , _ , nothing) ∷ ys) =
    if ⌊ xi N.≥? yi ⌋
    then 0
    else go ix xs ys
  go ix ((xi , x , nothing) ∷ xs) ys@((yi , y , just fl) ∷ yss) =
    if ⌊ xi N.≥? yi ⌋
    then 0
    else if ⌊ x N.≟ 0 ⌋
         then go ix xs ys
         else if ⌊ y N.>? 0 ⌋
              then fl * ix + go (ix + 1) ((xi , ∣ x - 1 ∣ , nothing) ∷ xs) ((yi , ∣ y - 1 ∣ , just fl) ∷ yss)
              else go ix ((xi , x , nothing) ∷ xs) yss

partA : String → String
partA inp =
  let ns = mapMaybe (readMaybe 10 ∘ Str.fromChar) $ Str.toList inp
      r = checkSum (label 0 0 ns)
  in NS.show r

{-# NON_TERMINATING #-}
adder : ℕ → ℕ → ℕ → ℕ
adder _ _ 0 = 0
adder i f t = i * f + adder (i + 1) f ∣ t - 1 ∣

fill : ℕ → ℕ → List (ℕ × ℕ × Maybe ℕ) → List (ℕ × ℕ × Maybe ℕ) → (ℕ × ℕ × List (ℕ × ℕ × Maybe ℕ))
fill ix x yss@((yi , y , just yf) ∷ ys) ssy =
  if ⌊ ix N.≥? yi ⌋
  then (0 , x , L.reverse ssy L.++ yss)
  else if ⌊ y N.≤? x ⌋
      then (adder ix yf y , ∣ x - y ∣ , L.reverse ssy L.++ (yi , y , nothing) ∷ ys)
      else fill ix x ys ((yi , y , just yf) ∷ ssy)
fill ix x yss@((yi , y , nothing) ∷ ys) ssy =
  fill ix x ys ((yi , y , nothing) ∷ ssy)
fill _ x yss ssy =
  (0 , x , yss L.++ L.reverse ssy)

{-# NON_TERMINATING #-}
checkSum' : List (ℕ × ℕ × Maybe ℕ) → ℕ
checkSum' = go 0
  where
  go : ℕ → List (ℕ × ℕ × Maybe ℕ) → ℕ
  go _ [] = 0
  
  go ix ((xi , 0 , nothing) ∷ xs) = go ix xs
  go ix xss@((xi , x , nothing) ∷ xs) =
    case (fill ix x (L.reverse xs) []) of λ where
      (acc , newX , newXss) →
        if ⌊ newX N.≟ x ⌋
        then go (ix + x) xs
        else acc + go (ix + ∣ x - newX ∣) ((xi , newX , nothing) ∷ L.reverse newXss)
  go ix ((xi , x , just xf) ∷ xs) =
    adder ix xf x + go (ix + x) xs

partB : String → String
partB inp =
  let ns = mapMaybe (readMaybe 10 ∘ Str.fromChar) $ Str.toList inp
      r = checkSum' (label 0 0 ns)
  in NS.show r