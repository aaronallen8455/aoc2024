module Days.D4 where

open import Data.String hiding (map; _++_)
open import Function
open import Data.List
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Nat.Show
open import Data.Char

zipIt : ∀ {a : Set} → List a → List (List a) → List (List a)
zipIt (x ∷ xs) (y ∷ ys) = (x ∷ y) ∷ zipIt xs ys
zipIt [] ys = ys
zipIt xs [] = map [_] xs

transpose : ∀ {a : Set} → List (List a) → List (List a)
transpose {a} = foldr zipIt []

diags : ∀ {a : Set} → List (List a) → List (List a)
diags {a} xss =
  let (a , b) = split 0 xss
  in reverse b ++ transpose a
  where
  split : ℕ → List (List a) → ( List (List a) × List (List a) )
  split n (x ∷ xs) =
    let (a , b) = splitAt n x
        (as , bs) = split (n + 1) xs
    in ( zipIt a as , zipIt b bs )
  split _ [] = ( [] , [] )

xmas : List Char → ℕ
xmas ('X' ∷ 'M' ∷ 'A' ∷ 'S' ∷ rest) = 1 + xmas rest
xmas (_ ∷ rest) = xmas rest
xmas [] = 0

partA : String → String
partA inp =
  let lns1 = map toList (lines inp)
      lns2 = transpose lns1
      lns3 = diags lns1
      lns4 = diags (reverse lns1)
  in Data.Nat.Show.show $
     sum (map xmas lns1)
   + sum (map xmas (map reverse lns1))
   + sum (map xmas lns2)
   + sum (map xmas (map reverse lns2))
   + sum (map xmas lns3)
   + sum (map xmas (map reverse lns3))
   + sum (map xmas lns4)
   + sum (map xmas (map reverse lns4))

x-mas' : List Char → List Char → List Char → ℕ
x-mas' ('M' ∷  a  ∷ 'S' ∷ rest1)
       ( _  ∷ 'A' ∷  b  ∷ rest2)
       ('M' ∷  c  ∷ 'S' ∷ rest3)
  = 1 + x-mas' (a ∷ 'S' ∷ rest1) ('A' ∷ b ∷ rest2) (c ∷ 'S' ∷ rest3)
x-mas' (_ ∷ r1) (_ ∷ r2) (_ ∷ r3) = x-mas' r1 r2 r3
x-mas' _ _ _ = 0

x-mas : List (List Char) → ℕ
x-mas (a ∷ b ∷ c ∷ rest) = x-mas' a b c + x-mas (b ∷ c ∷ rest)
x-mas _ = 0

partB : String → String
partB inp =
  let lns1 = map toList (lines inp)
      lns2 = transpose lns1
  in Data.Nat.Show.show $
       x-mas lns1
     + x-mas (map reverse lns1)
     + x-mas lns2
     + x-mas (map reverse lns2)