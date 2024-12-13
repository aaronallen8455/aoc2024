module Days.D11 where

open import Data.String as Str
open import Data.Nat as N
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Nat.Show as NS
import Data.Tree.AVL.Map
open Data.Tree.AVL.Map <-strictTotalOrder renaming (toList to mapToList; map to mapMap; foldr to mapFoldr; fromList to mapFromList; lookup to mapLookup; insert to mapInsert)
open import Data.List as L
open import Data.Bool
open import Function
open import Data.Product
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Maybe as M renaming (_>>=_ to _M>>=_)

Stones : Set
Stones = Map ℕ

step : ℕ → Stones
step 0 = singleton 1 1
step x =
  let xstr = Str.toList $ NS.show x
      (a , b) = L.splitAt ⌊ L.length xstr /2⌋ xstr
  in if ⌊ L.length a N.≟ L.length b ⌋
     then (
       let an = M.fromMaybe 0 $ readMaybe 10 $ Str.fromList a
           bn = M.fromMaybe 0 $ readMaybe 10 $ Str.fromList b
       in if ⌊ an N.≟ bn ⌋
          then singleton an 2
          else mapFromList ((an , 1) ∷ (bn , 1) ∷ [])
     )
     else singleton (x * 2024) 1

step' : Stones → Stones
step' = unionsWith (λ x y → M.fromMaybe 0 y + x) ∘ L.map (λ ( n , x ) → mapMap (_* x) (step n)) ∘ mapToList

count : Stones → ℕ
count = sum ∘ L.map proj₂ ∘ mapToList

blinks : ℕ → Stones → Stones
blinks 0 s = s
blinks (suc n) s = blinks n (step' s)

partA : String → String
partA inp =
  let xs = mapFromList ∘ L.map (λ x → ( x , 1 )) ∘ L.mapMaybe (readMaybe 10) $ words inp
      r = count $ blinks 25 xs
   in NS.show r

partB : String → String
partB inp =
  let xs = mapFromList ∘ L.map (λ x → ( x , 1 )) ∘ L.mapMaybe (readMaybe 10) $ words inp
      r = count $ blinks 75 xs
   in NS.show r