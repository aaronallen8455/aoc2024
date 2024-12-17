module Days.D16 where

open import Data.String as Str
open import Data.Nat as N
open import Data.Nat.Properties using (<-strictTotalOrder)
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
open import Effect.Monad
open import Effect.Monad.State
open import Data.Unit

data Dir : Set where
  U D L R : Dir

eqDir : Dir → Dir → Bool
eqDir U U = true
eqDir D D = true
eqDir L L = true
eqDir R R = true
eqDir _ _ = false

G : Set
G = Map (Map Char)

Cells : Set
Cells = Map ⊤

Q : Set
Q = Map (List ((ℕ × ℕ) × (Dir × Cells)))

lookupC : ∀ {a : Set} → ℕ × ℕ → Map (Map a) → Maybe a
lookupC (r , c) dp = mapLookup dp r M.>>= λ m → mapLookup m c

insertC : ∀ {a : Set} → ℕ × ℕ → a → Map (Map a) → Map (Map a)
insertC (r , c) a = insertWith r (λ { nothing → singleton c a ; (just k) → mapInsert c a k })

Visited : Set
Visited = Map (Map (List (Dir × ℕ)))

isVisited : ℕ × ℕ → Dir → ℕ → Visited → Maybe Visited
isVisited coord dir cost v = case lookupC coord v of λ where
  nothing → just $ insertC coord [ dir , cost ] v
  (just xs) →
    case L.breakᵇ (λ (d , _) → eqDir d dir) xs of λ where
      ( before , (_ , c) ∷ after ) →
        if ⌊ c N.<? cost ⌋
        then nothing
        else just (insertC coord ((dir , cost) ∷ before L.++ after) v)
      _ → just $ insertC coord ((dir , cost) ∷ xs) v

mv : ℕ × ℕ → Dir → ℕ × ℕ
mv (r , c) U = (pred r , c)
mv (r , c) D = (r + 1 , c)
mv (r , c) L = (r , pred c)
mv (r , c) R = (r , c + 1)

turnLeft : ℕ × ℕ → Dir → (ℕ × ℕ) × Dir
turnLeft coord U = (mv coord L , L)
turnLeft coord L = (mv coord D , D)
turnLeft coord D = (mv coord R , R)
turnLeft coord R = (mv coord U , U)

turnRight : ℕ × ℕ → Dir → (ℕ × ℕ) × Dir
turnRight coord U = (mv coord R , R)
turnRight coord L = (mv coord U , U)
turnRight coord D = (mv coord L , L)
turnRight coord R = (mv coord D , D)

straight : ℕ × ℕ → Dir → (ℕ × ℕ) × Dir
straight coord U = (mv coord U , U)
straight coord L = (mv coord L , L)
straight coord D = (mv coord D , D)
straight coord R = (mv coord R , R)

cands : ℕ × ℕ → Dir → ℕ → List (ℕ × ((ℕ × ℕ) × Dir))
cands coord dir cost = (cost + 1 , straight coord dir) ∷ (cost + 1001 , turnLeft coord dir) ∷ (cost + 1001 , turnRight coord dir) ∷ []

insertQ : Cells → ℕ × ((ℕ × ℕ) × Dir) → Q → Q
insertQ cells (cost , (coord@(r , c) , dir)) = insertWith cost λ where
  nothing → [ (coord , dir , mapInsert (r * 1000000 + c) _ cells) ]
  (just xs) → (coord , dir , mapInsert (r * 1000000 + c) _ cells) ∷ xs

traverseMaybe : ∀ {a b : Set} → (a → State Visited (Maybe b)) → List a → State Visited (List b)
traverseMaybe _ [] = pure []
  where open RawMonad monad
traverseMaybe f (x ∷ xs) = do
  m ← f x
  xs ← traverseMaybe f xs
  pure $ maybe (_∷ xs) xs m
  where open RawMonad monad

{-# NON_TERMINATING #-}
go : G → Q → State Visited (Maybe (ℕ × Cells))
go g q = case headTail q of λ where
    (just ((_ , []) , rest)) → go g rest
    (just ((cost , ((row , col) , (dir , cells)) ∷ xs) , rest)) → do
      (just cell) ← pure $ lookupC (row , col) g
        where nothing → go g (mapInsert cost xs rest)
      case cell of λ where
        '#' → go g (mapInsert cost xs rest)
        'E' → do
          rr ← traverseMaybe (go g) $ L.map (λ x → singleton cost [ x ]) xs
          pure (just (cost , union cells (unions $ L.map proj₂ rr)))
        _ → do
          (just newV) ← gets (isVisited (row , col) dir cost)
            where nothing → go g (mapInsert cost xs rest)
          put newV
          go g (L.foldr (insertQ cells) (mapInsert cost xs rest) $ cands (row , col) dir cost)
    nothing → pure nothing
  where
    open RawMonad monad
    open RawMonadState monadState

findS : G → Maybe (ℕ × ℕ)
findS = L.head ∘ L.concat ∘ L.map (λ ( ri , x ) → mapMaybe (λ (ci , c) →
                  if c C.== 'S' then (just (ri , ci)) else nothing)
                  (mapToList x))
            ∘ mapToList

mkG : List (List Char) → G
mkG [] = empty
mkG xs@(x ∷ _) =
    mapFromList ∘ L.zip (upTo nrows)
    $ L.map (λ r → mapFromList (L.zip (upTo ncols) r)) xs
  where
  nrows = L.length xs
  ncols = L.length x

partA : String → String
partA inp =
  let g = mkG ∘ L.map Str.toList $ lines inp
      s = M.fromMaybe (0 , 0) $ findS g
      r = evalState (go g (singleton 0 [ (s , R , singleton (proj₁ s * 1000000 + proj₂ s) _ ) ])) empty
  in NS.show ∘ proj₁ $ M.fromMaybe (0 , empty) r

partB : String → String
partB inp =
  let g = mkG ∘ L.map Str.toList $ lines inp
      s = M.fromMaybe (0 , 0) $ findS g
      r = evalState (go g (singleton 0 [ (s , R , singleton (proj₁ s * 1000000 + proj₂ s) _) ])) empty
  in NS.show ∘ size ∘ proj₂ $ M.fromMaybe (0 , empty) r