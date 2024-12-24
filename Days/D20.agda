module Days.D20 where

open import Data.String as Str
open import Data.Nat as N
open import Data.Nat.Properties using (<-strictTotalOrder ; ≤-decTotalOrder)
open import Data.Nat.Show as NS
import Data.Tree.AVL.Map
open Data.Tree.AVL.Map <-strictTotalOrder renaming (toList to mapToList; map to mapMap; foldr to mapFoldr; fromList to mapFromList; lookup to mapLookup; insert to mapInsert ; empty to emptyMap)
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

G : Set
G = Map (Map Char)

Cells : Set
Cells = Map (Map ℕ)

lookupC : ∀ {a : Set} → ℕ × ℕ → Map (Map a) → Maybe a
lookupC (r , c) dp = mapLookup dp r M.>>= λ m → mapLookup m c

insertC : ∀ {a : Set} → ℕ × ℕ → a → Map (Map a) → Map (Map a)
insertC (r , c) a = insertWith r (λ { nothing → singleton c a ; (just k) → mapInsert c a k })

findC : Char → G → Maybe (ℕ × ℕ)
findC g = L.head ∘ L.concat ∘ L.map (λ ( ri , x ) → mapMaybe (λ (ci , c) →
                  if c C.== g then (just (ri , ci)) else nothing)
                  (mapToList x))
            ∘ mapToList

mkG : List (List Char) → G
mkG [] = emptyMap
mkG xs@(x ∷ _) =
    mapFromList ∘ L.zip (upTo nrows)
    $ L.map (λ r → mapFromList (L.zip (upTo ncols) r)) xs
  where
  nrows = L.length xs
  ncols = L.length x

adj : ℕ × ℕ → List (ℕ × ℕ)
adj (r , c) = (pred r , c) ∷ (r + 1 , c) ∷ (r , pred c) ∷ (r , c + 1) ∷ []

traverse_ : ∀ {a s : Set} → (a → State s ⊤) → List a → State s ⊤
traverse_ f [] = pure tt
  where open RawMonad MS.monad
traverse_ f (x ∷ xs) = f x >> traverse_ f xs
  where open RawMonad MS.monad

{-# NON_TERMINATING #-}
path : G → ℕ → ℕ × ℕ → State Cells ⊤
path g n c = do
  ch ← pure (lookupC c g)
  case ch of λ where
    (just '#') → pure tt
    nothing → pure tt
    _ → do
      nothing ← gets (lookupC c)
        where _ → pure tt

      modify (insertC c n)

      traverse_ (path g (n + 1)) (adj c)

  where open RawMonad MS.monad
        open RawMonadState MS.monadState

cheatC : ℕ × ℕ → List (ℕ × ℕ)
cheatC (r , c) = (pred (pred r) , c) ∷ (r + 2 , c) ∷ (r , pred (pred c)) ∷ (r , c + 2) ∷ (pred r , pred c) ∷ (pred r , c + 1) ∷ (r + 1 , pred c) ∷ (r + 1 , c + 1) ∷ []

cheats : Cells → ℕ × ℕ → List ((ℕ × ℕ) × (ℕ × ℕ) × ℕ)
cheats cs c = do
  just s ← [ lookupC c cs ]
    where _ → []
  nc ← cheatC c
  just ns ← [ lookupC nc cs ]
    where _ → []
  true ← [ ⌊ ns N.>? s ⌋ ∧ ⌊ ∣ s - ns ∣′ N.≥? 102 ⌋ ]
    where _ → []
  [ c , nc , ∣ s - ns ∣ ]
  where open RawMonad LE.monad

partA : String → String
partA inp =
  let g = mkG (L.map Str.toList $ lines inp)
      s = M.fromMaybe (0 , 0) $ findC 'S' g
      cs = execState (path g 0 s) emptyMap
      cz = L.concatMap (λ (r , col) → L.map (λ (c , _) → (r , c)) $ mapToList col) $ mapToList cs
      r = L.concatMap (cheats cs) cz
  in NS.show (L.length r)

sub : ℕ → ℕ → List ℕ
sub a b =
  if ⌊ a N.<? b ⌋
  then []
  else [ ∣ a - b ∣′ ]

cellList : Map (Map ⊤) → List (ℕ × ℕ)
cellList = L.concatMap (λ (r , col) → L.map (λ (c , _) → (r , c)) $ mapToList col) ∘ mapToList

listCell : List (ℕ × ℕ) → Map (Map ⊤)
listCell xs = unionsWith (λ a → maybe (union a) a) $ L.map (λ (r , c) → singleton r (singleton c tt)) xs

superCheatC : ℕ × ℕ → List (ℕ × ℕ)
superCheatC (r , c) = cellList ∘ listCell $ do
  nr ← upTo 21
  nc ← upTo 21
  false ← [ ⌊ (nr + nc) N.≟ 0 ⌋ ]
    where true → []
  false ← [ ⌊ (nr + nc) N.>? 20 ⌋ ]
    where true → []
  ro ← (λ a b → [ a + b ]) ∷ sub ∷ []
  co ← (λ a b → [ a + b ]) ∷ sub ∷ []
  nnr ← ro r nr
  nnc ← co c nc
  [ nnr , nnc ]
  where open RawMonad LE.monad

superCheats : Cells → ℕ × ℕ → List ⊤
superCheats cs c = do
  just s ← [ lookupC c cs ]
    where _ → []
  nc ← superCheatC c
  just ns ← [ lookupC nc cs ]
    where _ → []
  let d = ∣ proj₁ c - proj₁ nc ∣′ + ∣ proj₂ c - proj₂ nc ∣′
  true ← [ ⌊ ns N.>? s ⌋ ∧ ⌊ ∣ s - ns ∣′ N.≥? (100 + d) ⌋ ]
    where _ → []
  [ tt ]
  where open RawMonad LE.monad

partB : String → String
partB inp =
  let g = mkG (L.map Str.toList $ lines inp)
      s = M.fromMaybe (0 , 0) $ findC 'S' g
      cs = execState (path g 0 s) emptyMap
      cz = L.concatMap (λ (r , col) → L.map (λ (c , _) → (r , c)) $ mapToList col) $ mapToList cs
      r = L.concatMap (superCheats cs) cz
  in NS.show (L.length r)