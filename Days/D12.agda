module Days.D12 where

open import Data.String as Str
open import Data.Nat as N
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Nat.Show as NS
open import Data.Char as C
import Data.Tree.AVL.Map
open Data.Tree.AVL.Map <-strictTotalOrder renaming (toList to mapToList; map to mapMap; foldr to mapFoldr; fromList to mapFromList; lookup to mapLookup; insert to mapInsert)
open import Data.List as L
open import Data.Bool as B
open import Function
open import Data.Product
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Maybe as M renaming (_>>=_ to _M>>=_) hiding (when)
open import Data.Unit
open import Effect.Monad
open import Effect.Monad.State

Plot : Set
Plot = Map (Map Char)

Visited : Set
Visited = Map (Map ⊤)

mkPlot : List (List Char) → Plot
mkPlot [] = empty
mkPlot xs@(x ∷ _) =
    mapFromList ∘ L.zip (upTo nrows)
    $ L.map (λ r → mapFromList (L.zip (upTo ncols) r)) xs
  where
  nrows = L.length xs
  ncols = L.length x

lookupC : ∀ {a : Set} → ℕ × ℕ → Map (Map a) → Maybe a
lookupC (r , c) dp = mapLookup dp r M.>>= λ m → mapLookup m c

insertC : ∀ {a : Set} → ℕ × ℕ → a → Map (Map a) → Map (Map a)
insertC (r , c) a = insertWith r (λ { nothing → singleton c a ; (just k) → mapInsert c a k })

adj : ℕ × ℕ → List (ℕ × ℕ)
adj (0 , 0) = (1 , 0) ∷ (0 , 1) ∷ (1000000 , 1000000) ∷ (1000000 , 1000000) ∷ []
adj (0 , c) = (1 , c) ∷ (0 , c + 1) ∷ (0 , ∣ c - 1 ∣) ∷ (1000000 , 1000000) ∷ []
adj (r , 0) = (r , 1) ∷ (r + 1 , 0) ∷ (∣ r - 1 ∣ , 0) ∷ (1000000 , 1000000) ∷ []
adj (r , c) = (r + 1 , c) ∷ (∣ r - 1 ∣ , c) ∷ (r , c + 1) ∷ (r , ∣ c - 1 ∣) ∷ []

sub1 : ℕ → ℕ
sub1 0 = 100000000000
sub1 (suc n) = n

diag : ℕ × ℕ → List (ℕ × ℕ)
diag (r , c) = (sub1 r , sub1 c) ∷ (sub1 r , c) ∷ (sub1 r , c + 1)
             ∷ (r , sub1 c) ∷           (r , c + 1)
             ∷ (r + 1 , sub1 c) ∷ (r + 1 , c) ∷ (r + 1 , c + 1) ∷ []

for : ∀ {a b s : Set} → List a → (a → State s b) → State s (List b)
for [] _ = pure []
  where open RawMonad monad
for (x ∷ xs) f = do
  b ← f x
  bs ← for xs f
  pure $ b ∷ bs
  where open RawMonad monad

modPerim : (ℕ → ℕ) → Visited × ℕ × ℕ → Visited × ℕ × ℕ
modPerim f (v , p , a) = (v , f p , a)

modArea : (ℕ → ℕ) → Visited × ℕ × ℕ → Visited × ℕ × ℕ
modArea f (v , p , a) = (v , p , f a)

{-# NON_TERMINATING #-}
explore : Plot → Char → ℕ × ℕ → State (Visited × ℕ × ℕ) ⊤
explore m pl coord = do
  nothing ← gets (lookupC coord ∘ proj₁)
    where (just _) → pure _
  just c ← pure (lookupC coord m)
    where nothing → pure _
  when (c C.== pl) $ do
    modify (λ (v , p , a) → (insertC coord _ v , p , a))
    modify (modArea suc)
    (vis , _ , _) ← get
    let nxt = filterᵇ (λ cc → is-nothing $ lookupC cc vis) $ adj coord
    let usingPerim = λ p → ∣ p - ∣ 4 - L.length nxt ∣ ∣ + L.length nxt
    modify (modPerim usingPerim)
    for nxt (explore m pl)
    pure _
  pure _
  where open RawMonad monad
        open RawMonadState monadState

{-# NON_TERMINATING #-}
regions : Plot → ℕ × ℕ → State Visited ℕ
regions m coord = do
  just c ← pure (lookupC coord m)
    where nothing → pure 0
  nothing ← gets (lookupC coord)
    where (just _) → pure 0
  modify (insertC coord _)
  let (vs , cp , ca) = execState (explore m c coord) (empty , 0 , 0)
  modify (unionWith (λ x y → union x (M.fromMaybe empty y)) vs)
  pure $ cp * ca
  where open RawMonad monad
        open RawMonadState monadState

partA : String → String
partA inp =
  let plt = mkPlot ∘ L.map Str.toList $ lines inp
      coords = L.concat ∘ L.map (λ ( r , col) → L.map (λ (c , _) → (r , c)) $ mapToList col) $ mapToList plt
      r = evalState (for coords (regions plt)) empty
  in NS.show $ sum r

transpose : Visited → Visited
transpose v = unionsWith (λ k mk → maybe (union k) k mk) ∘ L.concat ∘ L.map go $ mapToList v
  where
  go : ℕ × Map ⊤ → List Visited
  go (c , rows) = L.map (λ (r , _) → singleton r (singleton c _)) $ mapToList rows

diff : ∀ {a : Set} → Map (Map a) → Map (Map a) → Map (Map a)
diff a b = mapMap (mapFromList ∘ mapMaybe (λ (c , m) → m M>>= λ v → just (c , v)) ∘ mapToList) $
  unionWith (λ aa m → maybe (unionWith (λ v mm → maybe (const nothing) (just v) mm) aa) (mapMap just aa) m) a (mapMap (mapMap just) b)

xor : ∀ {a : Set} → Map (Map a) → Map (Map a) → Map (Map a)
xor a b = union (diff a b) (diff b a)

RS : Set
RS = Map (Map Bool)

rawSide : Visited → RS
rawSide v = xor (mapMap (mapMap (const true)) v) (mapFromList ∘ L.map (λ (k , x) → (k + 1 , mapMap (const false) x)) $ mapToList v)

sides : RS → ℕ
sides = sum ∘ L.map numSides ∘ mapToList
  where
  groupSide : Maybe (ℕ × Bool) → List (ℕ × Bool) → ℕ
  groupSide _ [] = 0
  groupSide nothing ((c , v) ∷ xs) = 1 + groupSide (just (c , v)) xs
  groupSide (just (l , v)) ((c , vv) ∷ xs) =
    if ⌊ suc l N.≟ c ⌋ ∧ ⌊ v B.≟ vv ⌋
      then groupSide (just (c , vv)) xs
      else 1 + groupSide (just (c , vv)) xs
  numSides : ℕ × Map Bool → ℕ
  numSides (_ , cols) = groupSide nothing $ mapToList cols

{-# NON_TERMINATING #-}
regions' : Plot → ℕ × ℕ → State Visited ℕ
regions' m coord = do
  just c ← pure (lookupC coord m)
    where nothing → pure 0
  nothing ← gets (lookupC coord)
    where (just _) → pure 0
  modify (insertC coord _)
  let (vs , cp , ca) = execState (explore m c coord) (empty , 0 , 0)
  let s1 = sides (rawSide vs)
  let s2 = sides (rawSide (transpose vs))
  modify (unionWith (λ x y → union x (M.fromMaybe empty y)) vs)
  pure $ (s1 + s2) * ca
  where open RawMonad monad
        open RawMonadState monadState

partB : String → String
partB inp =
  let plt = mkPlot ∘ L.map Str.toList $ lines inp
      coords = L.concat ∘ L.map (λ ( r , col) → L.map (λ (c , _) → (r , c)) $ mapToList col) $ mapToList plt
      r = evalState (for coords (regions' plt)) empty
  in NS.show $ sum r