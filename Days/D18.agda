module Days.D18 where

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
open import Effect.Monad
open import Data.Unit
open import Effect.Monad
open import Effect.Monad.State as MS

rBound : ℕ
rBound = 72

cBound : ℕ
cBound = 72

G : Set
G = Map (Map ⊤)

mkG : List (ℕ × ℕ) → G
mkG cs = unionsWith (λ x mx → maybe (union x) x mx) $ L.map (λ (r , c) → singleton r (singleton c tt)) cs

lookupC : ∀ {a : Set} → ℕ × ℕ → Map (Map a) → Maybe a
lookupC (r , c) dp = mapLookup dp r M.>>= λ m → mapLookup m c

insertC : ∀ {a : Set} → ℕ × ℕ → a → Map (Map a) → Map (Map a)
insertC (r , c) a = insertWith r (λ { nothing → singleton c a ; (just k) → mapInsert c a k })

inBounds : ℕ × ℕ → Bool
inBounds (0 , _) = false
inBounds (_ , 0) = false
inBounds (r , c) = ⌊ r N.<? rBound ⌋ ∧ ⌊ c N.<? cBound ⌋

adj : ℕ × ℕ → List (ℕ × ℕ)
adj (r , c) = filterᵇ inBounds $ (pred r , c) ∷ (r + 1 , c) ∷ (r , pred c) ∷ (r , c + 1) ∷ []

nonMem : G → ℕ × ℕ → Bool
nonMem g c = M.is-nothing $ lookupC c g

{-# NON_TERMINATING #-}
search : G → List (List (ℕ × ℕ)) → State G (List (ℕ × ℕ))
search _ [] = pure []
  where open RawMonad MS.monad
search g fringe = go fringe [] where
  open RawMonad MS.monad
  open RawMonadState MS.monadState
  go : List (List (ℕ × ℕ)) → List (List (ℕ × ℕ)) → State G (List (ℕ × ℕ))
  go [] acc = search g acc
  go ((coord ∷ p ) ∷ rest ) acc = do
    false ← pure (⌊ proj₁ coord N.≟ pred rBound ⌋ ∧ ⌊ proj₂ coord N.≟ pred cBound ⌋)
      where true → pure $ coord ∷ p
    nothing ← gets (lookupC coord)
      where _ → go rest acc
    modify $ insertC coord tt
    let cs = L.map (λ c → c ∷ coord ∷ p) $ filterᵇ (nonMem g) $ adj coord
    go rest (cs L.++ acc)
  go _ _ = pure []

parseC : String → Maybe (ℕ × ℕ)
parseC ln = case Str.wordsByᵇ (C._== ',') ln of λ where
  (x ∷ y ∷ []) → do
    xn ← readMaybe 10 x
    yn ← readMaybe 10 y
    just (yn + 1 , xn + 1)
  _ → nothing
 where open RawMonad ME.monad

showC : ℕ × ℕ → String
showC (r , c) = NS.show r Str.++ ", " Str.++ NS.show c

partA : String → String
partA inp =
  let bs = L.take 2903 $ mapMaybe parseC $ lines inp
      g = mkG bs
      r = evalState (search g [ [ (1 , 1) ] ]) emptyMap
  in NS.show (pred $ L.length r)

{-# NON_TERMINATING #-}
binS : List (ℕ × ℕ) → Maybe (ℕ × ℕ)
binS bs = go 1024 (L.length bs) where
  go : ℕ → ℕ → Maybe (ℕ × ℕ)
  go lb ub =
    if ⌊ ∣ lb - ub ∣ N.≟ 1 ⌋
    then L.head (L.drop lb bs)
    else
      let m = ∣ lb - ub ∣ / 2
          g = mkG $ take (lb + m) bs
      in case evalState (search g [ [ (1 , 1) ] ]) emptyMap of λ where
          [] → go lb (lb + m)
          _ → go (lb + m) ub

partB : String → String
partB inp =
  let bs = mapMaybe parseC $ lines inp
      r = binS bs
  in M.fromMaybe "no" $ M.map showC r