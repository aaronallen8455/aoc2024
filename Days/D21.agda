module Days.D21 where

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

record Ctl : Set where
  inductive
  field
    pos : ℕ × ℕ
    slave : Maybe Ctl
    grid : Map Char
    keys : Map (ℕ × ℕ)
    dp : Map (Map ℕ)
    pressed : Maybe Char
    root : Bool

key : Char → ℕ
key = C.toℕ

coor : ℕ × ℕ → ℕ
coor (r , c) = r + c * 100

showC : ℕ × ℕ → String
showC (r , c) = NS.show r Str.++ "," Str.++ NS.show c

{-# NON_TERMINATING #-}
press : Char → ℕ → Ctl → Ctl × ℕ
press c times ctl = M.fromMaybe (ctl , 0) $ do
  let dpV = do
        p ← Ctl.pressed ctl
        dp1 ← mapLookup (Ctl.dp ctl) (key p)
        dp ← mapLookup dp1 (key c)
        pure dp
  dest ← mapLookup (Ctl.keys ctl) (key c)
  nothing ← just dpV
    where (just v) → just (record ctl { pressed = just c ; pos = dest } , v + pred times)

  let cp = Ctl.pos ctl
  false ← pure (⌊ proj₁ dest N.≟ proj₁ cp ⌋ ∧ ⌊ proj₂ dest N.≟ proj₂ cp ⌋)
    where true → let mS = do
                        sl ← Ctl.slave ctl
                        just $ press 'A' times sl
                     pr = if is-just (Ctl.slave ctl) then 0 else times 
                  in just ( record ctl { slave = M.map proj₁ mS
                                       ; pressed = just c
                                       }
                          , M.fromMaybe 0 (M.map proj₂ mS) + pr)
  let changeR = case N.compare (proj₁ cp) (proj₁ dest) of λ where
        (less _ _) → do
          let dist = ∣ proj₁ cp - proj₁ dest ∣′
              mS = M.map (press 'v' dist) $ Ctl.slave ctl
              newP = ( proj₁ dest , proj₂ cp )
          _ ← mapLookup (Ctl.grid ctl) (coor newP)
          let newCtl = record ctl { pos = newP
                                  ; slave = M.map proj₁ mS
                                  ; pressed = nothing
                                  }
              sc = M.fromMaybe 0 $ M.map proj₂ mS
          just ∘ map₂ (_+ sc) $ press c times newCtl
        (equal _) → nothing
        (greater _ _) → do
          let dist = ∣ proj₁ cp - proj₁ dest ∣′
              mS = M.map (press '^' dist) $ Ctl.slave ctl
              newP = ( proj₁ dest , proj₂ cp )
          _ ← mapLookup (Ctl.grid ctl) (coor newP)
          let newCtl = record ctl { pos = newP
                                  ; slave = M.map proj₁ mS
                                  ; pressed = nothing
                                  }
              sc = M.fromMaybe 0 $ M.map proj₂ mS
          just ∘ map₂ (_+ sc) $ press c times newCtl

  let changeC = case N.compare (proj₂ cp) (proj₂ dest) of λ where
        (less _ _) → do
          let dist = ∣ proj₂ cp - proj₂ dest ∣′
              mS = M.map (press '>' dist) $ Ctl.slave ctl
              newP = ( proj₁ cp , proj₂ dest )
          _ ← mapLookup (Ctl.grid ctl) (coor newP)
          let newCtl = record ctl { pos = newP
                                  ; slave = M.map proj₁ mS
                                  ; pressed = nothing
                                  }
              sc = M.fromMaybe 0 $ M.map proj₂ mS
          just ∘ map₂ (_+ sc) $ press c times newCtl
        (equal _) → nothing
        (greater _ _) → do
          let dist = ∣ proj₂ cp - proj₂ dest ∣′
              mS = M.map (press '<' dist) $ Ctl.slave ctl
              newP = ( proj₁ cp , proj₂ dest )
          _ ← mapLookup (Ctl.grid ctl) (coor newP)
          let 
              newCtl = record ctl { pos = newP
                                  ; slave = M.map proj₁ mS
                                  ; pressed = nothing
                                  }
              nxt = press c times newCtl
              sc = M.fromMaybe 0 $ M.map proj₂ mS
          just $ map₂ (_+ sc) nxt

  let cheapest = do
        let cond =
              ( ((⌊ proj₁ cp N.≟ 0 ⌋ ∧ ⌊ proj₂ cp N.≟ 1 ⌋ ∧ ⌊ proj₁ dest N.≟ 1 ⌋ ∧ ⌊ proj₂ dest N.≟ 2 ⌋) ∨ (⌊ proj₁ cp N.≟ 1 ⌋ ∧ ⌊ proj₂ cp N.≟ 1 ⌋ ∧ ⌊ proj₁ dest N.≟ 0 ⌋ ∧ ⌊ proj₂ dest N.≟ 2 ⌋))
              ∨ Ctl.root ctl
              )
        true ← pure cond
          where false → nothing
        cr ← changeR
        cc ← changeC
        let -- cdp = unionWith (λ m mm → maybe (union m) m mm) (Ctl.dp (proj₁ cr)) (Ctl.dp (proj₁ cc))
            sc = M.fromMaybe (99 , 99) $ M.map Ctl.pos $ Ctl.slave ctl
        if ⌊ proj₂ cr N.<? proj₂ cc ⌋
          then just cr
          else just cc
  res ← cheapest <∣> changeC <∣> changeR 
  let newCtl = proj₁ res
      newCtl2 = case Ctl.pressed ctl of λ where
                  nothing → newCtl
                  (just start) →
                    let cost = ∣ proj₂ res - pred times ∣′
                    in record newCtl
                        { dp = insertWith (key start) (λ mE → maybe (mapInsert (key c) cost) (singleton (key c) cost) mE) (Ctl.dp newCtl)
                        }
  pure (newCtl2 , proj₂ res)
  where open RawMonad ME.monad

dirGrid : Map Char
dirGrid = mapFromList ∘ L.map (map₁ coor) $ ((0 , 1) , '^') ∷ ((0 , 2) , 'A') ∷ ((1 , 0), '<') ∷ ((1 , 1) , 'v') ∷ ((1 , 2) , '>') ∷ []

doorGrid : Map Char
doorGrid = mapFromList ∘ L.map (map₁ coor) $
  ((0 , 0) , '7') ∷
  ((0 , 1) , '8') ∷
  ((0 , 2) , '9') ∷
  ((1 , 0) , '4') ∷
  ((1 , 1) , '5') ∷
  ((1 , 2) , '6') ∷
  ((2 , 0) , '1') ∷
  ((2 , 1) , '2') ∷
  ((2 , 2) , '3') ∷
  ((3 , 1) , '0') ∷
  ((3 , 2) , 'A') ∷ []

toCoor : ℕ → ℕ × ℕ
toCoor n = ( n % 100 , n / 100)

toKeyMap : Map Char → Map (ℕ × ℕ)
toKeyMap = mapFromList ∘ L.map (map₂ toCoor ∘ map₁ key ∘ swap) ∘ mapToList

initSlave : Maybe Ctl → Ctl
initSlave s = record
  { pos = (0 , 2)
  ; slave = s
  ; grid = dirGrid
  ; keys = toKeyMap dirGrid
  ; dp = emptyMap
  ; pressed = just 'A'
  ; root = false
  }

initMaster : Ctl
initMaster = record
  { pos = (3 , 2)
  ; slave = just $ initSlave $ just $ initSlave $ just $ initSlave nothing
  ; grid = doorGrid
  ; keys = toKeyMap doorGrid
  ; dp = emptyMap
  ; pressed = just 'A'
  ; root = true
  }

compl : String → ℕ
compl s =
  let r = L.foldl (λ (c , n) x → map₂ (_+ n) $ press x 1 c) (initMaster , 0) $ Str.toList s
      n = M.fromMaybe 0 ∘ readMaybe 10 ∘ Str.fromList ∘ filterᵇ C.isDigit $ Str.toList s
   in proj₂ r * n

partA : String → String
partA inp = NS.show ∘ sum ∘ L.map compl $ lines inp

initMaster2 : Ctl
initMaster2 = record
  { pos = (3 , 2)
  ; slave = just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $ -- 
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave $ just $
      initSlave nothing
  ; grid = doorGrid
  ; keys = toKeyMap doorGrid
  ; dp = emptyMap
  ; pressed = just 'A'
  ; root = true
  }

compl2 : String → ℕ
compl2 s =
  let r = L.foldl (λ (c , n) x → map₂ (_+ n) $ press x 1 c) (initMaster2 , 0) $ Str.toList s
      n = M.fromMaybe 0 ∘ readMaybe 10 ∘ Str.fromList ∘ filterᵇ C.isDigit $ Str.toList s
   in proj₂ r * n
  
partB : String → String
partB inp = NS.show ∘ sum ∘ L.map compl2 $ lines inp