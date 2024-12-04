module Days.D3 where

open import Data.String
open import Data.List
open import Data.Char
open import Data.Nat
open import Data.Nat.Show
open import Data.Product
open import Data.Maybe hiding (_>>=_)
open import Function
open import Data.Bool
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Effect.Monad
open import Effect.Monad.State

St : Set
St = List Char × Bool

setFst : ∀ {a b : Set} → a → a × b → a × b
setFst = map₁ ∘ const

parseNum : State St (Maybe ℕ)
parseNum = do
  i ← gets proj₁
  let ( b , a ) = spanᵇ isDigit i
  if ( ⌊ (Data.List.length b) Data.Nat.>? 0 ⌋ ∧ ⌊ (Data.List.length b) Data.Nat.<? 4 ⌋ )
    then (do
      modify (setFst a)
      pure (readMaybe 10 (fromList b))
    )
    else (pure nothing)
  where open RawMonad monad
        open RawMonadState monadState

munch : Char → State St Bool
munch c = do
  (i ∷ rest) ← gets proj₁
    where [] → pure false
  if ⌊ i Data.Char.≟ c ⌋
    then (do
      modify (setFst rest)
      pure true
      )
    else (pure false)
  where open RawMonad monad
        open RawMonadState monadState

parseMul : State St (Maybe ℕ)
parseMul = do
  ( i , isOn ) ← get
  case i of λ where
    ('m' ∷ 'u' ∷ 'l' ∷ '(' ∷ rest ) → do
      modify (setFst rest)
      just a ← parseNum
        where nothing → pure nothing
      true ← munch ','
        where false → pure nothing
      just b ← parseNum
        where nothing → pure nothing
      true ← munch ')'
        where false → pure nothing
      if isOn
        then (pure (just (a * b)))
        else (pure nothing)
    (_ ∷ rest ) → do
      modify (setFst rest)
      pure nothing
    [] → pure nothing
  where open RawMonad monad
        open RawMonadState monadState

{-# NON_TERMINATING #-}
many : ∀ {a} → State St a → State St (List a)
many s = do
  _ ∷ _ ← gets proj₁
    where [] → pure []
  x ← s
  xs ← many s
  pure (x ∷ xs)
  where open RawMonad monad
        open RawMonadState monadState

partA : String → String
partA x =
  let l = Data.String.toList x
      r = evalState (many parseMul) ( l , true )
  in Data.Nat.Show.show (sum (catMaybes r))

parseDo : State St _
parseDo = do
  'd' ∷ 'o' ∷ '(' ∷ ')' ∷ rest ← gets proj₁
    where _ → pure _
  put ( rest , true )
  where open RawMonad monad
        open RawMonadState monadState

parseDon't : State St _
parseDon't = do
  'd' ∷ 'o' ∷ 'n' ∷ '\'' ∷ 't' ∷ '(' ∷ ')' ∷ rest ← gets proj₁
    where _ → pure _
  put ( rest , false )
  where open RawMonad monad
        open RawMonadState monadState

partB : String → String
partB x =
  let l = Data.String.toList x
      r = evalState (many (parseDo >> parseDon't >> parseMul)) ( l , true )
  in Data.Nat.Show.show (sum (catMaybes r))
  where open RawMonad monad