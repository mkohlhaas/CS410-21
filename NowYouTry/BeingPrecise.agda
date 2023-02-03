module NowYouTry.BeingPrecise where

open import Agda.Builtin.Nat

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

-- think of `Vec A n` as a `List A` with a lenght `n`
data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

-- Problem: Cannot return something from an empty list.
-- _!!_ : ∀ {A} → List A → Nat → A
-- [] !! n = {!!}
-- (x ∷ xs) !! zero = x
-- (x ∷ xs) !! suc n = xs !! n

-- open import Data.Maybe
--
-- Works, but clumsy because we will always get back a `Maybe`.
-- _!!_ : ∀ {A} → List A → Nat → Maybe A
-- [] !! n = nothing
-- (x ∷ xs) !! zero = just x
-- (x ∷ xs) !! suc n = xs !! n

-- using a Vector
-- We are asking for the n-th element were `Fin n` is smaller than n.
_!!_ : ∀ {A n} → Vec A n → Fin n → A
(x ∷ xs) !! zero = x
(x ∷ xs) !! suc n = xs !! n

---------------------------------------------------------------------------
-- Converting Haskell `head` and `tail` Functions from Lists to Vectors! --
---------------------------------------------------------------------------

---------------------------------------------------------------------------
--                                      head                             --
---------------------------------------------------------------------------

----------------------
-- 1. Haskell style --
----------------------

open import Data.Maybe

head' : ∀ {A} → List A → Maybe A
head' [] = nothing
head' (x ∷ _) = just x

----------------------
-- 2. Being Precise --
----------------------

head : ∀ {A n} → Vec A (suc n) → A
head (x ∷ _) = x

---------------------------------------------------------------------------
--                                      tail                             --
---------------------------------------------------------------------------

----------------------
-- 1. Haskell Style --
----------------------

tail' : ∀ {A} → List A → Maybe (List A)
tail' [] = nothing
tail' (_ ∷ xs) = just xs

----------------------
-- 2. Being Precise --
----------------------

tail : ∀ {A n} → Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs
