module NowYouTry.BeingPrecise where

open import Agda.Builtin.Nat

---------------
-- datatypes --
---------------

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc : ∀ {n} → Fin n → Fin (suc n)

----------------
-- index (!!) --
----------------

-- _!!_ : ∀ {A} → List A → Nat → A
-- [] !! n = {!!}                         -- cannot return something from an empty list
-- (x ∷ xs) !! zero = x
-- (x ∷ xs) !! suc n = xs !! n

-- open import Data.Maybe
--
-- works but clumsy because we will always get back a Maybe
-- _!!_ : ∀ {A} → List A → Nat → Maybe A
-- [] !! n = nothing
-- (x ∷ xs) !! zero = just x
-- (x ∷ xs) !! suc n = xs !! n

_!!_ : ∀ {A n} → Vec A n → Fin n → A
(x ∷ xs) !! zero = x
(x ∷ xs) !! suc n = xs !! n

index : ∀ {A n} → Vec A n → Fin n → A
index (x ∷ _) zero = x
index (_ ∷ xs) (suc n) = index xs n

------------------------------------------------------------------------
-- Convert the Haskell head and tail functions from lists to vectors! --
------------------------------------------------------------------------

----------
-- head --
----------

-------------------
-- Haskell style --
-------------------

open import Data.Maybe

head' : ∀ {A} → List A → Maybe A
head' [] = nothing
head' (x ∷ _) = just x

-------------------
-- being precise --
-------------------

head : ∀ {A n} → Vec A (suc n) → A
head (x ∷ _) = x

----------
-- tail --
----------

-------------------
-- Haskell style --
-------------------

tail' : ∀ {A} → List A → Maybe (List A)
tail' [] = nothing
tail' (_ ∷ xs) = just xs

-------------------
-- being precise --
-------------------

tail : ∀ {A n} → Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs
