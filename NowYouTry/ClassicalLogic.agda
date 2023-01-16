module NowYouTry.ClassicalLogic where

open import Data.Sum
open import Data.Empty
open import Relation.Nullary

---------------------------------------
-- Classical principles: LEM and DNE --
---------------------------------------

----------------------------
-- Law of Excluded Middle --
----------------------------

LEM : Set1
LEM = {P : Set} → P ⊎ ¬ P

-- lem : LEM                        -- Not provable in Agda! If it was we could solve the halting problem!
-- lem {P} = {!!}                   -- press C-u C-u C-c C-,

-- lem : LEM
-- lem = inj₁ {!!}                  -- Goal: P (we don't a value of type P)
-- lem {P} = inj₂ (λ p → {!!})      -- Goal: ⊥ (we cannot create a value of type ⊥)

---------------------------------
-- Double Negation Elimination --
---------------------------------

DNE : Set1
DNE = {P : Set} → ¬ ¬ P → P

-- `¬ ¬ P` means: P is not impossible.

-- dne : DNE                        -- Seems to be not provable in Agda either!
-- dne {P} ¬¬p = {!!}               -- press C-u C-u C-c C-,

-- This proves that DNE is as unimplementable as LEM. (LEM implies DNE.)
LEM→DNE : LEM → DNE
LEM→DNE lem {P} ¬¬p with lem {P}
LEM→DNE lem {P} ¬¬p | inj₁  p = p
LEM→DNE lem {P} ¬¬p | inj₂ ¬p = ⊥-elim (¬¬p ¬p)

LEM→DNE' : LEM → DNE
LEM→DNE' lem ¬¬p with lem
... | inj₁  p = p
... | inj₂ ¬p = ⊥-elim (¬¬p ¬p)

LEM→DNE'' : LEM → DNE
LEM→DNE'' lem ¬¬p with lem
... | inj₁  p = p
... | inj₂ ¬p with (¬¬p ¬p)
... | ()

-----------------
-- Now you try --
-----------------

-- Hint: You probably want to make your first move `dne`.

-- This proves that LEM is as unimplementable as DNE. (DNE implies LEM.)
DNE→LEM : DNE → LEM
DNE→LEM dne = dne (λ ¬lem → ¬lem (inj₂ (λ p → ¬lem (inj₁ p))))
