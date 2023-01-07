module NowYouTry.ClassicalLogic where

open import Data.Sum
open import Data.Empty
open import Relation.Nullary

-- Law of Excluded Middle

LEM : Set1
LEM = {P : Set} → P ⊎ ¬ P

lem : LEM
lem {P} = {!!} -- press C-u C-u C-c C-,

{-
lem : LEM -- Not provable! If it was we could solve the halting problem.
lem {P} = {!!}
-}

-- Double Negation Elimination

DNE : Set1
DNE = {P : Set} → ¬ ¬ P → P

dne : DNE -- Seems to be not provable either!
dne {P} ¬¬p = {!!} -- press C-u C-u C-c C-,

{-
dne : DNE -- Not provable!
dne {P} ¬¬p = {!!}
-}

-- these are classical principles

-- This prooves that LEM is as unimplementable as DNE.
LEM→DNE : LEM → DNE
LEM→DNE lem {P} ¬¬p with lem {P}
LEM→DNE lem {P} ¬¬p | inj₁  p = p
LEM→DNE lem {P} ¬¬p | inj₂ ¬p = ⊥-elim (¬¬p ¬p)

LEM→DNE' : LEM → DNE
LEM→DNE' lem ¬¬p with lem
... | inj₁  p = p
... | inj₂ ¬p = ⊥-elim (¬¬p ¬p)

-- Now you try
-- Hint: You probably want to make your first move `dne`.

-- This prooves that DNE is as unimplementable as LEM.
DNE→LEM : DNE → LEM
DNE→LEM dne = dne (λ ¬lem → ¬lem (inj₂ (λ p → ¬lem (inj₁ p))))

-- DNE→LEM' : DNE → LEM
-- DNE→LEM' dne {P} = dne {P ⊎ ¬ P} (λ ¬lem → ¬lem (inj₂ (λ p → ¬lem (inj₁ p))))
