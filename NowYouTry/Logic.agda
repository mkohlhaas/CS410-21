module NowYouTry.Logic where

{-

Traditional programming languages:

---------------------        ---------------------
|                   |        |                   |
|      Program      |        |   Specification   |
|                   |        |                   |
---------------------        ---------------------
    In computer                    On paper

Dependently typed programming languages:

   ---------------------------------------
   |                                     |
   |      Program   :    Specification   |
   |                                     |
   ---------------------------------------
                   In computer

-}

-- For this to work, we need to represent specifications = logical formulua in our language.

----------------------------------------------------------------------
-- Propositions-as-booleans?
----------------------------------------------------------------------

{-

First thought: use Bool, ie say that a proposition is either true or false.

-}

data Bool : Set where -- can be found in Data.Bool
  false true : Bool

-- We can define e.g. `and` by pattern matching:

_&_ : Bool → Bool → Bool
false & y = false
true & y = y

-- But how do we represent e.g. `(∀ n : ℕ) P(n)`?

-- Problem: with Propositions = Bool, we can only represent decidable properties.

----------------------------------------------------------------------
-- Propositions-as-types
----------------------------------------------------------------------

-- What is a proposition? Something which might have a proof.

-- Leap: identify a proposition with its "set" of proofs, i.e.

Proposition = Set

-- PROOFS = PROGRAMS

{-

In Haskell:

Algebra | Logic   | Haskell Type   | Agda Type      | Comment
--------+---------+---------------------------------------------
a + b   | a ∨ b   | Either a b     | ⊎ (union)      | any sum type
a × b   | a ∧ b   | (a, b) (tuple) | × (tuple)      | any product type
bᵃ      | a ⇒ b   | a → b          | a → b          |
a = b   | a ⇐⇒ b  | isomorphism    | isomorphism    | from . to = to . from = id
0       | ⊥       | Void           | ⊥              | empty type
1       | ⊤       | ()             | ⊤              | unit type

-}

----------------
-- Implication
----------------

-- Q: What is a proof of `A ⇒ B`?

-- A: A method for converting proofs of A into proofs of B -- a function!

_⇒_ : Set → Set → Set
A ⇒ B = A → B

-- A ⇒ A
I : {A : Set} → A → A
I a = a


-- ((A → B → C) → D) ⇒ (A → C) → D
ex1 : {A B C D : Set} → ((A → B → C) → D) → (A → C) → D
ex1 f g = f (λ a b → g a)

----------------
-- Conjunction
----------------

-- Q: What is a proof of `A ∧ B`?

-- A: A proof of A and a proof of B -- a tuple!

open import Data.Product

_∧_ : Set → Set → Set
A ∧ B = A × B

ex2 : {A B : Set} → A × B → A
ex2 (fst , snd) = fst

ex2' : {A B : Set} → A × B → A
ex2' = proj₁

ex3 : {A : Set} → A → A × A
ex3 a = (a , a)

----------------
-- True and False
----------------

-- the empty type represents a false proposition

open import Data.Empty

ex4 : {B : Set} → ⊥ → B
ex4 ()

-- ex4 = ⊥-elim
-- ⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
-- ⊥-elim ()

-- the unit type represents a true proposition

open import Data.Unit

ex5 : {B : Set} → B → ⊤
ex5 b = tt

-- use Agda's inferrence
ex5' : {B : Set} → B → ⊤
ex5' b = _

-- normalizing `test` (C-c C-n) yields: tt
--            B        b
--            |        |
--         |-----| |-------|
test = ex5 {⊤ → ⊤} (λ x → x)

----------------
-- Disjunction
---------------

-- Q: What is a proof of `A ∨ B`?

-- A: A proof of A, or a proof of B -- a disjoint union

open import Data.Sum

_∨_ : Set → Set → Set
A ∨ B = A ⊎ B

ex6 : {A B : Set} → A ⊎ B → B ⊎ A
ex6 (inj₁ a) = inj₂ a
ex6 (inj₂ b) = inj₁ b

----------------
-- Negation
----------------

-- Q: What is a proof of `¬ A`?

-- A: A method to show that all proofs of A are impossible -- A FUNCTION `A → ⊥`

¬_ : Set → Set
¬ A = A → ⊥

ex7 : ¬ (⊤ → ⊥)
ex7 ⊤→⊥ = ⊤→⊥ tt

explosion : {A B : Set} → A → ¬ A → B
explosion a ¬a = ⊥-elim (¬a a)

explosion' : {A B : Set} → A → ¬ A → B
explosion' a ¬a with ¬a a
... | ()

-- Now you try:
materialImplication : {A B : Set} → (¬ A ⊎ B) → (A → B)
materialImplication (inj₁ ¬a) a = ⊥-elim (¬a a)
materialImplication (inj₂  b) _ = b

-- what about `(A → B) → (¬ A ⊎ B)`?
-- not possible; there is no a ∈ A to apply to f
materialImplicationInv : {A B : Set} → (A → B) → (¬ A ⊎ B)
materialImplicationInv f = {!!}
