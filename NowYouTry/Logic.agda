module NowYouTry.Logic where

-- Traditional programming languages:

-- ---------------------        ---------------------
-- |                   |        |                   |
-- |      Program      |        |   Specification   |
-- |                   |        |                   |
-- ---------------------        ---------------------
--     In computer                    On paper
--
-- Dependently typed programming languages:
--
--    ---------------------------------------
--    |                                     |
--    |      Program   :    Specification   |
--    |                                     |
--    ---------------------------------------
--                    In computer

-- For this to work, we need to represent specifications = logical formulua in our language.

--------------------------------
-- Propositions as Booleans ? --
--------------------------------

-- First thought: use Bool, ie say that a proposition is either true or false.

data Bool : Set where -- can be found in Data.Bool
  false true : Bool

-- We can define e.g. `and` by pattern matching:

_&_ : Bool → Bool → Bool
false & y = false
true & y = y

-- But how do we represent e.g. `(∀ n : ℕ) P(n)`?

-- Problem: with Propositions = Bool, we can only represent decidable properties.

---------------------------
-- Propositions as Types --
---------------------------

-- What is a proposition? Something which might have a proof.

-- Leap: identify a proposition with its "set" of proofs, i.e.

Proposition = Set

-- PROOFS = PROGRAMS

--   Algebra | Logic   | Haskell Type   | Agda Type      | Comment
--   --------+---------+---------------------------------------------
--   a + b   | a ∨ b   | Either a b     | ⊎ (union)      | any sum type
--   a × b   | a ∧ b   | (a, b) (tuple) | × (tuple)      | any product type
--   bᵃ      | a ⇒ b   | a → b          | a → b          | implication
--   a = b   | a ⇐⇒ b  | isomorphism    | isomorphism    | from . to = to . from = id
--   0       | ⊥       | Void           | ⊥              | empty type
--   1       | ⊤       | ()             | ⊤              | unit type

-----------------
-- Implication --
-----------------

-- Q: What is a proof of `A ⇒ B`?
-- A: A method for converting proofs of A into proofs of B -- a function!

_⇒_ : Set → Set → Set
A ⇒ B = A → B

I : {A : Set} → A → A
I a = a

-- `b` is not used in the function given to `f`
ex1 : {A B C D : Set} → ((A → B → C) → D) → (A → C) → D
ex1 f g = f (λ a _ → g a)

-----------------
-- Conjunction --
-----------------

-- Q: What is a proof of `A ∧ B`?
-- A: A proof of A and a proof of B -- a tuple (pair), a product type!

open import Data.Product

-- `×` is a non-dependent product type
-- `Σ` is a     dependent product type
_∧_ : Set → Set → Set
A ∧ B = A × B

ex2 : {A B : Set} → A × B → A
ex2 (fst , _) = fst

ex2' : {A B : Set} → A × B → A
ex2' = proj₁

ex3 : {A : Set} → A → A × A
ex3 a = (a , a)

--------------------
-- True and False --
--------------------

-- The empty type represents a False proposition.
open import Data.Empty

-- `()` is the absurd pattern - cannot happen!
-- Logic breaks down and you can prove anything!
ex4 : {A : Set} → ⊥ → A
ex4 ()

-- ex4 = ⊥-elim
-- ⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
-- ⊥-elim ()

-- The unit type represents a True proposition.
open import Data.Unit

ex5 : {A : Set} → A → ⊤
ex5 a = tt

-- using Agda's inferrence
ex5' : {A : Set} → A → ⊤
ex5' a = _

-- normalizing `test` (C-c C-n) yields: tt
--             A        a
--             |        |
--          |-----| |-------|
test2 = ex5 {⊤ → ⊤} (λ x → x)

-----------------
-- Disjunction --
-----------------

-- Q: What is a proof of `A ∨ B`?
-- A: A proof of A, or a proof of B → disjoint union type, sum type.

open import Data.Sum

_∨_ : Set → Set → Set
A ∨ B = A ⊎ B

ex6 : {A B : Set} → A ⊎ B → B ⊎ A
ex6 (inj₁ a) = inj₂ a
ex6 (inj₂ b) = inj₁ b

--------------
-- Negation --
--------------

-- Q: What is a proof of `¬ A`?
-- A: A method to show that all proofs of A are impossible → function `A → ⊥`

¬_ : Set → Set
¬ A = A → ⊥

ex7 : ¬ (⊤ → ⊥)
ex7 ⊤→⊥ = ⊤→⊥ tt

-- Logic breaks down and we can prove anything.
-- If you believe A and ¬ A are true then you believe anything.
explosion : {A B : Set} → A → ¬ A → B
explosion a ¬a = ⊥-elim (¬a a)

explosion' : {A B : Set} → A → ¬ A → B
explosion' a ¬a with ¬a a
... | ()

-- Now you try:
materialImplication : {A B : Set} → (¬ A ⊎ B) → (A → B)
materialImplication (inj₁ ¬a) a = ⊥-elim (¬a a)
materialImplication (inj₂  b) _ = b

-- What about `(A → B) → (¬ A ⊎ B)`?
-- materialImplicationInv : {A B : Set} → (A → B) → (¬ A ⊎ B)
-- materialImplicationInv f = inj₁ (λ a → {!!}) -- Goal: ⊥ (not possible)
-- materialImplicationInv f = inj₂ (f {!!})     -- Goal: A (don't have an A)
