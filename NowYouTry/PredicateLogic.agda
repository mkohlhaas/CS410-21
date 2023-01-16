module NowYouTry.PredicateLogic where

open import Data.Nat

open import Data.Unit
open import Data.Empty
open import Data.Product hiding (curry; uncurry)
open import Data.Sum
open import Relation.Nullary

-- Propositional logic: - zero-order logic
--                      - propositions which can be true or false,
--                      - relations between propositions: ∧, ∨, ...
--                      - implications (⇒)

-- Predicate logic:     - first-order logic (on top of zero-order logic),
--                      - quantifiers (∃, ∀)

----------------------------------------------------------------------
--                 Predicates in Type Theory                        --
----------------------------------------------------------------------

-- What is a predicate (e.g. on natural numbers)?

-- Set1 is the type of Set
Pred : Set → Set1
Pred A = A → Set

-- In most programming languages a predicate is a function from `a` to Bool:
-- a → Bool : A → Set
--            A → Set : Set → Set1

-- Bool will be represented by ⊤ (the Unit type) for true and ⊥ (the Empty type) for false.

isEven : Pred ℕ
isOdd  : Pred ℕ

isEven zero = ⊤
isEven (suc n) = isOdd n

isOdd zero = ⊥
isOdd (suc n) = isEven n

-- isEven zero = ⊤
-- isEven (suc zero) = ⊥
-- isEven (suc (suc n)) = isEven n

test : isEven 4
test = tt

test' : ¬ isEven 5
test' ⊥ = ⊥

-- test' ()

_>1 : Pred ℕ
zero >1 = ⊥
suc zero >1 = ⊥
suc (suc n) >1 = ⊤

_<3 : Pred ℕ
zero <3 = ⊤
suc zero <3 = ⊤
suc (suc zero) <3 = ⊤
suc (suc (suc n)) <3 = ⊥

fact : 1 <3 × 2 >1
fact = _

----------------------------------------------------------------------
--                        Quantifiers (∀, ∃)                        --
----------------------------------------------------------------------

--------------------------------
-- Universal quantification ∀ --
--------------------------------

-- Q: What is a proof of (∀ x : A) P(x)?

-- A: A method which produces a proof of `P(a)` for any given `a : A` -> dependent function!

∀' : (A : Set) → Pred A → Set
∀' A P = (x : A) → P x

-- Note: `A ⇒ B` is "just" (_ : A) → B
-- Implication is just ∀ where B does not depend on A (independent function).
-- i.e. we don't use `x : A` in the predicate.

-- Compare a pair which is a dependent pair Σ where the `a` is not used which makes it independent.

ex8  : (n : ℕ) → isEven n ⊎ isEven (suc n)
ex8' : (n : ℕ) → isOdd  n ⊎ isOdd  (suc n)

ex8 zero = inj₁ tt
ex8 (suc n) = ex8' n

ex8' zero = inj₂ tt
ex8' (suc n) = ex8 n

-- ex8 zero = inj₁ tt
-- ex8 (suc zero) = inj₂ tt
-- ex8 (suc (suc n)) = ex8 n

----------------------------------
-- Existential quantification ∃ --
----------------------------------

-- Q: What is a proof of (∃ x : A) P(x)?

-- A: A choice of `a : A` and a proof of `P(a)` -> dependent tuple (Σ)!

∃' : (A : Set) → Pred A → Set
∃' A P = Σ[ x ∈ A ] (P x)

-- Note: A × B is "just" Σ[ _ ∈ A ] B
-- Conjunction is just ∃ where B does not depend on A (= independent tuple/pair).

-- ex9 : Σ ℕ isEven
ex9 : ∃' ℕ isEven
ex9 = (4 , tt)

-- Notice the parentheses!
-- ((∃ x : A)  P(x))        → Q  is the same as ...         (1)
--  (∀ x : A)        (P(x)  → Q) ... and vice versa         (2)

-- ∀' : (A : Set) → Pred A → Set
-- ∀' A P = (x : A) → P x

-- Proof of (1):
-- curry : {A : Set}{P : A → Set}{Q : Set} → ((Σ[ x ∈ A ] (P x)) → Q) → ((x : A) → (P x → Q))
curry : {A : Set}{P : A → Set}{Q : Set} → (∃' A P → Q) → ((x : A) → (P x → Q))
curry f a p = f (a , p)

-- Proof of (2):
-- uncurry : {A : Set}{P : A → Set}{Q : Set} → ((x : A) → (P x → Q)) → ((Σ[ x ∈ A ] (P x)) → Q)
uncurry : {A : Set}{P : A → Set}{Q : Set} → ((x : A) → (P x → Q)) → (∃' A P → Q)
uncurry f (a , p) = f a p

-----------------
-- Now you try --
-----------------

-- TODO
axiomOfChoice : {A B : Set}{R : A → B → Set} →
                ((a : A) → Σ[ b ∈ B ] (R a b)) →
                (Σ[ f ∈ (A → B) ] ((a : A) → R a (f a)))
axiomOfChoice f = (λ a → proj₁ (f a)) , (λ a → proj₂ (f a))
