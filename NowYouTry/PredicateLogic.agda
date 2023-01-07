module NowYouTry.PredicateLogic where

open import Data.Nat -- ℕ \bN

open import Data.Unit
open import Data.Empty
open import Data.Product hiding (curry; uncurry)
open import Data.Sum
open import Relation.Nullary

-- Propositional logic: A and B implies C
-- Predicate logic:     (isMan(x) implies isMortal(x)) and isMan(Socrates)

----------------------------------------------------------------------
--                 Predicates in Type Theory                        --
----------------------------------------------------------------------

-- What is a predicate (on natural numbers, say)?

Pred : Set → Set1
Pred A = A → Set

isEven : ℕ → Set
isOdd  : ℕ → Set

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

_>1 : ℕ → Set
zero >1 = ⊥
suc zero >1 = ⊥
suc (suc n) >1 = ⊤

_<3 : ℕ → Set
zero <3 = ⊤
suc zero <3 = ⊤
suc (suc zero) <3 = ⊤
suc (suc (suc n)) <3 = ⊥

fact : 1 <3 × 2 >1
fact = _

----------------------------------------------------------------------
-- Quantifiers (∀, ∃)
----------------------------------------------------------------------

-------------------------------
-- Universal quantification ∀
-------------------------------

-- Q: What is a proof of (∀ x : A) P(x)?

-- A: A method which produces a proof of `P(a)` for any given `a : A` -- A DEPENDENT FUNCTION!

∀' : (A : Set) → (P : A → Set) → Set
∀' A P = (x : A) → P x

-- Note: `A ⇒ B` is "just" (_ : A) → B
-- Implication is just ∀ where B does not depend on A.

ex8  : (n : ℕ) → isEven n ⊎ isEven (suc n)
ex8' : (n : ℕ) → isOdd  n ⊎ isOdd  (suc n)

ex8 zero = inj₁ tt
ex8 (suc n) = ex8' n

ex8' zero = inj₂ tt
ex8' (suc n) = ex8 n

-- ex8 zero = inj₁ tt
-- ex8 (suc zero) = inj₂ tt
-- ex8 (suc (suc n)) = ex8 n

---------------------------------
-- Existential quantification ∃
---------------------------------

-- Q: What is a proof of (∃ x : A) P(x)?

-- A: A choice of `a : A` and a proof of `P(a)` -- A DEPENDENT TUPLE!

∃' : (A : Set) → (P : A → Set) → Set
∃' A P = Σ[ x ∈ A ] (P x)

-- Note: A × B is "just" Σ[ _ ∈ A ] B
-- Conjunction is just ∃ where B does not depend on A.

ex9 : Σ ℕ isEven
ex9 = (4 , tt)

-- ((∃ x : A)  P(x))        → Q  is the same as (1)
--  (∀ x : A)        (P(x)  → Q) and vice versa (2)

-- proof of (1)
curry : {A : Set}{P : A → Set}{Q : Set} → ((Σ[ x ∈ A ] (P x)) → Q) → ((x : A) → (P x → Q))
curry f a p = f (a , p)

-- proof of (2)
uncurry : {A : Set}{P : A → Set}{Q : Set} → ((x : A) → (P x → Q)) → ((Σ[ x ∈ A ] (P x)) → Q)
uncurry f (a , p) = f a p

-- Now you try

axiomOfChoice : {A B : Set}{R : A → B → Set} →
                  ((a : A) → Σ[ b ∈ B ] (R a b)) →
                  (Σ[ f ∈ (A → B) ] ((a : A) → R a (f a)))
axiomOfChoice f = (λ a → proj₁ (f a)) , (λ a → proj₂ (f a))
