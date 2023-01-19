-- {-# OPTIONS --without-K #-}

module NowYouTry.MoreEquality where

open import Data.List                             hiding (reverse)
open import Data.Nat                              using (ℕ; zero; suc)
open import Data.Product
open import Data.Vec                              hiding (reverse; _++_; [_])
open import Lectures.Equality
open import Relation.Binary.PropositionalEquality hiding (cong; sym; trans; subst; [_])

------------------------------------------------------------------
--             Equality is an Equivalence Relation              --
------------------------------------------------------------------

-- Equivalence ⇔  Relation Reflexivity, Symmetry, Transitivity

-----------------
-- Reflexivity --
-----------------

-- (_≡_) is reflexive by design.

--------------
-- Symmetry --
--------------

sym : {A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

------------------
-- Transitivity --
------------------

trans : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- not looking into `p`
-- trans refl p = p

--------------------------------------------
-- Additional property - Substitutability --
--------------------------------------------

-- All properties respect equality.
-- Replace P (for Predicate or Property) by `px` if equality holds for component of P.
-- `cong` is for any function `A → B`.
subst : {A : Set}{x y : A} → (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

{- What have we learnt?
   1. Equality is an equivalence relation.
   2. We can substitute equal things for equal things. -}

-----------------------
-- Reversing Vectors --
-----------------------

-- We can reverse Lists naively (complexity O(n²)).
revList : {A : Set} → List A → List A
revList [] = []
revList (x ∷ xs) = revList xs ++ [ x ]

-- This works the same for Vectors.

-- We can reverse Lists in a fast way (complexity O(n)) with an accumulator.
revListFast : {A : Set} → List A → List A → List A
revListFast acc [] = acc
revListFast acc (x ∷ xs) = revListFast (x ∷ acc) xs

-- Let's do the same for Vectors!

-- with `rewrite`
-- revAcc : {A : Set}{n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
-- revAcc {A} {n} acc [] rewrite (+-identity-right n)= acc                          -- works
-- revAcc {A} {n} {m} acc (x ∷ xs) rewrite (+suc n m) = {! (revAcc (x ∷ acc) xs)!}  -- does not work!!!

-- with `subst`
revAcc : {A : Set}{n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
revAcc {A} acc [] = subst (Vec A) (sym (+-identity-right _)) acc
revAcc {A} acc (x ∷ xs) = subst (Vec A) (sym (+suc _ _)) (revAcc (x ∷ acc) xs)

reverse : {A : Set}{m : ℕ} → Vec A m → Vec A m
reverse = revAcc []

test = reverse (1 ∷ 2 ∷ 3 ∷ [])

{- What have we learnt?
   1. We can use `subst` to "fix up" types that are not definitionally equal.
   2. In certain situations, we can also use `rewrite`.
      - `subst`   works every single time
      - `rewrite` works half  of the time -}

---------------------------
-- Structural Equalities --
---------------------------

-- Some syntax for displaying the type the equality is at.
-- x ≡ y at type A
-- We are just making the type A explicit.
≡-syntax : (A : Set) → (x y : A) → Set
≡-syntax A x y = _≡_ {A = A} x y

-- `x` and `y` are equal at type `A`
syntax ≡-syntax A x y = x ≡[ A ] y

-------------------------------
-- When are Two Pairs Equal? --
-------------------------------

-- `pair` is a non-dependent pair.
pair-≡ : {A B : Set} {a a' : A}{b b' : B} →
         a ≡[ A ] a' → b ≡[ B ] b' → (a , b) ≡[ A × B ] (a' , b')
      -- the same: (We just made the type explicit.)
      -- a ≡[ A ] a' → b ≡[ B ] b' → (a , b) ≡ (a' , b')
pair-≡ refl refl = refl

-------------------------------------
-- When are Dependent Pairs Equal? --
-------------------------------------

-- B depends on A                           it's a dependent pair
--                                              ‸‸‸‸      ‸‸‸‸‸
dpair-≡ : {A : Set}{B : A → Set} {a a' : A}{b : B a}{b' : B a'} →
      -- (a ≡[ A ] a') → ? ≡[ B a' ] ? →
      -- (a ≡[ A ] a') → ? ≡[ B a  ] ? →
         (p : a ≡[ A ] a') → subst B p b ≡[ B a' ] b' →
         (a , b) ≡[ Σ A B ] (a' , b')
dpair-≡ refl refl = refl

-------------------------------
-- When are Functions Equal? --
-------------------------------

-- Not provable in Agda, so we postulate.
-- extensional equality
postulate funext : {A : Set}{B : A → Set}{f f' : (x : A) → B x} → ((x : A) → f x ≡[ B x ] f' x) → f ≡ f'

-------------------------------------
-- When are Equality Proofs Equal? --
-------------------------------------

-- Uniqueness of Identity Proofs (UIP).
-- Equivalently known as "Axiom K" (I for Identity, then J, then K)

-- By refuting Axiom K - {-# OPTIONS --without-K #-} - we can get new models with interesting properties.
-- This is known as "Homotopy Type Theory" and related to "Cubical Agda".

-- If `x` equal `y` in `A` then equality proof `p` is equal to equality proof `q`.
UIP : {A : Set}{x y : A}(p q : x ≡[ A ] y) → p ≡[ (x ≡ y) ] q
UIP refl refl = refl

-----------------
-- Now you try --
-----------------

-- Use the combinators above and the lemmas from `Lectures.Equality` to
-- prove the following slightly contrived equality:

-- the easy way
aBitContrived' : (n m : ℕ) →
                 (n + m , 16 , λ xs → m ∷ xs) ≡[ ℕ × (Σ[ k ∈ ℕ ] (Vec ℕ k → Vec ℕ (suc k))) ] (m + n , 4 * 4 , λ xs → m + 0 ∷ xs)
aBitContrived' n m rewrite +-comm n m | +-identity-right m = refl

-- TODO
aBitContrived : (n m : ℕ) →
                (n + m , 16 , λ xs → m ∷ xs) ≡[ ℕ × (Σ[ k ∈ ℕ ] (Vec ℕ k → Vec ℕ (suc k))) ] (m + n , 4 * 4 , λ xs → m + 0 ∷ xs)
aBitContrived zero zero = refl
aBitContrived zero (suc m) = pair-≡ (cong suc (sym (+-identity-right m))) (dpair-≡ refl (funext (λ x → {!!})))
aBitContrived (suc n) zero = pair-≡ (cong suc (+-identity-right n)) (dpair-≡ refl refl)
aBitContrived (suc n) (suc m) = pair-≡ (cong suc {!!}) (dpair-≡ refl (funext {!!}))

-- +-identity-right : (n : ℕ) → n + 0 ≡ n
-- +suc
-- n + suc m ≡ m + suc n

+1 : (n : ℕ) → suc n ≡ n + 1
+1 zero = refl
+1 (suc n) = cong suc (+1 n)

+sucsuc : (n m : ℕ) → n + suc m ≡ m + suc n
+sucsuc zero zero = refl
+sucsuc zero (suc m) = cong suc (+1 m)
+sucsuc (suc n) m = {!!}
