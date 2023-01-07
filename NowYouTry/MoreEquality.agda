-- {-# OPTIONS --without-K #-}
module NowYouTry.MoreEquality where

open import Data.Nat  using (ℕ; zero; suc)
open import Data.Vec  hiding (reverse; _++_; [_])
open import Data.List hiding (reverse)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (cong; sym; trans; subst; [_])
open import Lectures.Equality

-----------------------------------------
-- Equality is an Equivalence Relation --
-----------------------------------------

-- _≡_ is reflexive by design. What about symmetry and transitivity?

sym : {A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

-- looking into `q`
-- trans refl refl = refl

-- all properties respect equality
-- replace P by px if equality holds for component of P
subst : {A : Set}{x y : A} → (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

{-

What have we learnt?

1. Equality is an equivalence relation.
2. We can substitute equal things for equal things.

-}

-------------------------------------------
-- Reversing Vectors with an Accumulator --
-------------------------------------------

-- we can reverse lists naively (complexity O(n²))
revList : {A : Set} → List A → List A
revList [] = []
revList (x ∷ xs) = revList xs ++ [ x ]

-- This works the same for vectors (try it!).

-- we can also reverse lists in a fast way (complexity O(n))
revListFast : {A : Set} → List A → List A → List A
revListFast acc [] = acc
revListFast acc (x ∷ xs) = revListFast (x ∷ acc) xs

-- Let's do the same for vectors!
revAcc : {A : Set}{n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
revAcc {A} acc [] = subst (Vec A) (sym (+-identity-right _)) acc
revAcc {A} acc (x ∷ xs) = subst (Vec A) (sym (+suc _ _)) (revAcc (x ∷ acc) xs)

reverse : {A : Set}{m : ℕ} → Vec A m → Vec A m
reverse = revAcc []

test = reverse (1 ∷ 2 ∷ 3 ∷ [])

{-

What have we learnt?

1. We can use subst to "fix up" types that are not definitionally equal.
2. In certain situations, we can also use rewrite.
   - `subst`   works every single time
   - `rewrite` works half  of the time

-}

---------------------------
-- Structural Equalities --
---------------------------

-- Some syntax for displaying the type the equality is at.
≡-syntax : (A : Set) → (x y : A) → Set
≡-syntax A x y = _≡_ {A = A} x y

-- `x` and `y` are equal at type `A`
syntax ≡-syntax A x y = x ≡[ A ] y

-------------------------------
-- When are Two Pairs Equal? --
-------------------------------

pair-≡ : {A B : Set} {a a' : A}{b b' : B} →
         a ≡[ A ] a' → b ≡[ B ] b' → (a , b) ≡[ A × B ] (a' , b')
pair-≡ refl refl = refl

-------------------------------------
-- When are Dependent Pairs Equal? --
-------------------------------------

-- B depends on A
dpair-≡ : {A : Set}{B : A → Set} {a a' : A}{b : B a}{b' : B a'} →
         (p : a  ≡[ A ] a') → subst B p b ≡[ B a' ] b' →
         (a , b) ≡[ Σ A B ] (a' , b')
dpair-≡ refl refl = refl

-------------------------------
-- When are Functions Equal? --
-------------------------------

-- Not provable, so we postulate.
postulate
  funext : {A : Set}{B : A → Set}{f f' : (x : A) → B x} → ((x : A) → f x ≡[ B x ] f' x) → f ≡ f'

-------------------------------------
-- When are Equality Proofs Equal? --
-------------------------------------

-- "uniqueness of identity proofs"
-- Equivalently known as "Axiom K" (I for Identity, then J, then K)

-- By refuting Axiom K - {-# OPTIONS --without-K #-} - we can get
-- new models with interesting properties; this is known as
-- "Homotopy Type Theory" and related to "Cubical Agda".

-- If `x` equal `y` in `A` then equality proof `p` is equal to equality proof `q`.
UIP : {A : Set}{x y : A}(p q : x ≡[ A ] y) → p ≡[ (x ≡ y) ] q
UIP refl refl = refl

-----------------
-- Now you try --
-----------------

-- Use the combinators above and the lemmas from Lectures.Equality to
-- prove the following slightly contrived equality:

aBitContrived : (n m : ℕ) → (n + m , 16 , λ xs → m ∷ xs) ≡[ ℕ × (Σ[ k ∈ ℕ ] (Vec ℕ k → Vec ℕ (suc k))) ] (m + n , 4 * 4 , λ xs → m + 0 ∷ xs)
aBitContrived n m rewrite +-comm n m | +-identity-right m = refl 
