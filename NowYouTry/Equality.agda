module NowYouTry.Equality where

--------------------------------------
-- The natural numbers to play with --
--------------------------------------

open import Data.Nat using (ℕ; suc; zero)

_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

infixl 6 _+_

--------------
-- Equality --
--------------

open import Relation.Binary.PropositionalEquality hiding (cong)

+-identity-left : (n : ℕ) → 0 + n ≡ n
+-identity-left n = refl

-- "congruence"; every function respects equality
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

+-identity-right : (n : ℕ) → n + 0 ≡ n
+-identity-right zero = refl
+-identity-right (suc n) = cong suc (+-identity-right n)

+suc : (n m : ℕ) → n + suc m ≡ suc (n + m)
+suc zero m = refl
+suc (suc n) m = cong suc (+suc n m)

{-

What have we learnt?

1. Use `refl` to prove obvious equations.
2. "Why is it stuck?" -- follow same pattern in proof as in definition.
3. Use `cong f` to "peel off" `f` from both sides.

-}

---------------
-- Rewriting --
---------------

+-assoc : (n m k : ℕ) → ((n + m) + k) ≡ (n + (m + k))
+-assoc zero m k = refl
+-assoc (suc n) m k rewrite +-assoc n m k = refl

-- What happened?

example : {A : Set}{f : A → A}{P : A → A → A → Set}
          (lhs rhs x : A) ->
          (eq : lhs ≡ rhs) → P rhs (f lhs) x → P lhs (f lhs) x
example lhs rhs x eq p rewrite eq = p

-- "replace all occurrences of lhs with rhs in the goal and the context"

-----------------------
-- Multiple rewrites --
-----------------------

+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm n zero = +-identity-right n
+-comm n (suc m) rewrite +suc n m | +-comm n m = refl

{-

What have we learnt?

1. Use rewrite with a proof of an equality to change the goal.

Aside: rewrite is not magic; see if you can do the same thing using `with` only.

-}

--------------------------
-- Equational Reasoning --
--------------------------

_*_ : ℕ → ℕ → ℕ
zero * m = zero
suc n * m = m + (n * m) -- (1)

infixl 7 _*_

open ≡-Reasoning

*-distribʳ-+ : (m n o : ℕ) → (n + o) * m ≡ n * m + o * m
*-distribʳ-+ m zero o = refl
*-distribʳ-+ m (suc n) o =
  begin
    ((suc n + o) * m)
  ≡⟨⟩ -- definition of multiplication (1)
    (m + (n + o) * m)
  ≡⟨ cong (m +_) (*-distribʳ-+ m n o) ⟩ -- distributivity
    (m + (n * m + o * m))
  ≡˘⟨ +-assoc m (n * m) (o * m) ⟩ -- associativity
    (m + n * m) + (o * m)
  ≡⟨⟩
    (suc n * m) + (o * m)
  ∎

{-

What have we learnt?

1. open ≡-Reasoning to get access to `begin`, `≡⟨` `⟩`, `≡⟨⟩`, `∎`, `≡˘`.
2. Can work on equations step by step (from both directions).

-}

-----------------
-- Now you try --
-----------------

-- Hint: You will need to use two facts we have proven above (one backwards).

*-assoc : (n m k : ℕ) → n * (m * k) ≡ (n * m) * k
*-assoc zero m k = refl
*-assoc (suc n) m k =
  begin
    suc n * (m * k)
  ≡⟨⟩ -- definition of multiplication (1)
   (m * k) + (n * (m * k))
  ≡⟨ cong ((m * k) +_) (*-assoc n m k) ⟩ -- associativity
   (m * k) + (n * m) * k
  ≡˘⟨ *-distribʳ-+ k m (n * m) ⟩ -- distributivity
   suc n * m * k
  ∎
