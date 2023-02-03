module NowYouTry.Equality where

--------------------------------------
-- The natural numbers to play with --
--------------------------------------

open import Data.Nat using (ℕ; suc; zero)

_+_ : ℕ → ℕ → ℕ
zero +  m = m
suc n + m = suc (n + m)

infixl 6 _+_

--------------
-- Equality --
--------------

open import Relation.Binary.PropositionalEquality hiding (cong)

+-identity-left : (n : ℕ) → 0 + n ≡ n
+-identity-left n = refl

-- "congruence": Every function respects equality.
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong _ refl = refl

+-identity-right : (n : ℕ) → n + 0 ≡ n
+-identity-right zero    = refl
+-identity-right (suc n) = cong suc (+-identity-right n)

+-idʳ : (n : ℕ) → n + 0 ≡ n
+-idʳ zero    = refl
+-idʳ (suc n) = cong suc (+-idʳ n)

+suc : (n m : ℕ) → n + suc m ≡ suc (n + m)
+suc zero    m = refl
+suc (suc n) m = cong suc (+suc n m)

+-sucʳ : (n : ℕ) → (m : ℕ) → n + suc m ≡ suc (n + m)
+-sucʳ zero    m = refl
+-sucʳ (suc n) m = cong suc (+-sucʳ n m)


{- What have we learnt?
1. Use `refl` to prove obvious equations.
2. "Why is it stuck?" -- follow same pattern in proof as in definition.
3. Use `cong f` to "peel off" `f` from both sides. -}

---------------
-- Rewriting --
---------------

-- using `cong`
+-assoc' : (n m k : ℕ) → ((n + m) + k) ≡ (n + (m + k))
+-assoc' zero    m k = refl
+-assoc' (suc n) m k = cong suc (+-assoc' n m k)

-- using `rewrite`
-- rewriting the recursion
+-assoc : (n m k : ℕ) → ((n + m) + k) ≡ (n + (m + k))
+-assoc zero    m k = refl
+-assoc (suc n) m k rewrite +-assoc n m k = refl

-- What happened? How does it work?

-- Rewrite means to replace the lhs with the rhs of an equality *everywhere* (no matter how deeply nested)
example : {A : Set}{f : A → A}{P : A → A → A → Set}
          (lhs rhs x : A) →
          (eq : lhs ≡ rhs) → P rhs (f lhs) x → P lhs (f lhs) x
example lhs rhs a eq p rewrite eq = p

-----------------------
-- Multiple Rewrites --
-----------------------

+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm n zero = +-idʳ n
+-comm n (suc m) rewrite +suc n m | +-comm n m = refl

+-comm' : (n m : ℕ) → n + m ≡ m + n
+-comm' n zero    = +-idʳ n
+-comm' n (suc m) = trans (+suc _ _) (cong suc (+-comm' n m))

+-comm'' : (n m : ℕ) → n + m ≡ m + n
+-comm'' n zero = +-idʳ _
+-comm'' n (suc m) with m + n | +-comm'' n m
... | .(n + m) | refl = +suc _ _

{- What have we learnt?
Use `rewrite` with a proof of an equality to change the context and the goal.
Aside: rewrite is not magic; see if you can do the same thing using `with` only. -}

--------------------------
-- Equational Reasoning --
--------------------------

_*_ : ℕ → ℕ → ℕ
zero  * m = zero
suc n * m = m + (n * m) -- (1)

infixl 7 _*_

open ≡-Reasoning

*-distribʳ-+ : (m n o : ℕ) → (n + o) * m ≡ n * m + o * m
*-distribʳ-+ m zero    o = refl
*-distribʳ-+ m (suc n) o = begin
  (suc  n + o) * m      ≡⟨⟩                                   -- definition of addition (`≡⟨ refl ⟩` ↔ `≡⟨⟩`)
   suc (n + o) * m      ≡⟨⟩                                   -- definition of multiplication (1)
   m + (n + o) * m      ≡⟨ cong (m +_) (*-distribʳ-+ m n o) ⟩ -- distribution
   m + (n * m  + o * m) ≡˘⟨ +-assoc m (n * m) (o * m) ⟩       -- associativity of addition
  (m +  n * m) + o * m  ≡⟨⟩                                   -- definition of multiplication (1)
   suc n * m + o * m    ∎

{- What have we learnt?

1. `open ≡-Reasoning` to get access to `begin`, `≡⟨ ⟩`, `≡⟨⟩`, `∎`, `≡˘` for equational reasoning.
2. Allows working on equations step by step - from both directions! -}

-----------------
-- Now you try --
-----------------

-- Hint: You will need to use two facts we have proven above (one backwards).

*-assoc : (n m k : ℕ) → n * (m * k) ≡ (n * m) * k
*-assoc zero m k = refl
*-assoc (suc n) m k = begin
  suc n * (m * k)     ≡⟨⟩                                     -- definition of multiplication (1)
  m * k + n * (m * k) ≡⟨ cong ((m * k) +_) (*-assoc n m k) ⟩  -- associativity of multiplication
  m * k + (n * m) * k ≡˘⟨ *-distribʳ-+ k m (n * m) ⟩          -- distributivity
  (m + (n * m)) * k   ≡⟨⟩                                     -- definition of multiplication (1)
  (suc n * m) * k     ∎
