module NowYouTry.LessThan where

open import Data.Empty
open import Data.Nat            using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Sum
open import Data.Unit           using (⊤; tt)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

------------------------------------
-- Inductively Defined Predicates --
------------------------------------

module ByRecursion where

  -- In `Lectures.PredicateLogic`, we defined special cases of `<` by recursion.

  -- Here is the general definition:
  _≤_ : ℕ → ℕ → Set
  zero ≤ m = ⊤
  suc n ≤ zero = ⊥
  suc n ≤ suc m = n ≤ m

  -- It is easy to prove concrete instances ...
  2≤4 : 2 ≤ 4
  2≤4 = tt

  -- ... and to disprove concrete instances:
  ¬12≤3 : ¬ 12 ≤ 3
  ¬12≤3 ()

  -- For proving general facts, we resort to "why is it stuck?", as usual:
  -- producing ≤
  n≤1+n : (n : ℕ) → n ≤ suc n
  n≤1+n zero = tt
  n≤1+n (suc n) = n≤1+n n

  -- However this can become tedious when we have to "unstick" an
  -- assumption given to us, as well as a goal we are trying to prove:
  -- consuming ≤
  n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
  n≤0⇒n≡0 {zero} _ = refl
  -- n≤0⇒n≡0 {suc n} () 

module ByInduction where

  -- Sometimes it is nicer if we can just pattern match on the proof.

  -- Here is an alternative definition:
  data _≤_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

  -- Concrete cases are still easy (using Refine C-c C-r), but requires a little bit more manual work:
  2≤4 : 2 ≤ 4
  2≤4 = s≤s (s≤s z≤n)

  ¬12≤3 : ¬ 12 ≤ 3
  ¬12≤3 (s≤s (s≤s (s≤s ())))

  -- Constructing evidence is basically the same as before ...
  n≤1+n : (n : ℕ) → n ≤ suc n
  n≤1+n zero = z≤n
  n≤1+n (suc n) = s≤s (n≤1+n n)

  -- ... but when given evidence, we can now pattern match!
  n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
  n≤0⇒n≡0 z≤n = refl

  -- Bringing in `n` to see what's going on.
  -- Pattern matchingon `n` twice.
  n≤0⇒n≡0' : ∀ {n} → n ≤ 0 → n ≡ 0
  n≤0⇒n≡0' {zero} x = refl
  n≤0⇒n≡0' {suc n} ()

  -------------
  -- Summary --
  -------------

  -- Tradeoffs pattern matching vs defined as data:
  --   1. Pattern matching definitions compute.
  --   2. Can pattern match on data itself.

  --------------------------
  -- ≤ is a Partial Order --
  --------------------------

  -- Reflexivity, transivity, antisymmetry ↔ Partial Order

  ≤-reflexive : (n : ℕ) → n ≤ n
  ≤-reflexive zero = z≤n
  ≤-reflexive (suc n) = s≤s (≤-reflexive n)

  ≤-trans : {n m k : ℕ} → n ≤ m → m ≤ k → n ≤ k
  ≤-trans z≤n p = z≤n
  ≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

  ≤-antisym : {n m : ℕ} → n ≤ m → m ≤ n → n ≡ m
  ≤-antisym z≤n z≤n = refl
  ≤-antisym (s≤s p) (s≤s q) = cong suc (≤-antisym p q)

  -------------
  -- Summary --
  -------------

  -- Pattern matching on inductive families reveals information about other patterns, too.

  -------------------------------------------------------------------
  -- Other properties of ≤
  -------------------------------------------------------------------

  ≤-propositional : {n m : ℕ} → isPropositional (n ≤ m)
  ≤-propositional z≤n z≤n = refl
  ≤-propositional (s≤s p) (s≤s q) = cong s≤s (≤-propositional p q)

  ≤-decidable : (n m : ℕ) → Dec (n ≤ m)
  ≤-decidable zero m = yes z≤n
  ≤-decidable (suc n) zero = no (λ ())
  ≤-decidable (suc n) (suc m) with ≤-decidable n m
  ... |  yes n≤m = yes (s≤s n≤m)
  ... |  no ¬n≤m = no λ { (s≤s p) → ¬n≤m p }

  -------------
  -- Summary --
  -------------

  -- 1. Going down the wrong path can be painful.
  -- 2. The use of `with` to pattern match on "extra" data, eg recursive calls.

  -----------------
  -- Now You Try --
  -----------------

  -- First do it the painful way, pattern matching on `k` but without pattern matching on `p`.
  -- You will want to use `subst` and `+-identityʳ` and `+-suc`.

  -- TODO
  +-monotone : {n m k : ℕ} → m ≤ n → m ≤ (n + k)
  +-monotone {n} {m} {k} p = {!!}

  -- Then do it the easy way with pattern matching on `p`.

  +-monotone' : {n m k : ℕ} → m ≤ n → m ≤ (n + k)
  +-monotone' z≤n = z≤n
  +-monotone' (s≤s p) = s≤s (+-monotone' p)
