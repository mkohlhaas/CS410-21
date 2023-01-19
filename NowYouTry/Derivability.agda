module NowYouTry.Derivability where

open import Data.String
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Data.Nat
open import Function

-- 1. TODO: The whole chapter.
-- 2. https://en.wikipedia.org/wiki/SKI_combinator_calculus
-- 3. https://en.wikipedia.org/wiki/Semantics_of_logic
-- 4. https://en.wikipedia.org/wiki/Soundness
-- 5. Kripke Semantics

-------------------------------------------------------------------
--                 Inductively Defined Derivability              --
-------------------------------------------------------------------

--------------
-- Formulas --
--------------

data Formula : Set where
  Atom : String → Formula
  _⇒_  : Formula → Formula → Formula  -- Implication: A Formula implies another Formula.

infixr 6 _⇒_

-- We want to talk about derivability of Formulas.

--------------
-- Contexts --
--------------

-- Context is a list-like data structure.
data Context : Set where
  ε   : Context                      -- empty Context  
  _·_ : Context → Formula → Context  -- add Formula to Context (liked flipped Cons)

infixl 4 _·_

------------------
-- Proof System -- 
------------------

-- Γ = Context; A, B = Formula
-- ⊢ (pronounced: turnstile)
-- ⊢ = given a Context you can derive Formula
-- When a Context derives a Formula these four proof rules (hyp, weak, abs, app) apply.
data _⊢_ : Context → Formula → Set where
  hyp  : ∀ {Γ A}    → Γ · A ⊢ A
  weak : ∀ {Γ A B } → Γ ⊢ A → Γ · B ⊢ A
  abs  : ∀ {Γ A B } → Γ · A ⊢ B → Γ ⊢ A ⇒ B
  app  : ∀ {Γ A B } → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B

-- Seeing Context as a list:
-- Γ · A  : add an element to the list.
-- Γ ⊢ A  : A is an element of the list.
-- `hyp`  : takes the right-most element of the list.
-- `weak` : removes right-most element from list.

-- hypothesis:  Adding A to a Context makes A derivable. (Trivial.)
-- weakening:   Adding B to a Context which already derives A still derives A. Adding B to a Context does not change the derivability of A.
-- abstraction: A Context deriving B to which we add an A that means that A ⇒ B.
-- application: A Context deriving 'A implies B' and A means it derives B.

infix  3 _⊢_

--------------
-- Examples --
--------------

example1 : ε · Atom "A" ⊢ Atom "A"
example1 = hyp

-- Notice the precedences:
-- the same: example2 :  ε · Atom "A" · (Atom "A"  ⇒  Atom "B") ⊢ Atom "B"
-- but not:  example2 : (ε · Atom "A" ·  Atom "A") ⇒ (Atom "B"  ⊢ Atom "B")
example2 : ε · Atom "A" · Atom "A" ⇒ Atom "B" ⊢ Atom "B"
example2 = app hyp (weak hyp)

example2' : ε · Atom "A" · Atom "B" ⊢ Atom "A" ⇒ Atom "B"
example2' = abs (weak hyp)

-- How do I proof the reverse of `⇒` ? (Pattern matching on Formula (·) ?) ⇒ See next chapter!
-- Spoiler: It is not provable!
-- example2'' : ε · Atom "A" ⇒ Atom "B" ⊢ Atom "B"
-- example2'' = app hyp (app {!!} {!!}) 

-- example2''' : ε · Atom "A" ⇒ Atom "B" ⊢ Atom "A"
-- example2''' = app {!!} {!!}

-------------
-- Summary --
-------------

-- 1. Use inductive families to encode e.g. derivability and other treelike structures.
-- 2. Easy to show what is derivable. (But what about showing what isn't?)

-- inductive families = data types with params

----------------------------------------------
--                 Semantics                --
----------------------------------------------

-- No way to prove this: (endless loop)
-- example3 : ¬ (ε ⊢ (Atom "A" ⇒ Atom "B") ⇒ Atom "A")
-- example3 (abs (weak (app (abs hyp) d₁))) = {!!}

-- for turning Atoms into Sets
Env = String → Set

-- Create datatypes from Formula and Context so we can use them in proofs.

⟦_⟧F : Formula → Env → Set
⟦ Atom x ⟧F ρ = ρ x
⟦ A ⇒ B  ⟧F ρ = ⟦ A ⟧F ρ → ⟦ B ⟧F ρ  -- convert implication to Agda's way of implication (a function)

⟦_⟧C : Context → Env → Set
⟦ ε     ⟧C ρ = ⊤                     -- empty Context means true
⟦ Γ · A ⟧C ρ = ⟦ Γ ⟧C ρ × ⟦ A ⟧F ρ   -- `and` together all assumptions (with a product type)

-- Soundness: Every derivation has an interpretation.
-- Given an Env (ρ) every statement about Derivability (Γ ⊢ A) implies an interpretation (⟦ Γ ⟧C ρ → ⟦ A ⟧F ρ).
⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → (ρ : Env) → ⟦ Γ ⟧C ρ → ⟦ A ⟧F ρ
⟦ hyp      ⟧ ρ (γ , a) = a
⟦ weak d   ⟧ ρ (γ , b) = ⟦ d ⟧ ρ γ
⟦ abs  d   ⟧ ρ  γ      = λ a → ⟦ d ⟧ ρ (γ , a)
⟦ app  d e ⟧ ρ  γ      = ⟦ d ⟧ ρ γ (⟦ e ⟧ ρ γ)

-- Now we can prove example3.
example3 : ¬ (ε ⊢ (Atom "A" ⇒ Atom "B") ⇒ Atom "A")
example3 d = ⟦ d ⟧ ρ tt λ _ → tt
  where
    ρ : Env
    ρ "A" = ⊥
    ρ "B" = ⊤
    ρ _   = ℕ  -- any data type will do

-------------
-- Summary --
-------------

-- 1. Can use a model to show what is NOT derivable.
-- 2. Soundness: Everything provable is true in the model.
-- 3. Completeness: If true in the model, then provable. (But not in our case - model is too simple.)

----------------------------------------------------------------
--                 Meta-Theoretical Properties                --
----------------------------------------------------------------

-- Let's prove that we can replace abstraction and variables with just the S and K combinators.

-- First, we define an alternative proof system:

data ⊢sk_ : Formula → Set where
  app : ∀ {A B}   → ⊢sk  A ⇒ B → ⊢sk A → ⊢sk B
  K   : ∀ {A B}   → ⊢sk  A ⇒ B ⇒ A
  S   : ∀ {A B C} → ⊢sk (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C

infix  3  ⊢sk_

-- Look ma', no contexts!

-- Our claim is that we can translate between both proof systems.
-- We want to translate `⊢sk A → ε ⊢ A` and `ε ⊢ A → ⊢sk A`.

-- We can easily translate one way:
SKtoND : ∀ {A} → ⊢sk A → ε ⊢ A
SKtoND (app d e) = app (SKtoND d) (SKtoND e)
SKtoND K = abs (abs (weak hyp))
SKtoND S = abs (abs (abs (app (app (weak (weak hyp)) hyp) (app (weak hyp) hyp))))

-- The other way looks also promising but fails.

-- NDtoSK : ∀ {A} → ε ⊢ A → ⊢sk A
-- NDtoSK (abs d) = {!NDtoSK d!}
-- NDtoSK (app d e) = app (NDtoSK d) (NDtoSK e)

-- Generalise (using an arbitrary context)!
-- But fails again.

-- NDtoSK : ∀ {Γ A} → Γ ⊢ A → ⊢sk A
-- NDtoSK hyp = {!!} -- not going to work, because ⊢sk A does not talk about Γ!
-- NDtoSK (weak d) = {!!}
-- NDtoSK (abs d) = {!!}
-- NDtoSK (app d d₁) = {!!}

-- Generalise to non-empty contexts for the SK proof system!

-- Generalise ⊢sk A to take Γ into account too.
data _⊢skv_ : Context → Formula → Set where
  hyp  : ∀ {Γ A}     → Γ · A ⊢skv A
  weak : ∀ {Γ A B }  → Γ ⊢skv A → Γ · B ⊢skv A
  app  : ∀ {Γ A B}   → Γ ⊢skv A ⇒ B → Γ ⊢skv A → Γ ⊢skv B
  K    : ∀ {Γ A B}   → Γ ⊢skv A ⇒ B ⇒ A
  S    : ∀ {Γ A B C} → Γ ⊢skv (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C

infix  3 _⊢skv_

SKVtoSK : ∀ {A} → ε ⊢skv A → ⊢sk A
SKVtoSK (app d e) = app (SKVtoSK d) (SKVtoSK e)
SKVtoSK K         = K
SKVtoSK S         = S

-- We have hyp, weak and app in both systems, but not abstraction.
NDtoSKV : ∀ {Γ A} → Γ ⊢ A → Γ ⊢skv A
NDtoSKV hyp       = hyp
NDtoSKV (weak d)  = weak (NDtoSKV d)
NDtoSKV (app d e) = app (NDtoSKV d) (NDtoSKV e)
NDtoSKV (abs d)   = absSK (NDtoSKV d)
  where
    -- abstraction for the SK proof system
    -- Showing that the target proof system (SK) has the same underlying structure than the source system.
    absSK : ∀ {Γ A B } → Γ · A ⊢skv B →  Γ ⊢skv A ⇒ B
    absSK {A = A} hyp = app (app S K) (K {B = A})
    absSK (weak d)    = app K d
    absSK (app d e)   = app (app S (absSK d)) (absSK e)
    absSK K           = app K K
    absSK S           = app K S

NDtoSK : ∀ {A} → ε ⊢ A → ⊢sk A
NDtoSK = SKVtoSK ∘ NDtoSKV

-------------
-- Summary --
-------------

-- 1. Use pattern matching to prove things about the encoded logic itself.
-- 2. Here: S and K combinators can replace abstraction and application.

-----------------
-- Now You Try --
-----------------

-- Prove that `(B → A) → (A → B)` is not provable in the SK calculus:

-- TODO
¬everythingEquivalent : ¬ (⊢sk (Atom "B" ⇒ Atom "A") ⇒ (Atom "A" ⇒ Atom "B"))
¬everythingEquivalent d = {!!}
