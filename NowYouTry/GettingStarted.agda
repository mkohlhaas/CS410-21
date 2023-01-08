module NowYouTry.GettingStarted where

---------------
-- datatypes --
---------------

data List (A : Set) : Set where
  []   : List A
  _∷_  : A → List A → List A

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_

-----------
-- const --
-----------

-- const : {A B : Set} → A → B → A
-- const = λ a b → a

const : {A B : Set} → A → B → A
const a b = a

------------
-- append --
------------

-- append : {A : Set} → List A → List A → List A
-- append [] ys = ys
-- append (x ∷ xs) ys = x ∷ (append xs ys)

append : {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

----------
-- swap --
----------

-- swap : {A B : Set} → A × B → B × A
-- swap (a , b) = b , a

swap : {A B : Set} → A × B → B × A
swap (a , b) = b , a

----------------
-- distribute --
----------------

-- distribute : {A B C : Set} → A × (B ⊎ C) → (A × B) ⊎ (A × C)
-- distribute (a , inj₁ b) = inj₁ (a , b)
-- distribute (a , inj₂ c) = inj₂ (a , c)

distribute : {A B C : Set} → A × (B ⊎ C) → (A × B) ⊎ (A × C)
distribute (a , inj₁ b) = inj₁ (a , b)
distribute (a , inj₂ c) = inj₂ (a , c)

-----------------------
-- distributeInverse --
-----------------------

distributeInverse : {A B C : Set} → (A × B) ⊎ (A × C) → A × (B ⊎ C)
distributeInverse (inj₁ (a , b)) = a , inj₁ b
distributeInverse (inj₂ (a , c)) = a , inj₂ c
