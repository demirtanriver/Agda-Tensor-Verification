module LU where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

-- falsehood with no constructors
data ⊥ : Set where

-- anything follows from a contradition
⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

-- negation
¬_ : Set → Set
¬ A = A → ⊥

infix 3 ¬_

-- inequality
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

infix 4 _≢_

-- decidability: proof of A or proof of ¬ A
data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

-- Maybe type to handle zero pivots
data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

-- Product type
data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

infixr 2 _×_
infix  4 ⟨_,_⟩

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- valid indices
data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)


postulate
  Scalar : Set
  0#     : Scalar
  1#     : Scalar
  _+_    : Scalar → Scalar → Scalar
  _-_    : Scalar → Scalar → Scalar
  _*_    : Scalar → Scalar → Scalar
  _/_    : Scalar → Scalar → Scalar
  _≟0#   : (x : Scalar) → Dec (x ≡ 0#)

infixl 6 _+_ _-_
infixl 7 _*_ _/_
infix  4 _≟0#

-- algebraic laws required 
postulate
  +-identityʳ  : ∀ (x : Scalar) → x + 0# ≡ x
  *-identityˡ  : ∀ (x : Scalar) → 1# * x ≡ x
  *-zeroˡ      : ∀ (x : Scalar) → 0# * x ≡ 0#
  *-zeroʳ      : ∀ (x : Scalar) → x * 0# ≡ 0#
  /-*-inverseˡ : ∀ {x : Scalar} (y : Scalar) → x ≢ 0# → (y / x) * x ≡ y
  +-sub-cancel : ∀ (x y : Scalar) → x + (y - x) ≡ y


-- the type system for the matrix DSL
data Ty : Set where
  scal : Ty
  vec  : ℕ → Ty
  mat  : ℕ → ℕ → Ty

Ar : Ty → Set
Ar scal      = Scalar
Ar (vec n)   = Fin n → Scalar
Ar (mat m n) = Fin m → Fin n → Scalar