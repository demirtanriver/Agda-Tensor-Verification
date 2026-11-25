module LU where

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agda.Builtin.Float using
  ( Float
  ; primFloatPlus
  ; primFloatMinus
  ; primFloatTimes
  ; primFloatDiv
  )

open import Effect.Applicative using (RawApplicative)
open RawApplicative {{...}} hiding (_⊗_)

open import Array
open ArOps

-- Bundle of basic math operations
record Num (A : Set) : Set where
  field
    0# 1# : A
    _+_ _-_ _*_ _/_ : A → A → A

  infixl 6 _+_ _-_
  infixl 7 _*_ _/_

open Num {{...}}

-- Connect Num to Agda's built-in Float
instance
  NumFloat : Num Float
  NumFloat = record
    { 0#  = 0.0
    ; 1#  = 1.0
    ; _+_ = primFloatPlus
    ; _-_ = primFloatMinus
    ; _*_ = primFloatTimes
    ; _/_ = primFloatDiv
    }

private variable
  m n k b : ℕ
  s p q : S
  A : Set

-- Fill an array of any shape with 0
zeroAr : {{_ : Num A}} → Ar s A
zeroAr = pure 0#

-- Element-wise addition
_⊞_ : {{_ : Num A}} → Ar s A → Ar s A → Ar s A
a ⊞ b = _+_ <$> a <*> b

-- Element-wise subtraction
_⊟_ : {{_ : Num A}} → Ar s A → Ar s A → Ar s A
a ⊟ b = _-_ <$> a <*> b

infixl 6 _⊞_ _⊟_

-- Multiply every entry in an array by a single number
_·*_ : {{_ : Num A}} → A → Ar s A → Ar s A
c ·* a = (c *_) <$> a

infixl 7 _·*_

-- Sum all elements in an array
sum : {{_ : Num A}} → Ar s A → A
sum = fold _+_ 0#

-- Matrix multiplication
matmul : {{_ : Num A}} → Ar (s ⊗ p) A → Ar (p ⊗ q) A → Ar (s ⊗ q) A
matmul a b (i ⊗ j) = sum (λ k → a (i ⊗ k) * b (k ⊗ j))

-- Swap rows and columns
transpose : Ar (s ⊗ p) A → Ar (p ⊗ s) A
transpose a (j ⊗ i) = a (i ⊗ j)

-- n x n identity matrix
eye : {{_ : Num A}} → (n : ℕ) → Ar (ι n ⊗ ι n) A
eye n (ι i ⊗ ι j) with i ≟ j
... | yes _ = 1#
... | no  _ = 0#

-- Test 2x2 matrix: [ 2.0  3.0 ]
--                  [ 4.0  7.0 ]
sample2x2 : Ar (ι 2 ⊗ ι 2) Float
sample2x2 (ι zero       ⊗ ι zero)       = 2.0
sample2x2 (ι zero       ⊗ ι (suc zero)) = 3.0
sample2x2 (ι (suc zero) ⊗ ι zero)       = 4.0
sample2x2 (ι (suc zero) ⊗ ι (suc zero)) = 7.0

-- Check that multiplying by the identity matrix works
test-mul : Ar (ι 2 ⊗ ι 2) Float
test-mul = matmul sample2x2 (eye 2)