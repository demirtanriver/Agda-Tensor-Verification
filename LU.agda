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


-- Get the first item of a 1D array
head : Ar (ι (suc n)) A → A
head v = v (ι zero)

-- Get everything except the first item of a 1D array
tail : Ar (ι (suc n)) A → Ar (ι n) A
tail v i = v (ιsuc i)

-- Put a single item onto the front of a 1D array
cons : A → Ar (ι n) A → Ar (ι (suc n)) A
cons x xs (ι zero)    = x
cons x xs (ι (suc i)) = xs (ι i)

-- Multiply a column vector and a row vector into a 2D grid
outer : {{_ : Num A}} → Ar (ι m) A → Ar (ι n) A → Ar (ι m ⊗ ι n) A
outer u v (i ⊗ j) = u i * v j

-- Grab the top-left corner number of a matrix
topLeft : Ar (ι (suc m) ⊗ ι (suc n)) A → A
topLeft M = head (head (nest M))

-- Grab the rest of the first row
topRow : Ar (ι (suc m) ⊗ ι (suc n)) A → Ar (ι n) A
topRow M = tail (head (nest M))

-- Grab the rest of the first column
leftCol : Ar (ι (suc m) ⊗ ι (suc n)) A → Ar (ι m) A
leftCol M = head <$> tail (nest M)

-- Grab the remaining bottom-right submatrix
botRight : Ar (ι (suc m) ⊗ ι (suc n)) A → Ar (ι m ⊗ ι n) A
botRight M = unnest (tail <$> tail (nest M))

-- Stick the 4 pieces back together into one matrix
joinMat : A → Ar (ι n) A → Ar (ι m) A → Ar (ι m ⊗ ι n) A
        → Ar (ι (suc m) ⊗ ι (suc n)) A
joinMat a11 a12 a21 A22 =
  unnest (cons (cons a11 a12) (cons <$> a21 <*> nest A22))

-- Unblocked LU decomposition: splits an n x n matrix into (L , U)
lu : {{_ : Num A}} → ∀ {n} → Ar (ι n ⊗ ι n) A
   → Ar (ι n ⊗ ι n) A × Ar (ι n ⊗ ι n) A
lu {n = zero}  M = zeroAr , zeroAr
lu {n = suc n} M = joinMat 1# zeroAr l21 L22 , joinMat a11 u12 zeroAr U22
  where
    a11 = topLeft M
    u12 = topRow M
    l21 = (_/ a11) <$> leftCol M
    M22 = botRight M ⊟ outer l21 u12
    rec = lu M22
    L22 = proj₁ rec
    U22 = proj₂ rec

-- Run unblocked LU on sample2x2
test-lu : Ar (ι 2 ⊗ ι 2) Float × Ar (ι 2 ⊗ ι 2) Float
test-lu = lu sample2x2

-- Multiply L and U back together to check we get sample2x2 back
test-lu-check : Ar (ι 2 ⊗ ι 2) Float
test-lu-check = matmul (proj₁ test-lu) (proj₂ test-lu)

-- A b x b block of numbers
Block : ℕ → Set → Set
Block b A = Ar (ι b ⊗ ι b) A

-- Solve L * X = B where L is lower triangular
trsm-L : {{_ : Num A}} → ∀ {n} → Ar (ι n ⊗ ι n) A → Ar (ι n ⊗ ι m) A
       → Ar (ι n ⊗ ι m) A
trsm-L {n = zero}  L B = zeroAr
trsm-L {n = suc n} L B = unnest (cons x1 (nest X2))
  where
    l11 = topLeft L
    l21 = leftCol L
    L22 = botRight L
    b1  = head (nest B)
    B2  = unnest (tail (nest B))
    x1  = (_/ l11) <$> b1
    X2  = trsm-L L22 (B2 ⊟ outer l21 x1)

-- Solve X * U = B where U is upper triangular
trsm-U : {{_ : Num A}} → ∀ {n} → Ar (ι m ⊗ ι n) A → Ar (ι n ⊗ ι n) A
       → Ar (ι m ⊗ ι n) A
trsm-U B U = transpose (trsm-L (transpose U) (transpose B))

-- Subtract two grids of blocks block-by-block
_⊟grid_ : {{_ : Num A}} → Ar s (Block b A) → Ar s (Block b A) → Ar s (Block b A)
X ⊟grid Y = _⊟_ <$> X <*> Y

-- Outer product of a column of blocks and a row of blocks
blockOuter : {{_ : Num A}} → Ar (ι m) (Block b A) → Ar (ι n) (Block b A)
           → Ar (ι m ⊗ ι n) (Block b A)
blockOuter u v (i ⊗ j) = matmul (u i) (v j)

-- Multiply two grids of blocks
gridMul : {{_ : Num A}} → Ar (ι m ⊗ ι k) (Block b A) → Ar (ι k ⊗ ι n) (Block b A)
        → Ar (ι m ⊗ ι n) (Block b A)
gridMul X Y (i ⊗ j) = fold _⊞_ zeroAr (λ r → matmul (X (i ⊗ r)) (Y (r ⊗ j)))

-- Blocked LU on a k x k grid of b x b blocks
lu-grid : {{_ : Num A}} → ∀ {k} → Ar (ι k ⊗ ι k) (Block b A)
        → Ar (ι k ⊗ ι k) (Block b A) × Ar (ι k ⊗ ι k) (Block b A)
lu-grid {k = zero}  M = pure zeroAr , pure zeroAr
lu-grid {k = suc k} M =
  joinMat L11 (pure zeroAr) L21 L22 , joinMat U11 U12 (pure zeroAr) U22
  where
    A11  = topLeft M
    A12  = topRow M
    A21  = leftCol M
    A22  = botRight M
    lu11 = lu A11
    L11  = proj₁ lu11
    U11  = proj₂ lu11
    U12  = trsm-L L11 <$> A12
    L21  = (λ blk → trsm-U blk U11) <$> A21
    S22  = A22 ⊟grid blockOuter L21 U12
    rec  = lu-grid S22
    L22  = proj₁ rec
    U22  = proj₂ rec

-- Test 2x2 grid of 2x2 blocks
sampleGrid : Ar (ι 2 ⊗ ι 2) (Block 2 Float)
sampleGrid (ι zero       ⊗ ι zero)       = sample2x2
sampleGrid (ι zero       ⊗ ι (suc zero)) = eye 2
sampleGrid (ι (suc zero) ⊗ ι zero)       = eye 2
sampleGrid (ι (suc zero) ⊗ ι (suc zero)) = sample2x2

-- Run blocked LU on sampleGrid and multiply L and U back together
test-grid-lu : Ar (ι 2 ⊗ ι 2) (Block 2 Float) × Ar (ι 2 ⊗ ι 2) (Block 2 Float)
test-grid-lu = lu-grid sampleGrid

test-grid-check : Ar (ι 2 ⊗ ι 2) (Block 2 Float)
test-grid-check = gridMul (proj₁ test-grid-lu) (proj₂ test-grid-lu)