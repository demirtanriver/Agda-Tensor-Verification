module LU where

open import Array
open ArOps

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)

open import Effect.Applicative using (RawApplicative)
open RawApplicative {{...}} hiding (_⊗_)

open import Agda.Builtin.Float using ( Float ; primFloatPlus ; primFloatMinus ; primFloatTimes; primFloatDiv)

infixl 6 _+_ _-_
infixl 7 _*_ _/_

_+_ : Float → Float → Float
x + y = primFloatPlus x y

_-_ : Float → Float → Float
x - y = primFloatMinus x y

_*_ : Float → Float → Float
x * y = primFloatTimes x y

_/_ : Float → Float → Float
x / y = primFloatDiv x y  

open Tests
matMulFloat : ∀ {s p q} → Ar (s ⊗ p) Float → Ar (p ⊗ q) Float → Ar (s ⊗ q) Float
matMulFloat a b = matmul Float 0.0 _+_ _*_ a b 

