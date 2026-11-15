open import Data.Nat as ℕ
open import Level renaming (zero to ℓzero; suc to ℓsuc)
open import Function

open import Effect.Monad using (RawMonad)
open import Effect.Applicative using (RawApplicative)
open import Effect.Functor using (RawFunctor)
open RawMonad {{...}} hiding (_⊗_)


module _ where

module ArOps where
  open import Data.Fin as Fin using (Fin; zero; suc) 
  open import Data.Sum using (inj₁; inj₂)
  open import Relation.Nullary using (Dec; yes; no) 
  open import Data.Empty using (⊥; ⊥-elim)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans) 
 
  private variable
    ℓ ℓ₁ ℓ₂ : Level
    m n : ℕ

  data S : Set where
    ι   : ℕ → S
    _⊗_ : S → S → S

  private variable
    s p q r : S

  data P : S → Set where
    ι   : Fin n → P (ι n)
    _⊗_ : P s → P p → P (s ⊗ p)
 
  ιsuc : P (ι n) → P (ι (suc n))
  ιsuc (ι i) = ι (suc i)

  Ar : S → Set ℓ → Set ℓ
  Ar s X = P s → X

  Vec : ℕ → Set ℓ → Set ℓ
  Vec n X = Ar (ι n) X

  ar-map : {X : Set ℓ₁} {Y : Set ℓ₂} {s : S} → (X → Y) → Ar s X → Ar s Y
  ar-map f a i = f (a i)

  K : {X : Set ℓ} {s : S} → X → Ar s X
  K x _ = x
  
  nest : {X : Set ℓ} → Ar (s ⊗ p) X → Ar s (Ar p X)
  nest a i j = a (i ⊗ j)

  unnest : {X : Set ℓ} → Ar s (Ar p X) → Ar (s ⊗ p) X
  unnest a (i ⊗ j) = a i j

  instance
    ArFunctor : RawFunctor {ℓ} (Ar s)
    ArFunctor .RawFunctor._<$>_ = ar-map

    ArApplicative : RawApplicative {ℓ} (Ar s)
    ArApplicative .RawApplicative.rawFunctor = ArFunctor
    ArApplicative .RawApplicative.pure = K
    ArApplicative .RawApplicative._<*>_ = λ fs a i → fs i (a i)

    ArMonad : RawMonad {ℓ} (Ar s)
    ArMonad .RawMonad.rawApplicative = ArApplicative
    ArMonad .RawMonad._>>=_ = λ a mf i → mf (a i) i
 

  fold₁ : ∀ {ℓ}{X : Set ℓ} → (X → X → X) → X → Vec n X → X
  fold₁ {zero} f e v = e
  fold₁ {suc n} f e v = f (v (ι zero)) (fold₁ f e (v ∘′ ιsuc))

  fold : ∀ {ℓ}{X : Set ℓ} → (X → X → X) → X → Ar s X → X
  fold {ι x} f e a = fold₁ f e a
  fold {s ⊗ s₁} f e a = fold f e (fold f e <$> nest a)


module Tests where

  open ArOps

  private variable
    s p q : S

  module _ {ℓ} (X : Set ℓ) (𝟘 : X) (_⊞_ _⊠_ : X → X → X) where

    matmul : Ar (s ⊗ p) X → Ar (p ⊗ q) X → Ar (s ⊗ q) X
    matmul a b (i ⊗ j) = sum λ k → a (i ⊗ k) ⊠ b (k ⊗ j)
      where 
        sum = fold _⊞_ 𝟘
