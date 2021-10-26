{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}

module Test_Reflection_Z3_Nats where

open import Data.Nat using (ℕ; _+_; _∸_; _*_; _≤_; _<_; _≥_; _>_; z≤n; s≤s)
open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import SMT.Theories.Nats as Nats
open import SMT.Backend.Z3 Nats.theory

_ : (x y : ℕ) → x + y ≡ y + x
_ = solveZ3

_ : (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
_ = solveZ3

_ : Σ ℕ λ z → ∀ n → z * n ≡ 0
_ = solveZ3

_ : Σ[ z ∈ ℕ ] ∀ n → z * n ≡ 0
_ = solveZ3

_ : ∃ λ z → ∀ n → z * n ≡ 0
_ = solveZ3

-- Gets eta contracted to ∃ (_>_ n), so reflectToRawTerm needs to do some work.
t : ∀ n → ∃[ m ] (n > m)
t = solveZ3

-- Test proof computations

compute₁ : (x y : ℕ) → x ≤ y → x ≥ y → x ≡ y
compute₁ = solveZ3

check-compute₁ : (H : 5 ≤ 5) → compute₁ 5 5 H H ≡ refl
check-compute₁ _ = refl

compute₂ : (x : ℕ) → x ≢ 0 → x * x > 0
compute₂ = solveZ3

check-compute₂ : (H : 2 ≢ 0) → compute₂ 2 H ≡ s≤s z≤n
check-compute₂ _ = refl
