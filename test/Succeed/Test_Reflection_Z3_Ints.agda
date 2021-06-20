{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}

module Test_Reflection_Z3_Ints where

open import Data.Integer using (ℤ; _+_; _-_; _*_; _>_; _<_; _≥_; _≤_; +<+)
open import Data.Nat using (s≤s; z≤n)
open import Data.List using (List; _∷_; [])
open import Data.Unit using () -- constructor instance
open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import SMT.Theories.Ints as Ints
open import SMT.Backend.Z3 Ints.reflectable

import Data.Integer.Literals as Int using (number; negative)

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg

instance _ = Int.number
         _ = Int.negative

_ : (x y : ℤ) → x + y ≡ y + x
_ = solveZ3

_ : (x y z : ℤ) → x + (y + z) ≡ (x + y) + z
_ = solveZ3

_ : (x : ℤ) → (x + 2) * (x + -2) ≡ x * x - 4
_ = solveZ3

_ : Σ ℤ λ z → ∀ n → z * n ≡ 0
_ = solveZ3

_ : Σ[ z ∈ ℤ ] ∀ n → z * n ≡ 0
_ = solveZ3

_ : ∃ λ z → ∀ n → z * n ≡ 0
_ = solveZ3

-- Gets eta contracted to ∃ (_>_ n), so reflectToRawTerm needs to do some work.
t : ∀ n → ∃[ m ] (n > m)
t = solveZ3

-- Test proof computations

compute₁ : (x y : ℤ) → x ≤ y → x ≥ y → x ≡ y
compute₁ = solveZ3

check-compute₁ : (H : 5 ≤ 5) → compute₁ 5 5 H H ≡ refl
check-compute₁ _ = refl

compute₂ : (x : ℤ) → x ≢ 0 → x * x > 0
compute₂ = solveZ3

check-compute₂ : (H : 2 ≢ 0) → compute₂ 2 H ≡ +<+ (s≤s z≤n)
check-compute₂ _ = refl
