{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}

module Test_Reflection_Z3_Nats where

open import Data.Nat using (ℕ; _+_; _∸_; _*_)
open import Data.List using (List; _∷_; [])
open import Data.Unit using () -- constructor instance
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
