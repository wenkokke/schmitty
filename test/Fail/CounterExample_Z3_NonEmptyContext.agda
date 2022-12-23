{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}

module CounterExample_Z3_NonEmptyContext where

open import Data.Integer using (ℤ; +_; -[1+_]; _-_; _+_; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theories.Ints as Ints
open import SMT.Backend.Z3 Ints.theory

-- - Call solveZ3 in a non-empty context
-- - Handle unused variables
-- - Handle alternations of quantifiers and implications
_ : (x y w : ℤ) → x ≤ y → ∀ z → z ≤ y → x ≡ y
_ = λ x y H → solveZ3
