{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}

module CounterExample_Z3_IgnoreNonsense where

open import Data.Integer using (ℤ; +_; -[1+_]; _-_; _+_; _≤_)
open import Data.List.Base using (List)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theories.Ints as Ints
open import SMT.Backend.Z3 Ints.theory

-- - Report when some argument is ignored.
_ : (x : ℤ) → List ℤ → x ≡ + 0
_ = solveZ3
