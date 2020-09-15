{-# OPTIONS --allow-exec #-}

module Test_Reflection_Z3_Ints where

open import Data.Integer using (ℤ; _+_; _-_; _*_)
open import Data.List using (List; _∷_; [])
open import Data.Unit using () -- constructor instance
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theories.Ints as Ints
open import SMT.Backend.Z3 Ints.reflectable

_ : (x y : ℤ) → x + y ≡ y + x
_ = solveZ3

_ : (x y z : ℤ) → x + (y + z) ≡ (x + y) + z
_ = solveZ3

module OverloadedLiterals where

  import Data.Integer.Literals as Int using (number; negative)

  open import Agda.Builtin.FromNat
  open import Agda.Builtin.FromNeg

  instance _ = Int.number
           _ = Int.negative

  _ : (x : ℤ) → (x + 2) * (x + -2) ≡ x * x - 4
  _ = solveZ3
