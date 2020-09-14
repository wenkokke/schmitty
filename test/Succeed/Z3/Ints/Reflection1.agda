{-# OPTIONS --allow-exec #-}

module Succeed.Z3.Ints.Reflection1 where

open import Data.Integer using (ℤ; _+_)
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theories.Ints as Ints
open import SMT.Backend.Z3 Ints.reflectable

_ : (x y : ℤ) → x + y ≡ y + x
_ = solveZ3

_ : (x y z : ℤ) → x + (y + z) ≡ (x + y) + z
_ = solveZ3
