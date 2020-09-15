{-# OPTIONS --allow-exec #-}

module CounterExample_Z3_Ints where

open import Data.Integer using (ℤ; +_; -[1+_]; _-_; _+_; _≤_)
open import Data.List using (List; _∷_; [])
open import Data.Unit using () -- constructor instance
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theories.Ints as Ints
open import SMT.Backend.Z3 Ints.reflectable

_ : (x y : ℤ) → x ≤ y → x ≡ y
_ = solveZ3
