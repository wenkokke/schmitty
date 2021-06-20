{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}

---------------------------------------------------------
-- Test handwritten scripts for Reals.As.Float with Z3 --
---------------------------------------------------------

module Test_Scripts_Z3_RealsAsFloat where

open import Data.Empty using (⊥)
open import Data.Float using (_≟_; _÷_)
open import Data.Integer using (+_)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (True)
open import Text.Parser.String
open import SMT.Theories.Reals as Reals
open import SMT.Backend.Z3 Reals.reflectable

script : Script [] (REAL ∷ REAL ∷ []) (MODEL (REAL ∷ REAL ∷ []) ∷ [])
script = `declare-const "x" REAL
       ∷ `declare-const "y" REAL
       ∷ `assert (`app₂ eq (# 0) (`app₂ div (# 1) (`lit (nat 2))))
       ∷ `assert (`app₂ gt (# 0) (`lit (nat 1)))
       ∷ `assert (`app₂ gt (# 1) (`lit (nat 1)))
       ∷ `get-model
       ∷ []

is-correct : Outputs (MODEL (REAL ∷ REAL ∷ []) ∷ []) → Set
is-correct ((sat     , (x ∷ y ∷ [])) ∷ []) = True (x ≟ y ÷ 2.0)
is-correct ((unsat   , tt)           ∷ []) = ⊥
is-correct ((unknown , tt)           ∷ []) = ⊥

_ : is-correct (z3 script)
_ = tt
