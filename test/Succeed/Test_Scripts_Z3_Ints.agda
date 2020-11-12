-----------------------------------------------
-- Test handwritten scripts for Ints with Z3 --
-----------------------------------------------

{-# OPTIONS --allow-exec #-}

module Test_Scripts_Z3_Ints where

open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theories.Ints as Ints
open import SMT.Backend.Z3 Ints.reflectable

-- |Taken from <http://smtlib.cs.uiowa.edu/examples.shtml>
--
-- @
--   ; Integer arithmetic
--   (set-logic QF_LIA)
--   (declare-const x Int)
--   (declare-const y Int)
--   (assert (= (- x y) (+ x (- y) 1)))
--   (check-sat)
--   ; unsat
--   (exit)
-- @
--
script₁ : Script [] (INT ∷ INT ∷ []) (SAT ∷ [])
script₁ = declare-const "x" INT
       ∷ declare-const "y" INT
       ∷ assert (app₂ eq
                (app₂ sub (# 0) (# 1))
                (app₂ add (app₂ add (# 0) (app₁ neg (# 1))) (lit (nat 1)))
                )
       ∷ check-sat
         ∷ []

_ : z3 script₁ ≡ unsat ∷ []
_ = refl



script₂ : Script [] (INT ∷ []) (SAT ∷ [])
script₂ = declare-const "x" INT
  ∷ assert (
    ⟨let⟩ "y" ∶ INT ≈ # 0 ⟨in⟩
      app₂ eq (# 0) (# 1))
  ∷ check-sat
  ∷ []

_ : z3 script₂ ≡ sat ∷ []
_ = refl
