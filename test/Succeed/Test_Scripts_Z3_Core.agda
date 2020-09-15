-----------------------------------------------
-- Test handwritten scripts for Core with Z3 --
-----------------------------------------------

{-# OPTIONS --allow-exec #-}

module Test_Scripts_Z3_Core where

open import Data.List using (List; _∷_; [])
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theories.Core as Core
open import SMT.Backend.Z3 Core.coreReflectable

-- |Taken from <http://smtlib.cs.uiowa.edu/examples.shtml>
--
-- @
--   ; Boolean example
--   (set-option :print-success false)
--   (set-logic QF_UF)
--   (declare-const p Bool)
--   (assert (and p (not p)))
--   (check-sat)
--   ; unsat
--   (exit)
-- @
--
b∧¬b : Script [] (BOOL ∷ []) (SAT ∷ [])
b∧¬b = declare-const "b" BOOL
     ∷ assert (app₂ and (# 0) (app₁ not (# 0)))
     ∷ check-sat
     ∷ []

_ : z3 b∧¬b ≡ unsat ∷ []
_ = refl


-- |Pierce's law.
pierce : Script [] [] (SAT ∷ [])
pierce = assert
       ( forAll BOOL
       $ forAll BOOL
       $ app₂ implies (app₂ implies (app₂ implies (# 1) (# 0)) (# 1)) (# 1)
       )
       ∷ check-sat
       ∷ []

_ : z3 pierce ≡ sat ∷ []
_ = refl
