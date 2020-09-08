{-# OPTIONS --allow-exec #-}

module SMT.Theories.Core.Example where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; suc; zero)
open import Data.List using (List; _∷_; [])
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theories.Core as Core
open import SMT.Script Core.coreTheory Core.coreReflectable
open import SMT.Backend.Z3 Core.coreTheory Core.coreReflectable


module Example₁ where

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
  script : Script [] (BOOL ∷ []) (SAT ∷ [])
  script = declare-const "b" BOOL
         ∷ assert (app₂ and (# 0) (app₁ not (# 0)))
         ∷ check-sat
         ∷ []

  _ : z3 script ≡ unsat ∷ []
  _ = refl


module Example₂ where

  -- |Pierce's law.
  script : Script [] [] (SAT ∷ [])
  script = assert (forAll BOOL (forAll BOOL ((app₂ implies (app₂ implies (app₂ implies (# 1) (# 0)) (# 1)) (# 1)))))
         ∷ check-sat
         ∷ []

  _ : z3 script ≡ sat ∷ []
  _ = refl


module Example₃ where

  -- |Parsing models.
  script : Script [] (BOOL ∷ []) (MODEL (BOOL ∷ []) ∷ [])
  script = declare-const "b" BOOL
         ∷ assert (# 0)
         ∷ get-model
         ∷ []
  _ : z3 script ≡ (sat , true ∷ []) ∷ []
  _ = refl
