{-# OPTIONS --allow-exec #-}

module SMT.Theories.Core.Example where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; suc; zero)
open import Data.List using (List; _∷_; [])
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theories.Core as Core
open import SMT.Backend.Z3 Core.corePrintable Core.coreParsable


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
  script = declare-const BOOL
         ∷ assert (app₂ and p (app₁ not p))
         ∷ check-sat
         ∷ []
         where
           p = var (zero , refl)

  _ : z3 script ≡ unsat ∷ []
  _ = refl


module Example₂ where

  -- |Pierce's law.
  script : Script [] [] (SAT ∷ [])
  script = assert (forAll BOOL (forAll BOOL ((app₂ implies (app₂ implies (app₂ implies p q) p) p))))
         ∷ check-sat
         ∷ []
         where
           p = var (suc zero , refl)
           q = var (    zero , refl)

  _ : z3 script ≡ sat ∷ []
  _ = refl


module Example₃ where

  -- |Parsing models.
  script : Script [] (BOOL ∷ []) (MODEL (BOOL ∷ []) ∷ [])
  script = declare-const BOOL
         ∷ assert (var (zero , refl))
         ∷ get-model
         ∷ []
  _ : z3 script ≡ (true ∷ []) ∷ []
  _ = refl
