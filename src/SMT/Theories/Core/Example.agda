{-# OPTIONS --allow-exec #-}

module SMT.Theories.Core.Example where

open import Data.Fin using (Fin; suc; zero)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)
open import Reflection.External
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import SMT.Theories.Core
open import SMT.Script coreTheory
open import SMT.Script.Show corePrintable
open import SMT.Backend.Z3 corePrintable

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
script₁ : Script [] (BOOL ∷ []) (SAT ∷ [])
script₁ = declare-const BOOL
        ∷ assert (app₂ and p (app₁ not p))
        ∷ check-sat
        ∷ []
        where
          p = var (zero , refl)

test₁ : runCmd (z3Cmd script₁) ≡ "unsat\n"
test₁ = refl


-- |Pierce's law.
term₂ : Term [] BOOL
term₂ = forAll (forAll ((app₂ implies (app₂ implies (app₂ implies p q) p) p)))
  where
    p = var (suc zero , refl)
    q = var (    zero , refl)

script₂ : Script [] [] (SAT ∷ [])
script₂ = assert term₂
        ∷ check-sat
        ∷ []

test₂ : runCmd (z3Cmd script₂) ≡ "sat\n"
test₂ = refl
