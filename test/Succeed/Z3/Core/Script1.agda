{-# OPTIONS --allow-exec #-}

module Succeed.Z3.Core.Script1 where

open import Data.List using (List; _∷_; [])
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
script : Script [] (BOOL ∷ []) (SAT ∷ [])
script = declare-const "b" BOOL
       ∷ assert (app₂ and (# 0) (app₁ not (# 0)))
       ∷ check-sat
       ∷ []

_ : z3 script ≡ unsat ∷ []
_ = refl
