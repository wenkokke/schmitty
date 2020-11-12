--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Exports the various bits and pieces needed to use a specific theory.
--------------------------------------------------------------------------------

open import SMT.Theory

module SMT.Script {theory : Theory} (reflectable : Reflectable theory) where

open Theory theory
open import SMT.Script.Base baseTheory public
open import SMT.Script.Show theory public
open import SMT.Script.Reflection reflectable public
