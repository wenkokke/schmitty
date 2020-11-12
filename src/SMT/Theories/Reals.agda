--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Exports the `Theory` and `Reflectable` instances for the theory of real
-- numbers, called `theory` and `reflectable`.
-- See <http://smtlib.cs.uiowa.edu/theories-Reals.shtml>.
--------------------------------------------------------------------------------

module SMT.Theories.Reals where

open import SMT.Theories.Reals.Base public
open import SMT.Theories.Reals.Reflection public
