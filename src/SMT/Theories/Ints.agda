--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Exports the `Theory` and `Reflectable` instances for the theory of integers,
-- called `theory` and `reflectable`.
-- See <http://smtlib.cs.uiowa.edu/theories-Ints.shtml>.
--------------------------------------------------------------------------------

module SMT.Theories.Ints where

open import SMT.Theories.Ints.Base public
open import SMT.Theories.Ints.Reflection public
