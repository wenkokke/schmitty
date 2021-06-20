{-# OPTIONS --guardedness #-}

--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Exports the `Theory` and `Reflectable` instances for the core theory, called
-- `coreTheory` and `coreReflectable`.
-- See <http://smtlib.cs.uiowa.edu/theories-Core.shtml>.
--------------------------------------------------------------------------------

module SMT.Theories.Core where

open import SMT.Theories.Core.Base public
open import SMT.Theories.Core.Reflection public
