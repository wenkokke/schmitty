{-# OPTIONS --guardedness #-}

--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Exports the various bits and pieces needed to use a specific theory.
--------------------------------------------------------------------------------

open import SMT.Theory

module SMT.Script (theory : Theory) where

open import SMT.Script.Base theory public
open import SMT.Script.Show theory public
open import SMT.Script.Reflection theory public
