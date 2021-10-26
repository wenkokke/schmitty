{-# OPTIONS --guardedness #-}

--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Exports the `Theory` and the `Reflectable` class, as well as the raw theory
-- which is required to implement the `Reflectable` class.
--------------------------------------------------------------------------------

module SMT.Theory where

open import SMT.Theory.Base public
open import SMT.Theory.Class.Parsable public
open import SMT.Theory.Class.Printable public
open import SMT.Theory.Class.Reflectable public
open import SMT.Theory.Class.Solvable public
open import SMT.Theory.Raw.Base public
