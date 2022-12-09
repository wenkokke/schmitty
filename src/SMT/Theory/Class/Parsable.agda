-------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Defines the `Parsable` class, which provides parsers that parse the sorts
-- and values output as part of the SMT-LIB model.
--------------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}
module SMT.Theory.Class.Parsable where

open import SMT.Theory.Base
open import Text.Parser.String using (IUniversal; Parser)


record Parsable (theory : Theory) : Set₁ where
  open Theory theory
  field
    parseSort  : ∀[ Parser Sort ]
    parseValue : (σ : Sort) → ∀[ Parser (Value σ) ]
