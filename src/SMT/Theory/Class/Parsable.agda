-------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- TODO
--------------------------------------------------------------------------------

module SMT.Theory.Class.Parsable where

open import SMT.Theory.Base
open import Text.Parser.String using (IUniversal; Parser)


record Parsable (theory : Theory) : Set₁ where
  open Theory theory
  field
    parseSort  : ∀[ Parser Sort ]
    parseValue : (σ : Sort) → ∀[ Parser (Value σ) ]
