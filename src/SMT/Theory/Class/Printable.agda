-------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Defines the `Printable` class, which  provides pretty-printers that print
-- the sorts, literals, and identifiers to their corresponding SMT-LIB terms.
-- To help define these functions, this module also exports `mkSTerm`, which
-- prints a list of strings as an S-expression.
--------------------------------------------------------------------------------

module SMT.Theory.Class.Printable where

open import Data.List using (List)
open import Data.String as String using (String)
open import Function using (_∘_)
open import SMT.Theory.Base


record Printable (theory : Theory) : Set where
  open Theory theory
  field
    showSort       : Sort → String
    showLiteral    : {σ : Sort} → Literal σ → String
    showIdentifier : {σ : Sort} {Σ : Signature σ} → Identifier Σ → String


-----------------------
-- Printer utilities --
-----------------------

-- |Create an S-expression from a list of strings.
--
-- @
--   mkSTerm ("*" ∷ "4" ∷ "5") ≡ "(* 4 5)"
-- @
--
mkSTerm : List String → String
mkSTerm = String.parens ∘ String.unwords
