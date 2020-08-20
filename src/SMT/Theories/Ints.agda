module SMT.Theories.Ints where

open import Data.Bool.Base as Bool using (Bool; false; true)
open import Data.Nat.Base as Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List as List using (List; _∷_; [])
open import Data.String as String using (String)
open import SMT.Theory
open import SMT.Theories.Core.Extensions


-- Sorts

data Sort : Set where
   CORE : (φ : CoreSort) → Sort
   INT  : Sort

open Sorts Sort CORE

showSort : Sort → String
showSort (CORE φ) = showCoreSort φ
showSort INT      = "Int"

private
  variable
    σ : Sort
    Σ : Signature σ
    φ : CoreSort
    Φ : Signature φ


-- Literals

data Literal : Sort → Set where
  core : CoreLiteral φ → Literal (CORE φ)
  int  : ℕ → Literal INT

open Literals Sort CORE Literal core

showLiteral : Literal σ → String
showLiteral (core x) = showCoreLiteral x
showLiteral (int  x) = showℕ x

private
  variable
    l : Literal σ


-- Identifiers

data Identifier : (Σ : Signature σ) → Set where
  -- Core theory
  core : CoreIdentifier Φ → Identifier (map CORE Φ)
  eq   : Identifier (Rel INT)
  neq  : Identifier (Rel INT)
  ite  : Identifier (ITE σ)
  -- Ints theory
  neg  : Identifier (Op₁ INT)
  sub  : Identifier (Op₂ INT)
  add  : Identifier (Op₂ INT)
  mul  : Identifier (Op₂ INT)
  div  : Identifier (Op₂ INT)
  mod  : Identifier (Op₂ INT)
  abs  : Identifier (Op₁ INT)
  leq  : Identifier (Rel INT)
  lt   : Identifier (Rel INT)
  geq  : Identifier (Rel INT)
  gt   : Identifier (Rel INT)

open Identifiers Sort CORE Identifier core

showIdentifier : Identifier Σ → String
showIdentifier (core x) = showCoreIdentifier x
showIdentifier eq       = "="
showIdentifier neq      = "distinct"
showIdentifier ite      = "ite"
showIdentifier neg      = "-"
showIdentifier sub      = "-"
showIdentifier add      = "+"
showIdentifier mul      = "*"
showIdentifier div      = "/"
showIdentifier mod      = "mod"
showIdentifier abs      = "abs"
showIdentifier leq      = "<="
showIdentifier lt       = "<"
showIdentifier geq      = ">="
showIdentifier gt       = ">"

private
  variable
    i : Identifier Σ


-- Instances

theory : Theory _ _ _
Theory.Sort       theory = Sort
Theory.BOOL       theory = BOOL
Theory.Literal    theory = Literal
Theory.Identifier theory = Identifier

printable : Printable theory
Printable.showSort       printable = showSort
Printable.showLiteral    printable = showLiteral
Printable.showIdentifier printable = showIdentifier
