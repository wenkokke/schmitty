{-# OPTIONS --without-K --safe #-}

module SMT.Theories.Reals where

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
   REAL  : Sort

open Sorts Sort CORE

showSort : Sort → String
showSort (CORE φ) = showCoreSort φ
showSort REAL     = "Real"

private
  variable
    σ : Sort
    Σ : Signature σ
    φ : CoreSort
    Φ : Signature φ


-- Literals

data Literal : Sort → Set where
  core : CoreLiteral φ → Literal (CORE φ)
  real : ℕ → Literal REAL

open Literals Sort CORE Literal core

showLiteral : Literal σ → String
showLiteral (core x) = showCoreLiteral x
showLiteral (real x) = showℕ x

private
  variable
    l : Literal σ


-- Identifiers

data Identifier : (Σ : Signature σ) → Set where
  -- Core theory
  core : CoreIdentifier Φ → Identifier (map CORE Φ)
  eq   : Identifier (Rel REAL)
  neq  : Identifier (Rel REAL)
  ite  : Identifier (ITE σ)
  -- Reals theory
  neg  : Identifier (Op₁ REAL)
  sub  : Identifier (Op₂ REAL)
  add  : Identifier (Op₂ REAL)
  mul  : Identifier (Op₂ REAL)
  div  : Identifier (Op₂ REAL)
  leq  : Identifier (Rel REAL)
  lt   : Identifier (Rel REAL)
  geq  : Identifier (Rel REAL)
  gt   : Identifier (Rel REAL)

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
