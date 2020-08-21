module SMT.Theories.Ints where

open import Data.Bool.Base as Bool using (Bool; false; true)
open import Data.Integer.Base as Int using (ℤ; +_; -[1+_])
open import Data.Nat.Base as Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List as List using (List; _∷_; [])
open import Data.String as String using (String)
open import Function.Equivalence using (equivalence)
open import Reflection using (Term; con; lit; nat; vArg)
open import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import SMT.Theory
open import SMT.Theories.Core hiding (BOOL)
open import SMT.Theories.Core.Extensions
open import Text.Parser.String


-- Sort

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
    φ φ′ : CoreSort
    Φ : Signature φ


CORE-injective : CORE φ ≡ CORE φ′ → φ ≡ φ′
CORE-injective refl = refl

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


-------------
-- Parsers --
-------------

_≟-Sort_ : (σ σ′ : Sort) → Dec (σ ≡ σ′)
CORE φ ≟-Sort CORE φ′ = Dec.map (equivalence (cong CORE) CORE-injective) (φ ≟-CoreSort φ′)
CORE φ ≟-Sort INT     = no (λ ())
INT    ≟-Sort CORE φ  = no (λ ())
INT    ≟-Sort INT     = yes refl

readSort : ∀[ Parser Sort ]
readSort = (CORE <$> readCoreSort) <|> pINT
  where
    pINT = withSpaces (INT <$ text "Int")

Value : Sort → Set
Value (CORE φ) = CoreValue φ
Value INT      = ℤ

readValue : (σ : Sort) → ∀[ Parser (Value σ) ]
readValue (CORE φ) = readCoreValue φ
readValue INT      = decimalℤ

quoteInt : ℤ → Term
quoteInt (+ n)    = con (quote +_) (vArg (lit (nat n)) ∷ [])
quoteInt -[1+ n ] = con (quote -[1+_]) (vArg (lit (nat n)) ∷ [])

quoteValue : (σ : Sort) → Value σ → Term
quoteValue (CORE φ) = quoteCoreValue φ
quoteValue INT      = quoteInt


---------------
-- Instances --
---------------

theory : Theory
Theory.Sort       theory = Sort
Theory.BOOL       theory = BOOL
Theory.Literal    theory = Literal
Theory.Identifier theory = Identifier

printable : Printable theory
Printable.showSort       printable = showSort
Printable.showLiteral    printable = showLiteral
Printable.showIdentifier printable = showIdentifier

parsable : Parsable theory
Parsable._≟-Sort_   parsable = _≟-Sort_
Parsable.readSort   parsable = readSort
Parsable.Value      parsable = Value
Parsable.readValue  parsable = readValue
Parsable.quoteValue parsable = quoteValue
