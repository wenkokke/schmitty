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

private
  variable
    σ : Sort
    Σ : Signature σ
    φ φ′ : CoreSort
    Φ : Signature φ

CORE-injective : CORE φ ≡ CORE φ′ → φ ≡ φ′
CORE-injective refl = refl

_≟-Sort_ : (σ σ′ : Sort) → Dec (σ ≡ σ′)
CORE φ ≟-Sort CORE φ′ = Dec.map (equivalence (cong CORE) CORE-injective) (φ ≟-CoreSort φ′)
CORE φ ≟-Sort INT     = no (λ ())
INT    ≟-Sort CORE φ  = no (λ ())
INT    ≟-Sort INT     = yes refl

showSort : Sort → String
showSort (CORE φ) = showCoreSort φ
showSort INT      = "Int"

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


------------
-- Values --
------------

Value : Sort → Set
Value (CORE φ) = CoreValue φ
Value INT      = ℤ


-------------
-- Parsers --
-------------

parseSort : ∀[ Parser Sort ]
parseSort = (CORE <$> parseCoreSort) <|> pINT
  where
    pINT = withSpaces (INT <$ text "Int")

_ : parseSort parses "Bool"
_ = ! BOOL

_ : parseSort parses "Int"
_ = ! INT

parseInt : ∀[ Parser ℤ ]
parseInt = withSpaces (readPos <|> readNeg)
  where
    readPos readNeg : ∀[ Parser ℤ ]
    readPos = Int.+_ <$> decimalℕ
    readNeg = Int.-_ <$> parens (box (text "-" &> box spaces &> box readPos))

parseValue : (σ : Sort) → ∀[ Parser (Value σ) ]
parseValue (CORE φ) = parseCoreValue φ
parseValue INT      = parseInt

_ : parseValue INT parses "1"
_ = ! + 1

_ : parseValue INT parses "0"
_ = ! + 0

_ : parseValue INT parses "(- 1)"
_ = ! -[1+ 0 ]

quoteSort : Sort → Term
quoteSort (CORE φ) = con (quote CORE) (vArg (quoteCoreSort φ) ∷ [])
quoteSort INT      = con (quote INT) []

quoteInt : ℤ → Term
quoteInt (+ n)    = con (quote +_) (vArg (lit (nat n)) ∷ [])
quoteInt -[1+ n ] = con (quote -[1+_]) (vArg (lit (nat n)) ∷ [])

quoteValue : (σ : Sort) → Value σ → Term
quoteValue (CORE φ) = quoteCoreValue φ
quoteValue INT      = quoteInt


---------------
-- Instances --
---------------

baseTheory : BaseTheory
BaseTheory.Sort       baseTheory = Sort
BaseTheory._≟-Sort_   baseTheory = _≟-Sort_
BaseTheory.BOOL       baseTheory = BOOL
BaseTheory.Value      baseTheory = Value
BaseTheory.Literal    baseTheory = Literal
BaseTheory.Identifier baseTheory = Identifier
BaseTheory.quoteSort  baseTheory = quoteSort
BaseTheory.quoteValue baseTheory = quoteValue

printable : Printable baseTheory
Printable.showSort       printable = showSort
Printable.showLiteral    printable = showLiteral
Printable.showIdentifier printable = showIdentifier

parsable : Parsable baseTheory
Parsable.parseSort   parsable = parseSort
Parsable.parseValue  parsable = parseValue

theory : Theory
Theory.baseTheory theory = baseTheory
Theory.printable  theory = printable
Theory.parsable   theory = parsable
