{-# OPTIONS --guardedness #-}

--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Defines the `Theory` instance for the theory of integers, called `theory`.
--------------------------------------------------------------------------------

module SMT.Theories.Ints.Base where

open import Data.Bool.Base as Bool using (Bool; false; true)
open import Data.Integer as Int using (ℤ; +_; -[1+_])
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.Nat.Base as Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List as List using (List; _∷_; [])
open import Data.String as String using (String)
open import Function.Equivalence using (equivalence)
import Reflection as Rfl
open import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)
open import SMT.Theory
open import SMT.Theories.Core as Core hiding (BOOL; theory)
open import SMT.Theories.Core.Extensions
open import Text.Parser.String


-----------
-- Sorts --
-----------

data Sort : Set where
   CORE : (φ : CoreSort) → Sort
   INT  : Sort

pattern `CORE φ = Rfl.con (quote CORE) (Rfl.vArg φ ∷ [])
pattern `INT    = Rfl.con (quote INT) []

open Sorts Sort CORE public hiding (BOOL)

pattern BOOL = CORE Core.BOOL

private
  variable
    σ σ′ : Sort
    Σ Σ′ : Signature σ
    φ φ′ : CoreSort
    Φ Φ′ : Signature φ

CORE-injective : CORE φ ≡ CORE φ′ → φ ≡ φ′
CORE-injective refl = refl

_≟-Sort_ : (σ σ′ : Sort) → Dec (σ ≡ σ′)
CORE φ ≟-Sort CORE φ′ = Dec.map (equivalence (PropEq.cong CORE) CORE-injective) (φ ≟-CoreSort φ′)
CORE φ ≟-Sort INT     = no (λ ())
INT    ≟-Sort CORE φ  = no (λ ())
INT    ≟-Sort INT     = yes refl

showSort : Sort → String
showSort (CORE φ) = showCoreSort φ
showSort INT      = "Int"

parseSort : ∀[ Parser Sort ]
parseSort = CORE <$> parseCoreSort
        <|> INT  <$  lexeme "Int"

_ : parseSort parses "Bool"
_ = ! BOOL

_ : parseSort parses "Int"
_ = ! INT

_ : parseSort rejects "Real"
_ = _

quoteSort : Sort → Rfl.Term
quoteSort (CORE φ) = `CORE (quoteCoreSort φ)
quoteSort INT      = `INT


------------
-- Values --
------------

Value : Sort → Set
Value (CORE φ) = CoreValue φ
Value INT      = ℤ

parseInt : ∀[ Parser ℤ ]
parseInt = withSpaces (pPos <|> pNeg)
  where
    pPos pNeg : ∀[ Parser ℤ ]
    pPos = Int.+_ <$> decimalℕ
    pNeg = Int.-_ <$> parens (box (text "-" &> box spaces &> box pPos))

parseValue : (σ : Sort) → ∀[ Parser (Value σ) ]
parseValue (CORE φ) = parseCoreValue φ
parseValue INT      = parseInt

_ : parseValue BOOL parses "true"
_ = ! UNIT

_ : parseValue BOOL parses "false"
_ = ! EMPTY

_ : parseValue BOOL rejects "kitty"
_ = _

_ : parseValue INT parses "1"
_ = ! + 1

_ : parseValue INT parses "0"
_ = ! + 0

_ : parseValue INT parses "(- 1)"
_ = ! -[1+ 0 ]

_ : parseValue INT rejects "1.0"
_ = _

private
  pattern `nat    n = Rfl.lit (Rfl.nat n)
  pattern `+_     n = Rfl.con (quote +_) (Rfl.vArg (`nat n) ∷ [])
  pattern `-[1+_] n = Rfl.con (quote -[1+_]) (Rfl.vArg (`nat n) ∷ [])

quoteInt : ℤ → Rfl.Term
quoteInt (+ n)    = `+ n
quoteInt -[1+ n ] = `-[1+ n ]

quoteValue : (σ : Sort) → Value σ → Rfl.Term
quoteValue (CORE φ) = quoteCoreValue φ
quoteValue INT      = quoteInt


--------------
-- Literals --
--------------

data Literal : Sort → Set where
  core : CoreLiteral φ → Literal (CORE φ)
  nat  : ℕ → Literal INT
  int  : ℤ → Literal INT

showLiteral : Literal σ → String
showLiteral (core x) = showCoreLiteral x
showLiteral (nat  x) = showℕ x
showLiteral (int  x) = showℤ x

private
  variable
    l : Literal σ


-----------------
-- Identifiers --
-----------------

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

open Identifiers Sort CORE Identifier core public

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


---------------
-- Instances --
---------------

theory : Theory
Theory.Sort          theory = Sort
Theory._≟-Sort_      theory = _≟-Sort_
Theory.BOOL          theory = BOOL
Theory.Value         theory = Value
Theory.Literal       theory = Literal
Theory.Identifier    theory = Identifier
Theory.quoteSort     theory = quoteSort
Theory.quoteValue    theory = quoteValue
Theory.interpValue   theory = interpCoreValue

instance
  printable : Printable theory
  Printable.showSort       printable = showSort
  Printable.showLiteral    printable = showLiteral
  Printable.showIdentifier printable = showIdentifier

  parsable : Parsable theory
  Parsable.parseSort   parsable = parseSort
  Parsable.parseValue  parsable = parseValue

  solvable : Solvable theory
  solvable = makeSolvable theory
