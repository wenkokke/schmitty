module SMT.Theories.Reals where

open import Data.Bool.Base as Bool using (Bool; false; true; if_then_else_)
open import Data.Integer as Int using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Float as Float using (Float)
open import Data.Nat as Nat using (ℕ)
import Data.Nat.Show as Nat using (show)
open import Data.List as List using (List; _∷_; [])
open import Data.Product as Prod using (_×_; _,_)
open import Data.Rational.Unnormalised as Rat using (ℚᵘ; ↥_)
open import Data.String as String using (String)
open import Function.Equivalence using (equivalence)
open import Relation.Nullary using (Dec; yes; no)
open import Reflection using (Term; con; lit; nat; vArg)
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import SMT.Theory
open import SMT.Theories.Core hiding (BOOL)
open import SMT.Theories.Core.Extensions
open import Text.Parser.String


-----------
-- Sorts --
-----------

data Sort : Set where
   CORE : (φ : CoreSort) → Sort
   REAL  : Sort

open Sorts Sort CORE public

private
  variable
    σ σ′ : Sort
    Σ Σ′ : Signature σ
    φ φ′ : CoreSort
    Φ Φ′ : Signature φ

CORE-injective : CORE φ ≡ CORE φ′ → φ ≡ φ′
CORE-injective refl = refl

_≟-Sort_ : (σ σ′ : Sort) → Dec (σ ≡ σ′)
CORE φ ≟-Sort CORE φ′ = Dec.map (equivalence (cong CORE) CORE-injective) (φ ≟-CoreSort φ′)
CORE φ ≟-Sort REAL    = no (λ ())
REAL   ≟-Sort CORE φ  = no (λ ())
REAL   ≟-Sort REAL    = yes refl

showSort : Sort → String
showSort (CORE φ) = showCoreSort φ
showSort REAL     = "Real"

parseSort : ∀[ Parser Sort ]
parseSort = CORE <$> parseCoreSort
        <|> REAL <$  lexeme "Real"

_ : parseSort parses "Bool"
_ = ! BOOL

_ : parseSort rejects "Int"
_ = _

_ : parseSort parses "Real"
_ = ! REAL

quoteSort : Sort → Term
quoteSort (CORE φ) = con (quote CORE) (vArg (quoteCoreSort φ) ∷ [])
quoteSort REAL     = con (quote REAL) []


------------
-- Values --
------------

Value : Sort → Set
Value (CORE φ) = CoreValue φ
Value REAL     = ℚᵘ

private
  -- |Construct a rational number from a natural number
  fromℕ : ℕ → ℚᵘ
  fromℕ n = Rat.mkℚᵘ (+ n) 0

  -- |SMT division (where p ÷ 0 = 0)
  _÷_ : (p q : ℚᵘ) → ℚᵘ
  p ÷ q with ∣ ↥ q ∣ Nat.≟ 0
  ... | yes q≡0 = Rat.0ℚᵘ
  ... | no ¬q≡0 = Rat._÷_ p q {Dec.fromWitnessFalse ¬q≡0}

-- |Parse an unnormalised rational number
--
--  NOTE: We're not taking the fixpoint over expressions,
--        since it seems that SMT solvers output the numbers
--        in a normal form with negation after division.
--
parseRat : ∀[ Parser ℚᵘ ]
parseRat = pNum <|> pDiv <|> pNeg
  where
    pNum pDiv pNeg : ∀[ Parser ℚᵘ ]
    pNum = withSpaces (fromℕ <$> (decimalℕ <& box (text ".0")))
    pDiv = withSpaces (parens (box (text "/" &> box (_÷_ <$> pNum <*> box pNum))))
    pNeg = withSpaces (parens (box (text "-" &> box (Rat.-_ <$> (pNum <|> pDiv)))))

parseValue : (σ : Sort) → ∀[ Parser (Value σ) ]
parseValue (CORE φ) = parseCoreValue φ
parseValue REAL     = parseRat

_ : parseValue BOOL parses "true"
_ = ! true

_ : parseValue BOOL parses "false"
_ = ! false

_ : parseValue BOOL rejects "kitty"
_ = _

_ : parseValue REAL parses "1.0"
_ = ! Rat.1ℚᵘ

_ : parseValue REAL parses "(/ 1.0 2.0)"
_ = ! Rat.½

_ : parseValue REAL parses "(- (/ 1.0 2.0))"
_ = ! Rat.-½

_ : parseValue REAL rejects "10"
_ = _

quoteRat : ℚᵘ → Term
quoteRat (Rat.mkℚᵘ n d-1) =
  con (quote Rat.mkℚᵘ) (vArg (quoteInt n) ∷ vArg (lit (nat d-1)) ∷ [])
  where
    quoteInt : ℤ → Term
    quoteInt (+ n)    = con (quote +_) (vArg (lit (nat n)) ∷ [])
    quoteInt -[1+ n ] = con (quote -[1+_]) (vArg (lit (nat n)) ∷ [])

quoteValue : (σ : Sort) → Value σ → Term
quoteValue (CORE φ) = quoteCoreValue φ
quoteValue REAL     = quoteRat


--------------
-- Literals --
--------------

data Literal : Sort → Set where
  core  : CoreLiteral φ → Literal (CORE φ)
  nat   : ℕ → Literal REAL
  float : Float → Literal REAL

open Literals Sort CORE Literal core public

showLiteral : Literal σ → String
showLiteral (core  x) = showCoreLiteral x
showLiteral (nat   x) = Nat.show x String.++ ".0"
showLiteral (float x) =
  if x Float.<ᵇ 0.0 then mkSTerm ("-" ∷ Float.show (Float.- x) ∷ []) else Float.show x

private
  variable
    l : Literal σ


-----------------
-- Identifiers --
-----------------

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

baseTheory : BaseTheory
BaseTheory.Sort         baseTheory = Sort
BaseTheory._≟-Sort_     baseTheory = _≟-Sort_
BaseTheory.BOOL         baseTheory = BOOL
BaseTheory.Value        baseTheory = Value
BaseTheory.Literal      baseTheory = Literal
BaseTheory.Identifier   baseTheory = Identifier
BaseTheory.quoteSort    baseTheory = quoteSort
BaseTheory.quoteValue   baseTheory = quoteValue

printable : Printable baseTheory
Printable.showSort       printable = showSort
Printable.showLiteral    printable = showLiteral
Printable.showIdentifier printable = showIdentifier

parsable : Parsable baseTheory
Parsable.parseSort  parsable = parseSort
Parsable.parseValue parsable = parseValue

theory : Theory
Theory.baseTheory theory = baseTheory
Theory.printable  theory = printable
Theory.parsable   theory = parsable
