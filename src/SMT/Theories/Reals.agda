module SMT.Theories.Reals where

open import Data.Bool.Base as Bool using (Bool; false; true; if_then_else_)
open import Data.Integer as Int using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Float as Float using (Float)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat as Nat using (ℕ)
import Data.Nat.Show as Nat using (show)
open import Data.List as List using (List; []; _∷_)
open import Data.Product as Prod using (Σ-syntax; -,_; _×_; _,_)
open import Data.String as String using (String)
open import Function.Equivalence using (equivalence)
open import Relation.Nullary using (Dec; yes; no)
import Reflection as Rfl
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong)
open import SMT.Theory
open import SMT.Theories.Core as Core hiding (BOOL)
open import SMT.Theories.Core.Extensions
import SMT.Utils.Float as Float
open import Text.Parser.String


-----------
-- Sorts --
-----------

data Sort : Set where
   CORE : (φ : CoreSort) → Sort
   REAL  : Sort

pattern `CORE φ = Rfl.con (quote CORE) (Rfl.vArg φ ∷ [])
pattern `REAL   = Rfl.con (quote REAL) []

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

quoteSort : Sort → Rfl.Term
quoteSort (CORE φ) = `CORE (quoteCoreSort φ)
quoteSort REAL     = `REAL

sorts : List Sort
sorts = REAL ∷ List.map CORE coreSorts


------------
-- Values --
------------

Value : Sort → Set
Value (CORE φ) = CoreValue φ
Value REAL     = Float

-- |Parse a rational number as a Float.
--
--  NOTE: We're not taking the fixpoint over expressions,
--        since it seems that SMT solvers output the numbers
--        in a normal form with negation after division.
--
parseRat : ∀[ Parser Float ]
parseRat = pNum <|> pDiv <|> pNeg
  where
    pNum pDiv pNeg : ∀[ Parser Float ]
    pNum = withSpaces (Float.fromℕ <$> (decimalℕ <& box (text ".0")))
    pDiv = withSpaces (parens (box (text "/" &> box (Float._÷_ <$> pNum <*> box pNum))))
    pNeg = withSpaces (parens (box (text "-" &> box (Float.-_ <$> (pNum <|> pDiv)))))

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
_ = ! 1.0

_ : parseValue REAL parses "(/ 1.0 2.0)"
_ = ! 0.5

_ : parseValue REAL parses "(- (/ 1.0 2.0))"
_ = ! -0.5

_ : parseValue REAL rejects "10"
_ = _

private
  pattern `nat    n = Rfl.lit (Rfl.nat n)
  pattern `float  f = Rfl.lit (Rfl.float f)
  pattern `+_     n = Rfl.con (quote +_) (Rfl.vArg (`nat n) ∷ [])
  pattern `-[1+_] n = Rfl.con (quote -[1+_]) (Rfl.vArg (`nat n) ∷ [])

quoteFloat : Float → Rfl.Term
quoteFloat f = `float f

quoteValue : (σ : Sort) → Value σ → Rfl.Term
quoteValue (CORE φ) = quoteCoreValue φ
quoteValue REAL     = quoteFloat


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

checkLiteral : (σ : Sort) → Rfl.Term → Maybe (Literal σ)
checkLiteral (CORE φ) x          = Maybe.map core (checkCoreLiteral φ x)
checkLiteral REAL     (`float f) = just (float f)
checkLiteral REAL     _          = nothing

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
  pattern `eq  = quote Eq._≡_
  pattern `neq = quote Eq._≢_
  -- NOTE: We're interpreting BOOL to be Set. Unfortunately, that means that `ite`
  --       cannot really be given a sensible interpretation. (Unless, perhaps, we
  --       involve Dec.)
  --
  -- pattern `ite = ?
  pattern `neg = quote Float.-_
  pattern `sub = quote Float._-_
  pattern `add = quote Float._+_
  pattern `mul = quote Float._*_
  pattern `div = quote Float._÷_
  -- NOTE: Float modulo is currently not defined in the standard library, so we
  --       don't map them here.
  --
  -- pattern `mod = ?
  --
  -- NOTE: Float relations are currently not defined in the standard library, so
  --       provide quick and dirty definitions in SMT.Utils.Float, which are
  --       mapped below. These should be replaced once proper orderings on Float
  --       become available in the standard library.
  pattern `leq = quote Float._≤_
  pattern `lt  = quote Float._<_
  pattern `geq = quote Float._≥_
  pattern `gt  = quote Float._>_

checkIdentifier : (σ : Sort) → Rfl.Name → Maybe (Σ[ Σ ∈ Signature σ ] Identifier Σ)
checkIdentifier BOOL     `eq  = just (-, eq)
checkIdentifier BOOL     `neq = just (-, neq)
checkIdentifier REAL     `neg = just (-, neg)
checkIdentifier REAL     `sub = just (-, sub)
checkIdentifier REAL     `add = just (-, add)
checkIdentifier REAL     `mul = just (-, mul)
checkIdentifier REAL     `div = just (-, div)
checkIdentifier BOOL     `leq = just (-, leq)
checkIdentifier BOOL     `lt  = just (-, lt)
checkIdentifier BOOL     `geq = just (-, geq)
checkIdentifier BOOL     `gt  = just (-, gt)
checkIdentifier REAL      _   = nothing
checkIdentifier (CORE φ)  x   =
  Maybe.map (Prod.map fromCoreSignature core) (checkCoreIdentifier φ x)

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

reflectable : Reflectable baseTheory
Reflectable.sorts           reflectable = sorts
Reflectable.checkLiteral    reflectable = checkLiteral
Reflectable.checkIdentifier reflectable = checkIdentifier

theory : Theory
Theory.baseTheory  theory = baseTheory
Theory.printable   theory = printable
Theory.parsable    theory = parsable
Theory.reflectable theory = reflectable
