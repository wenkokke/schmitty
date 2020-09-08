module SMT.Theories.Core.Base where


open import Data.Bool.Base as Bool using (Bool; false; true)
open import Data.List.Base as List using (List; _∷_; [])
open import Data.String.Base as String using (String)
import Reflection as Rfl
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theory
open import SMT.Theories.Raw as Raw
open import Text.Parser.String


-----------
-- Sorts --
-----------

data CoreSort : Set where
  BOOL : CoreSort

private
  variable
    φ : CoreSort
    Φ : Signature φ

_≟-CoreSort_ : (φ φ′ : CoreSort) → Dec (φ ≡ φ′)
BOOL ≟-CoreSort BOOL = yes refl

showCoreSort : CoreSort → String
showCoreSort BOOL = "Bool"

parseCoreSort : ∀[ Parser CoreSort ]
parseCoreSort = BOOL <$ lexeme "Bool"

_ : parseCoreSort parses "Bool"
_ = ! BOOL

_ : parseCoreSort rejects "Int"
_ = _

quoteCoreSort : CoreSort → Rfl.Term
quoteCoreSort BOOL = Rfl.con (quote BOOL) []


------------
-- Values --
------------

CoreValue : CoreSort → Set
CoreValue BOOL = Bool

parseBool : ∀[ Parser Bool ]
parseBool = true  <$ lexeme "true"
        <|> false <$ lexeme "false"

parseCoreValue : (φ : CoreSort) → ∀[ Parser (CoreValue φ) ]
parseCoreValue BOOL = parseBool

quoteBool : Bool → Rfl.Term
quoteBool false = Rfl.con (quote false) []
quoteBool true  = Rfl.con (quote true)  []

quoteCoreValue : (φ : CoreSort) → CoreValue φ → Rfl.Term
quoteCoreValue BOOL = quoteBool


--------------
-- Literals --
--------------

data CoreLiteral : CoreSort → Set where
  bool : Bool → CoreLiteral BOOL

showCoreLiteral : CoreLiteral φ → String
showCoreLiteral (bool false) = "false"
showCoreLiteral (bool true)  = "true"


-----------------
-- Identifiers --
-----------------

data CoreIdentifier : (Φ : Signature φ) → Set where
  not     : CoreIdentifier (Op₁ BOOL)
  implies : CoreIdentifier (Op₂ BOOL)
  and     : CoreIdentifier (Op₂ BOOL)
  or      : CoreIdentifier (Op₂ BOOL)
  xor     : CoreIdentifier (Op₂ BOOL)

showCoreIdentifier : CoreIdentifier Φ → String
showCoreIdentifier not     = "not"
showCoreIdentifier implies = "=>"
showCoreIdentifier and     = "and"
showCoreIdentifier or      = "or"
showCoreIdentifier xor     = "xor"


---------------
-- Instances --
---------------

coreBaseTheory : BaseTheory
BaseTheory.Sort         coreBaseTheory = CoreSort
BaseTheory.BOOL         coreBaseTheory = BOOL
BaseTheory._≟-Sort_     coreBaseTheory = _≟-CoreSort_
BaseTheory.Value        coreBaseTheory = CoreValue
BaseTheory.Literal      coreBaseTheory = CoreLiteral
BaseTheory.Identifier   coreBaseTheory = CoreIdentifier
BaseTheory.quoteSort    coreBaseTheory = quoteCoreSort
BaseTheory.quoteValue   coreBaseTheory = quoteCoreValue

corePrintable : Printable coreBaseTheory
Printable.showSort       corePrintable = showCoreSort
Printable.showLiteral    corePrintable = showCoreLiteral
Printable.showIdentifier corePrintable = showCoreIdentifier

coreParsable : Parsable coreBaseTheory
Parsable.parseSort   coreParsable = parseCoreSort
Parsable.parseValue  coreParsable = parseCoreValue

coreTheory : Theory
Theory.baseTheory  coreTheory = coreBaseTheory
Theory.printable   coreTheory = corePrintable
Theory.parsable    coreTheory = coreParsable
