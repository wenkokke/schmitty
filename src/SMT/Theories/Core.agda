module SMT.Theories.Core where

open import Data.Bool.Base as Bool using (Bool; false; true)
open import Data.List.Base as List using (List; _∷_; [])
open import Data.String.Base as String using (String)
open import Function using (id)
open import Reflection
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theory
open import SMT.Logics
open import Text.Parser.String


-- Sorts

data CoreSort : Set where
  BOOL : CoreSort

showCoreSort : CoreSort → String
showCoreSort BOOL = "Bool"


-- Literals

data CoreLiteral : CoreSort → Set where
  bool : Bool → CoreLiteral BOOL

showCoreLiteral : {σ : CoreSort} → CoreLiteral σ → String
showCoreLiteral (bool false) = "false"
showCoreLiteral (bool true)  = "true"


-- Identifiers

data CoreIdentifier : {σ : CoreSort} (Σ : Signature σ) → Set where
  not     : CoreIdentifier (Op₁ BOOL)
  implies : CoreIdentifier (Op₂ BOOL)
  and     : CoreIdentifier (Op₂ BOOL)
  or      : CoreIdentifier (Op₂ BOOL)
  xor     : CoreIdentifier (Op₂ BOOL)

showCoreIdentifier : {σ : CoreSort} {Σ : Signature σ} → CoreIdentifier Σ → String
showCoreIdentifier not     = "not"
showCoreIdentifier implies = "=>"
showCoreIdentifier and     = "and"
showCoreIdentifier or      = "or"
showCoreIdentifier xor     = "xor"


-- Parsers

CoreValue : CoreSort → Set
CoreValue BOOL = Bool

_≟-CoreSort_ : (φ φ′ : CoreSort) → Dec (φ ≡ φ′)
BOOL ≟-CoreSort BOOL = yes refl

parseCoreSort : ∀[ Parser CoreSort ]
parseCoreSort = pBOOL
  where
    pBOOL = withSpaces (BOOL <$ text "Bool")

readBool : ∀[ Parser Bool ]
readBool = true  <$ lexeme "true"
       <|> false <$ lexeme "false"

parseCoreValue : (φ : CoreSort) → ∀[ Parser (CoreValue φ) ]
parseCoreValue BOOL = readBool

quoteBool : Bool → Term
quoteBool false = con (quote false) []
quoteBool true  = con (quote true)  []

quoteCoreSort : CoreSort → Term
quoteCoreSort BOOL = con (quote BOOL) []

quoteCoreValue : (φ : CoreSort) → CoreValue φ → Term
quoteCoreValue BOOL = quoteBool


-- Instances

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
Theory.baseTheory coreTheory = coreBaseTheory
Theory.printable  coreTheory = corePrintable
Theory.parsable   coreTheory = coreParsable
