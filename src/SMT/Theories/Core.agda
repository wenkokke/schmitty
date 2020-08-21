module SMT.Theories.Core where

open import Data.Bool.Base as Bool using (Bool; false; true)
open import Data.List.Base as List using (List; _∷_; [])
open import Data.String.Base as String using (String)
open import Function using (id)
open import Reflection
open import SMT.Theory
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

readBool : ∀[ Parser Bool ]
readBool = withSpaces (pTrue <|> pFalse)
  where
    pTrue  = true  <$ text "true"
    pFalse = false <$ text "false"

readCoreValue : (φ : CoreSort) → ∀[ Parser (CoreValue φ) ]
readCoreValue BOOL = readBool

quoteBool : Bool → Term
quoteBool false = con (quote false) []
quoteBool true = con (quote true) []

quoteCoreValue : (φ : CoreSort) → CoreValue φ → Term
quoteCoreValue BOOL = quoteBool


-- Instances

coreTheory : Theory
Theory.Sort       coreTheory = CoreSort
Theory.BOOL       coreTheory = BOOL
Theory.Literal    coreTheory = CoreLiteral
Theory.Identifier coreTheory = CoreIdentifier

corePrintable : Printable coreTheory
Printable.showSort       corePrintable = showCoreSort
Printable.showLiteral    corePrintable = showCoreLiteral
Printable.showIdentifier corePrintable = showCoreIdentifier

coreParsable : Parsable coreTheory
Parsable.Value      coreParsable = CoreValue
Parsable.readValue  coreParsable = readCoreValue
Parsable.quoteValue coreParsable = quoteCoreValue
