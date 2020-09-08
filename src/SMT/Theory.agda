module SMT.Theory where

open import Level
open import Data.List as List using (List; _∷_; [])
open import Data.String as String using (String)
open import Data.Maybe as Maybe using (Maybe)
open import Data.Product as Prod using (Σ-syntax)
open import Function using (_∘_)
import Reflection as Rfl
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Text.Parser.String


record Signature {Sort : Set} (σ : Sort) : Set where
  field
    ArgTypes : List Sort

open Signature public


module _ {Sort : Set} where

  infix 3 _↦_

  _↦_ : (σs : List Sort) (σ : Sort) → Signature σ
  Σ ↦ _ = record { ArgTypes = Σ }

  Op₁ : (σ : Sort) → Signature σ
  Op₁ σ = σ ∷ [] ↦ σ

  Op₂ : (σ : Sort) → Signature σ
  Op₂ σ = σ ∷ σ ∷ [] ↦ σ

  map : {CoreSort : Set} {φ : CoreSort} (CORE : CoreSort → Sort) → Signature φ → Signature (CORE φ)
  map CORE Φ = record { ArgTypes = List.map CORE (ArgTypes Φ) }


record BaseTheory : Set₁ where
  field
    Sort         : Set
    _≟-Sort_     : (σ σ′ : Sort) → Dec (σ ≡ σ′)
    BOOL         : Sort
    Value        : Sort → Set
    Literal      : Sort → Set
    Identifier   : {σ : Sort} → Signature σ → Set
    quoteSort    : Sort → Rfl.Term
    quoteValue   : (σ : Sort) → Value σ → Rfl.Term

record Printable (baseTheory : BaseTheory) : Set where
  open BaseTheory baseTheory
  field
    showSort       : Sort → String
    showLiteral    : {σ : Sort} → Literal σ → String
    showIdentifier : {σ : Sort} {Σ : Signature σ} → Identifier Σ → String

record Parsable (baseTheory : BaseTheory) : Set₁ where
  open BaseTheory baseTheory
  field
    parseSort  : ∀[ Parser Sort ]
    parseValue : (σ : Sort) → ∀[ Parser (Value σ) ]

record Theory : Set₁ where
  field
    baseTheory  : BaseTheory
    printable   : Printable   baseTheory
    parsable    : Parsable    baseTheory

  open BaseTheory  baseTheory  public
  open Printable   printable   public
  open Parsable    parsable    public


record Reflectable (theory : Theory) : Set where
  open Theory theory
  field
    sorts           : List Sort
    checkLiteral    : (σ : Sort) → Rfl.Term → Maybe (Literal σ)
    checkIdentifier : (σ : Sort) → Rfl.Name → Maybe (Σ[ Σ ∈ Signature σ ] Identifier Σ)


-----------------------
-- Printer utilities --
-----------------------

-- |Create an S-expression from a list of strings.
--
-- @
--   mkSTerm ("*" ∷ "4" ∷ "5") ≡ "(* 4 5)"
-- @
--
mkSTerm : List String → String
mkSTerm = String.parens ∘ String.unwords
