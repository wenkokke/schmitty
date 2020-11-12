--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Defines the `Theory` class. The implementation of SMT-LIB terms and scripts
-- is parameterised by an instance of the `Theory` class, which determines the
-- sorts, literals, and identifiers, as well as the links to the SMT-LIB version
-- of the theory.
--
-- The `Theory` class is split up into *three* subclasses:
--
-- - The `BaseTheory` class provides the sorts, literals, and identifiers.
--   Furthermore, it contains the machinery needed to convert models back to
--   Agda terms: `Value` interprets the SMT sorts as Agda types, and `quoteSort`
--   and `quoteValue` quote sorts and values to reflected Agda syntax.
--
--   Finally, the `interpValue` function can be used to adjust the reflected
--   syntax, which can be used to keep the values in `Set`. For instance, see
--   `SMT.Theories.Core.Base`.
--
-- - The `Printable` class provides pretty-printers, which print the sorts,
--   literals, and identifiers to their corresponding SMT-LIB terms. To help
--   define these functions, this module also exports `mkSTerm`, which prints a
--   list of strings as an S-expression.
--
-- - The `Parsable` class provides parsers, which parse the sorts and values
--   output as part of the SMT-LIB model.
--
-- The `Theory` class itself merely combines instances of all three of these
-- classes.
--------------------------------------------------------------------------------

module SMT.Theory.Base where

open import Level
open import Data.List as List using (List; _∷_; [])
open import Data.String as String using (String)
open import Data.Maybe as Maybe using (Maybe)
open import Data.Product as Prod using (Σ-syntax)
open import Function using (_∘_)
import Reflection as Rfl
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Text.Parser.String using (IUniversal; Parser)


record Signature {Sort : Set} (σ : Sort) : Set where
  field
    ArgSorts : List Sort

open Signature public


module _ {Sort : Set} where

  infix 3 _↦_

  _↦_ : (σs : List Sort) (σ : Sort) → Signature σ
  Σ ↦ _ = record { ArgSorts = Σ }

  Op₀ : (σ : Sort) → Signature σ
  Op₀ σ = [] ↦ σ

  Op₁ : (σ : Sort) → Signature σ
  Op₁ σ = σ ∷ [] ↦ σ

  Op₂ : (σ : Sort) → Signature σ
  Op₂ σ = σ ∷ σ ∷ [] ↦ σ

  map : {CoreSort : Set} {φ : CoreSort} (CORE : CoreSort → Sort) → Signature φ → Signature (CORE φ)
  map CORE Φ = record { ArgSorts = List.map CORE (ArgSorts Φ) }


record BaseTheory : Set₁ where
  field
    Sort          : Set
    _≟-Sort_      : (σ σ′ : Sort) → Dec (σ ≡ σ′)
    BOOL          : Sort
    Literal       : Sort → Set
    Identifier    : {σ : Sort} → Signature σ → Set
    quoteSort     : Sort → Rfl.Term

    -- The Value family encodes which Agda map interprets the values returned as
    -- part of a model:
    --
    --   * If the Agda equivalent is in Set₀, Value should return the type
    --     directly, and interpValue should be the identity function.
    --
    --   * If the Agda equivalent is *not* in Set₀, Value should return a
    --     universe encoding of the possible return values, and interpValue
    --     should map the elements of that universe encoding to their intended
    --     interpretation.
    --
    Value       : Sort → Set
    quoteValue  : (σ : Sort) → Value σ → Rfl.Term
    interpValue : Rfl.Term → Rfl.Term

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
