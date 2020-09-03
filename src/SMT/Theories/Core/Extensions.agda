module SMT.Theories.Core.Extensions where


open import Data.Bool.Base as Bool using (Bool)
open import Data.List.Base as List using (List; _∷_; [])
open import SMT.Theory
open import SMT.Theories.Core as Core public
  using ( CoreSort
        ; CoreLiteral
        ; CoreIdentifier
        ; showCoreSort
        ; showCoreLiteral
        ; showCoreIdentifier
        )

module Sorts
  (Sort : Set)
  (CORE : CoreSort → Sort)
  where

  BOOL : Sort
  BOOL = CORE Core.BOOL

  Rel : (σ : Sort) → Signature BOOL
  Rel σ = record { ArgTypes = σ ∷ σ ∷ [] }

  ITE : (σ : Sort) → Signature σ
  ITE σ = record { ArgTypes = BOOL ∷ σ ∷ σ ∷ [] }

  fromCoreSignature : ∀ {φ} → Signature φ → Signature (CORE φ)
  fromCoreSignature Φ = record { ArgTypes = List.map CORE (ArgTypes Φ) }


module Literals
  (Sort : Set)
  (CORE : CoreSort → Sort)
  (Literal : Sort → Set)
  (coreLiteral : ∀ {φ} → CoreLiteral φ → Literal (CORE φ))
  where

  open Sorts Sort CORE

  bool : Bool → Literal BOOL
  bool b = coreLiteral (Core.bool b)


module Identifiers
  (Sort : Set)
  (CORE : CoreSort → Sort)
  (Identifier : ∀ {σ} (Σ : Signature σ) → Set)
  (coreIdentifier : {φ : CoreSort} {Φ : Signature φ} → CoreIdentifier Φ → Identifier (map CORE Φ))
  where

  open Sorts Sort CORE

  not : Identifier (Op₁ BOOL)
  not = coreIdentifier Core.not

  implies : Identifier (Op₂ BOOL)
  implies = coreIdentifier Core.implies

  and : Identifier (Op₂ BOOL)
  and = coreIdentifier Core.and

  or : Identifier (Op₂ BOOL)
  or = coreIdentifier Core.or

  xor : Identifier (Op₂ BOOL)
  xor = coreIdentifier Core.xor
