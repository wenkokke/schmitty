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
  Rel σ = record { ArgSorts = σ ∷ σ ∷ [] }

  ITE : (σ : Sort) → Signature σ
  ITE σ = record { ArgSorts = BOOL ∷ σ ∷ σ ∷ [] }

  liftCoreSignature : ∀ {φ} → Signature φ → Signature (CORE φ)
  liftCoreSignature Φ = record { ArgSorts = List.map CORE (ArgSorts Φ) }


module Identifiers
  (Sort : Set)
  (CORE : CoreSort → Sort)
  (Identifier : ∀ {σ} (Σ : Signature σ) → Set)
  (coreIdentifier : {φ : CoreSort} {Φ : Signature φ} → CoreIdentifier Φ → Identifier (map CORE Φ))
  where

  open Sorts Sort CORE

  true : Identifier (Op₀ BOOL)
  true = coreIdentifier Core.true

  false : Identifier (Op₀ BOOL)
  false = coreIdentifier Core.false

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
