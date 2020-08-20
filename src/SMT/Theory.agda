module SMT.Theory where

open import Level
open import Data.List as List using (List; _∷_; [])
open import Data.String using (String)


record Signature {s} {Sort : Set s} (σ : Sort) : Set s where
  field
    ArgTypes : List Sort

open Signature public


module _ {s} {Sort : Set s} where

  infix 3 _↦_

  _↦_ : (σs : List Sort) (σ : Sort) → Signature σ
  Σ ↦ _ = record { ArgTypes = Σ }

  Op₁ : (σ : Sort) → Signature σ
  Op₁ σ = σ ∷ [] ↦ σ

  Op₂ : (σ : Sort) → Signature σ
  Op₂ σ = σ ∷ σ ∷ [] ↦ σ

  map : ∀ {c} {CoreSort : Set c} {φ : CoreSort} (CORE : CoreSort → Sort) → Signature φ → Signature (CORE φ)
  map CORE Φ = record { ArgTypes = List.map CORE (ArgTypes Φ) }

record Theory (s i l : Level) : Set (suc (s ⊔ i ⊔ l)) where
  field
    Sort       : Set s
    BOOL       : Sort
    Literal    : Sort → Set l
    Identifier : {σ : Sort} → Signature σ → Set i

record Printable {s i l : Level} (theory : Theory s i l) : Set (suc (s ⊔ i ⊔ l)) where
  open Theory theory
  field
    showSort       : Sort → String
    showLiteral    : {σ : Sort} → Literal σ → String
    showIdentifier : {σ : Sort} {Σ : Signature σ} → Identifier Σ → String
