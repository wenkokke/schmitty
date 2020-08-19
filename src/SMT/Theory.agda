module SMT.Theory where

open import Level
open import Data.List using (List)
open import Data.String using (String)

record Signature {s} {Sort : Set s} (σ : Sort) : Set s where
  field
    ArgTypes : List Sort

open Signature public

_↦_ : ∀ {s} {Sort : Set s} (Σ : List Sort) (σ : Sort) → Signature σ
Σ ↦ _ = record { ArgTypes = Σ }

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
