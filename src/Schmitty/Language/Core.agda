{-# OPTIONS --safe --without-K #-}

module Schmitty.Language.Core where

open import Level
open import Data.Nat
open import Data.List

variable a b c′ i o j ℓ ℓ′ : Level
         A : Set a
         B : Set b
         C : Set c′
         I : Set i
         O : Set o
         J : Set j
         P Q : A → Set ℓ
         n m k : ℕ

Pred : (A : Set ℓ) → Set (Level.suc ℓ)
Pred {ℓ} A = A → Set ℓ

Ctx = List


module _ (T : Set) where

  data Cell : Set where
    value   : (s   : T) → Cell
    closure : (s t : T) → Cell

  Sto : Set
  Sto = List Cell

  open import Data.List.Relation.Unary.All

  Env : ∀ {I} → (T → Pred {0ℓ} I) → Ctx T → Pred I
  Env V Γ Σ = All (λ t → V t Σ) Γ


open import Box public
open import Data.List.Relation.Binary.Sublist.Propositional

instance sto-rel : ∀ {A : Set} → Rel₂ _ (Sto A)
Rel₂.R sto-rel     = _⊆_
Rel₂.refl sto-rel  = ⊆-refl
Rel₂.trans sto-rel = ⊆-trans
