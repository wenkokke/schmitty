{-# OPTIONS --safe --without-K #-}

module Schmitty.Composable.Core where

open import Level using (Level)
open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Schmitty.Composable.Box public using (Rel₂)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_; ⊆-refl; ⊆-trans)

private
  variable
    ℓ ℓ′ : Level

Pred : (A : Set ℓ) → Set (Level.suc ℓ)
Pred {ℓ} A = A → Set ℓ

Ctx = List

module _ (T : Set) where

  data Cell : Set where
    value   : (s   : T) → Cell
    closure : (s t : T) → Cell

  Sto : Set
  Sto = List Cell

  Env : ∀ {I} → (T → Pred {Level.zero} I) → Ctx T → Pred I
  Env V Γ Σ = All (λ t → V t Σ) Γ

instance sto-rel : ∀ {A : Set} → Rel₂ _ (Sto A)
Rel₂.R sto-rel     = _⊆_
Rel₂.refl sto-rel  = ⊆-refl
Rel₂.trans sto-rel = ⊆-trans
