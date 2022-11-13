{-# OPTIONS --safe --without-K #-}

module Schmitty.Composable.Core where

open import Level using (Level)
open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_; ⊆-refl; ⊆-trans)

private
  variable
    ℓ ℓ′ : Level

Pred : (A : Set ℓ) → Set (Level.suc ℓ)
Pred {ℓ} A = A → Set ℓ

Ctx = List

{- A notion of types with preorders -}
module _ where

  record Rel₂ {a} (ℓ : Level) (A : Set a) : Set (a Level.⊔ Level.suc ℓ) where
    field
      R     : A → A → Set ℓ
      refl  : ∀ {x}                     → R x x
      trans : ∀ {x y z} → R x y → R y z → R x z

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
