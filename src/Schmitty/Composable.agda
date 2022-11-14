{-# OPTIONS --safe --without-K #-}

module Schmitty.Composable where

open import Level using (Level; Lift)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Product as Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base as Sum using (_⊎_)
open import Data.These.Base as These using (These; this; that; these)
open import Function using (id; _∘_)
open import Relation.Unary using (IUniversal; _⇒_; _∪_)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)


private
  variable
    ℓ ℓ′ : Level
    I J  : Set ℓ


-- Signatures

record Signature (ℓ : Level) (I J : Set ℓ) : Set (Level.suc ℓ) where
  constructor _▹_
  field
    Shape : I → Set
    Param : {i : I} → Shape i → List J

open Signature public

⟦_⟧σ : Signature ℓ I J → (J → Set ℓ′) → (I → Set (ℓ Level.⊔ ℓ′))
⟦ Shape ▹ Param ⟧σ P i = Σ[ s ∈ Shape i ] All P (Param s)

infixr 5 _∙σ_

_∙σ_ : Signature ℓ I J → Signature ℓ I J → Signature ℓ I J
Shape (σ₁ ∙σ σ₂)              = Shape σ₁ ∪ Shape σ₂
Param (σ₁ ∙σ σ₂) (Sum.inj₁ s) = Param σ₁ s
Param (σ₁ ∙σ σ₂) (Sum.inj₂ s) = Param σ₂ s


-- Algebras

record Algebra (σ : Signature ℓ I I) (P : I → Set ℓ′) : Set (ℓ Level.⊔ ℓ′) where
  field
    ⟦_⟧α : ∀[ ⟦ σ ⟧σ P ⇒ P ]

open Algebra public

infixr 5 _∙α_

_∙α_ : {σ₁ σ₂ : Signature ℓ I I} {P : I → Set ℓ′} → Algebra σ₁ P → Algebra σ₂ P  → Algebra (σ₁ ∙σ σ₂) P
⟦ α₁ ∙α α₂ ⟧α (Sum.inj₁ s , param) = ⟦ α₁ ⟧α (s , param)
⟦ α₁ ∙α α₂ ⟧α (Sum.inj₂ s , param) = ⟦ α₂ ⟧α (s , param)


-- Fixpoints

data μ (σ : Signature ℓ I I) : I → Set ℓ where
  ⟦_⟧μ : ∀[ ⟦ σ ⟧σ (μ σ) ⇒ μ σ ]

μ-Algebra : (σ : Signature ℓ I I) → Algebra σ (μ σ)
⟦ μ-Algebra σ ⟧α = ⟦_⟧μ


-- Subsignatures

infix 4 _≼_

record _≼_ (σ₁ σ₂ : Signature ℓ I J) : Set (Level.suc ℓ) where
  field
    inj  : {P : J → Set ℓ} → ∀[ ⟦ σ₁ ⟧σ P ⇒ ⟦ σ₂ ⟧σ P ]
    proj : {P : J → Set ℓ} → ∀[ ⟦ σ₂ ⟧σ P ⇒ Maybe ∘ ⟦ σ₁ ⟧σ P ]

  field
    proj-inj : {P : J → Set ℓ} {i : I} {x : ⟦ σ₁ ⟧σ P i} →
               proj (inj x) ≡ just x

    inj-proj : {P : J → Set ℓ} {i : I} {x : ⟦ σ₁ ⟧σ P i} {y : ⟦ σ₂ ⟧σ P i} →
               proj y ≡ just x → inj x ≡ y

open _≼_ public


-- Automatic injection

inject : {σ₁ σ₂ : Signature ℓ I I} → ⦃ σ₁ ≼ σ₂ ⦄ → ∀[ ⟦ σ₁ ⟧σ (μ σ₂) ⇒ μ σ₂ ]
inject ⦃ σ₁≼σ₂ ⦄ x = ⟦ inj σ₁≼σ₂ x ⟧μ

instance
  ≼-refl : {σ : Signature ℓ I J} → σ ≼ σ
  inj      ≼-refl         = id
  proj     ≼-refl         = just
  proj-inj ≼-refl         = Eq.refl
  inj-proj ≼-refl Eq.refl = Eq.refl

instance
  ≼-injectˡ : {σ₁ σ₂ : Signature ℓ I J} → σ₁ ≼ σ₁ ∙σ σ₂
  inj      ≼-injectˡ (s , param) = (Sum.inj₁ s , param)
  proj     ≼-injectˡ (Sum.inj₁ s , param) = just (s , param)
  proj     ≼-injectˡ (Sum.inj₂ s , param) = nothing
  proj-inj ≼-injectˡ                                    = Eq.refl
  inj-proj ≼-injectˡ {y = (Sum.inj₁ s , param)} Eq.refl = Eq.refl

instance
  ≼-injectʳ : {σ σ₁ σ₂ : Signature ℓ I J} → ⦃ σ ≼ σ₂ ⦄ → σ ≼ σ₁ ∙σ σ₂
  inj      (≼-injectʳ ⦃ σ≼σ₂ ⦄) x with inj σ≼σ₂ x
  inj      (≼-injectʳ ⦃ σ≼σ₂ ⦄) x | (s , param) = (Sum.inj₂ s , param)
  proj     (≼-injectʳ ⦃ σ≼σ₂ ⦄) (Sum.inj₁ s , param) = nothing
  proj     (≼-injectʳ ⦃ σ≼σ₂ ⦄) (Sum.inj₂ s , param) = proj σ≼σ₂ (s , param)
  proj-inj (≼-injectʳ ⦃ σ≼σ₂ ⦄) = proj-inj σ≼σ₂
  inj-proj (≼-injectʳ ⦃ σ≼σ₂ ⦄) {x = x} {y = (Sum.inj₂ s , param)} projy≡x
    rewrite inj-proj σ≼σ₂ {x = x} {y = (s , param)} projy≡x = Eq.refl

-- -}
