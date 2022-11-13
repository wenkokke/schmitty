{-# OPTIONS --safe --without-K #-}

module Schmitty.Language.Signature where

open import Schmitty.Language.Core

open import Data.Nat
open import Data.Product
open import Data.Vec renaming (map to vmap ; zip to vzip)
open import Data.List
open import Data.Sum
open import Data.Maybe

open import Relation.Unary hiding (U ; Pred ; _⊆_)
open import Data.List.Relation.Unary.All renaming (map to map-all)
open import Relation.Binary.PropositionalEquality

open import Function

import      Level as L


--------------------------------------------------------------------------------
--- (Indexed) signatures, and their algebras and folds

{- Non-indexed signatures -}
module _ where

  -- The type of signatures, restricted here to finitely-branching
  -- trees
  record Signature ℓ : Set (L.suc ℓ) where
    constructor _▹_
    field Shape  : Set ℓ
          Arity  : Shape → ℕ

  variable σ σ′ σ₁ σ₂ : Signature ℓ

  open Signature public

  -- Extension/semantics of signatures in `Set`
  ⟦_⟧ : Signature ℓ → Set ℓ′ → Set (ℓ L.⊔ ℓ′)
  ⟦_⟧ {ℓ} {ℓ′} σ X = Σ (Shape σ) λ s → L.Lift (ℓ L.⊔ ℓ′) (Vec X (Arity σ s))

  -- Least fixpoint of signature-encoded functors
  data μ {ℓ} (σ : Signature ℓ) : Set ℓ where
    ⟨_⟩ : ⟦ σ ⟧ (μ σ) → μ σ

  -- Signature sums
  _:+:_ : Signature ℓ → Signature ℓ → Signature ℓ
  Shape (σ₁ :+: σ₂)          = Shape σ₁ ⊎ Shape σ₂
  Arity (σ₁ :+: σ₂) (inj₁ s) = Arity σ₁ s
  Arity (σ₁ :+: σ₂) (inj₂ s) = Arity σ₂ s

{- maps, algebras and folds for non-indexed signatures -}
module _ where

  map-sig : (A → B) → (⟦ σ ⟧ A → ⟦ σ ⟧ B)
  map-sig f (s , L.lift as) = s , L.lift (vmap f as)

  record Algebra (σ : Signature ℓ) (A : Set a) (B : Set b) : Set (ℓ L.⊔ a L.⊔ b) where
    field alg : ⟦ σ ⟧ A → B

  open Algebra public

  mutual
    map-cata : Algebra σ A A → Vec (μ σ) n → Vec A n
    map-cata f []       = []
    map-cata f (a ∷ as) = cata f a ∷ map-cata f as

    cata : Algebra σ A A → μ σ → A
    cata f ⟨ s , L.lift as ⟩ = alg f (s , L.lift (map-cata f as))

  mutual
    map-para : {A : Set a} → Algebra σ (μ σ × A) A → Vec (μ σ) n → Vec A n
    map-para f []       = []
    map-para f (x ∷ xs) = para f x ∷ map-para f xs

    para : {A : Set ℓ} {σ : Signature ℓ′} → Algebra σ (μ σ × A ) A → μ σ → A
    para f ⟨ c , L.lift xs ⟩ = alg f (c , L.lift (vzip xs (map-para f xs)))

  -- Algebra sums
  _⊕_ : Algebra σ₁ A B → Algebra σ₂ A B → Algebra (σ₁ :+: σ₂) A B
  alg (f ⊕ g) (inj₁ s , as) = alg f (s , as)
  alg (f ⊕ g) (inj₂ s , as) = alg g (s , as)


{- Indexed signatures -}
module _ where


  -- The type of indexed signatures, again restricted to
  -- finitely-branching trees
  record ISignature ℓ (I J : Set ℓ) : Set (L.suc ℓ) where
    constructor _▸_
    field Shapeᴵ  : I → Set ℓ
          Indices : {i : I} → Shapeᴵ i → List J

  variable ζ₁ ζ₂ ζ : ISignature ℓ I J

  open ISignature public

  -- Extension/semantics of indexed signatures as functors on indexed sets
  ⟦_⟧ᴵ : ISignature ℓ I O → (O → Set ℓ′) → I → Set (ℓ L.⊔ ℓ′)
  ⟦_⟧ᴵ {ℓ = ℓ} {ℓ′ = ℓ′} ζ X i =
    Σ (Shapeᴵ ζ i) λ s → L.Lift (ℓ L.⊔ ℓ′) (All X (Indices ζ s))

  -- Least fixpoint of signature-encoded functors on indexed sets
  data μᴵ (ζ : ISignature ℓ I I) : I → Set ℓ where
    I⟨_⟩ : ∀[ ⟦ ζ ⟧ᴵ (μᴵ ζ) ⇒ μᴵ ζ ]

  -- Indexed signature sums
  _:++:_ : ISignature ℓ I J → ISignature ℓ I J → ISignature ℓ I J
  Shapeᴵ  (ζ₁ :++: ζ₂)          = Shapeᴵ ζ₁ ∪ Shapeᴵ ζ₂
  Indices (ζ₁ :++: ζ₂) (inj₁ s) = Indices ζ₁ s
  Indices (ζ₁ :++: ζ₂) (inj₂ s) = Indices ζ₂ s

{- maps, algebras and folds for indexed signatures -}
module _ where

  map-sigᴵ :  ∀[ P ⇒ Q ] → ∀[ ⟦ ζ ⟧ᴵ P ⇒ ⟦ ζ ⟧ᴵ Q ]
  map-sigᴵ f (s , as) = s , L.lift (map-all f (L.lower as))

  record IAlgebra (ζ : ISignature ℓ I I) (P : I → Set ℓ) : Set ℓ where
    field ialg : ∀[ ⟦ ζ ⟧ᴵ P ⇒ P ]

  open IAlgebra public

  mutual
    map-foldᴵ : IAlgebra ζ P → ∀[ All (μᴵ ζ) ⇒ All P ]
    map-foldᴵ f []       = []
    map-foldᴵ f (a ∷ as) = foldᴵ f a ∷ map-foldᴵ f as

    foldᴵ : IAlgebra ζ P → ∀[ μᴵ ζ ⇒ P ]
    foldᴵ f I⟨ s , as ⟩ = ialg f (s , L.lift (map-foldᴵ f (L.lower as)))

  -- Indexed algebra sums
  _:⊕:_ : IAlgebra ζ₁ P → IAlgebra ζ₂ P → IAlgebra (ζ₁ :++: ζ₂) P
  ialg (f :⊕: g) (inj₁ s , as) = ialg f (s , as)
  ialg (f :⊕: g) (inj₂ s , as) = ialg g (s , as)



--------------------------------------------------------------------------------
-- Subsignature relations, and instances for automated injections


{- Subsignature relation for non-indexed signatures -}
module _ where

  record _≼_ {ℓ} (σ₁ σ₂ : Signature ℓ) : Set (L.suc ℓ) where
    field inj  : ∀[ ⟦_⟧ {ℓ} {ℓ} σ₁ ⇒ ⟦ σ₂ ⟧ ]
          proj : ∀[ ⟦_⟧ {ℓ} {ℓ} σ₂ ⇒ Maybe ∘ ⟦ σ₁ ⟧ ]

          proj-inj : ∀ {A} {x : ⟦ σ₁ ⟧ A}    → proj (inj x) ≡ just x
          inj-proj : ∀ {A} {x : ⟦ σ₁ ⟧ A}{y} → proj y ≡ just x → inj x ≡ y


{- instances of _≼_ used for automated injections -}
module _ where

  open _≼_

  ≼-trans : ∀ {ℓ} {F G H : Signature ℓ} → F ≼ G → G ≼ H → F ≼ H
  inj  (≼-trans r₁ r₂) = inj r₂ ∘ inj r₁
  proj (≼-trans r₁ r₂) x with proj r₂ x
  ... | nothing = nothing
  ... | just x′ = proj r₁ x′
  proj-inj (≼-trans r₁ r₂) {x = x} with proj-inj r₁ {x = x} | proj-inj r₂ {x = inj r₁ x}
  ... | px₁ | px₂ rewrite px₂ = px₁
  inj-proj (≼-trans r₁ r₂) {x = x} {y = y} p with proj r₂ y | inspect (proj r₂) y
  inj-proj (≼-trans r₁ r₂) {x = x} {y = y} p | just v | [ eq ] = inj-proj r₂ (trans eq (cong just (sym $ inj-proj r₁ p)))

  instance ≼-refl : ∀ {ℓ} {σ : Signature ℓ} → σ ≼ σ
  inj  ≼-refl = id
  proj ≼-refl = just
  proj-inj ≼-refl      = refl
  inj-proj ≼-refl refl = refl

  instance ≼-left : ∀ {ℓ} {σ₁ σ₂ : Signature ℓ} → σ₁ ≼ (σ₁ :+: σ₂)
  inj  ≼-left (s , as)      = inj₁ s , as
  proj ≼-left (inj₁ s , as) = just (s , as)
  proj ≼-left (inj₂ s , as) = nothing
  proj-inj ≼-left                       = refl
  inj-proj ≼-left {y = inj₁ _ , _} refl = refl

  instance ≼-right : ∀ {ℓ} {σ₁ σ₂ σ : Signature ℓ} → ⦃ σ ≼ σ₂ ⦄ → σ ≼ (σ₁ :+: σ₂)
  inj  (≼-right ⦃ sub ⦄) x with inj sub x
  ... | s , as  = inj₂ s , as
  proj (≼-right ⦃ sub ⦄) (inj₁ s , as) = nothing
  proj (≼-right ⦃ sub ⦄) (inj₂ s , as) = proj sub (s , as)
  proj-inj (≼-right ⦃ sub ⦄) = proj-inj sub
  inj-proj (≼-right ⦃ sub ⦄) {x = x} {y = inj₂ s , as} px₁ with inj-proj sub {x = x} {s , as} px₁
  ... | refl = refl

  inject : ⦃ σ₁ ≼ σ ⦄ → ⟦ σ₁ ⟧ (μ σ) → μ σ
  inject ⦃ sub ⦄ x = ⟨ inj sub x ⟩

{- Subsignature relation for indexed signatures -}
module _ where

  record _I≼_ {ℓ} {I J : Set ℓ}(ζ₁ ζ₂ : ISignature ℓ I J) : Set (L.suc ℓ) where
    field Iinj  : ∀ {P} → ∀[ ⟦_⟧ᴵ {ℓ′ = ℓ} ζ₁ P ⇒ ⟦ ζ₂ ⟧ᴵ P ]
          Iproj : ∀ {P} → ∀[ ⟦_⟧ᴵ {ℓ′ = ℓ} ζ₂ P ⇒ Maybe ∘ ⟦ ζ₁ ⟧ᴵ P ]

          Iproj-inj : ∀ {P} {i} {x : ⟦ ζ₁ ⟧ᴵ P i}     → Iproj (Iinj x) ≡ just x
          Iinj-proj : ∀ {P} {i} {x : ⟦ ζ₁ ⟧ᴵ P i} {y} → Iproj y ≡ just x → Iinj x ≡ y

{- instances of _I≼_ used for automated injections -}
module _ where

  open _I≼_

  instance I≼-refl  : ∀ {ℓ I J} {ζ : ISignature ℓ I J} → ζ I≼ ζ
  Iinj  I≼-refl = id
  Iproj I≼-refl = just
  Iproj-inj I≼-refl      = refl
  Iinj-proj I≼-refl refl = refl

  instance I≼-left  : ∀ {ℓ I J} {ζ₁ ζ₂ : ISignature ℓ I J} → ζ₁ I≼ (ζ₁ :++: ζ₂)
  Iinj I≼-left (s , as)       = inj₁ s , as
  Iproj I≼-left (inj₁ s , as) = just (s , as)
  Iproj I≼-left (inj₂ s , as) = nothing
  Iproj-inj I≼-left                       = refl
  Iinj-proj I≼-left {y = inj₁ _ , _} refl = refl

  instance I≼-right : ∀ {ℓ I J} {ζ ζ₁ ζ₂ : ISignature ℓ I J} → ⦃ ζ I≼ ζ₂ ⦄ → ζ I≼ (ζ₁ :++: ζ₂)
  Iinj (I≼-right ⦃ sub ⦄) x with Iinj sub x
  ... | s , as = inj₂ s , as
  Iproj (I≼-right ⦃ sub ⦄) (inj₁ s , as) = nothing
  Iproj (I≼-right ⦃ sub ⦄) (inj₂ s , as) = Iproj sub (s , as)
  Iproj-inj (I≼-right ⦃ sub ⦄) = Iproj-inj sub
  Iinj-proj (I≼-right ⦃ sub ⦄) {x = x} {inj₂ s , as} px with Iinj-proj sub {x = x} {s , as} px
  ... | refl = refl
