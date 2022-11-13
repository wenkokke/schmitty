{-# OPTIONS --without-K --safe #-}

module Schmitty.Composable.Fragment where

open import Level using (Level)
open import Relation.Unary using (IUniversal; _⇒_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_$_; _∘_)
open import Schmitty.Composable.Box using (module Necessary)
open import Schmitty.Composable.Signature
     using (ISignature; IAlgebra; cata; para; μ; μᴵ; foldᴵ; _:++:_; _:⊕:_)
open import Schmitty.Composable.Canon
     using (Canon; module Canon; ICanon; module ICanon; Values; module Values;
            _∙_≣_; _∙_≣ᵖ_; ∙-⊑ᵖ₁; ∙-⊑ᵖ₂; ∙-⊑₁; ∙-⊑₂; out)

{- Pure Language fragments -}
module _ where

  open Canon

  -- A language fragment with canonical forms `c` consists of:
  --
  -- 1) A set of object language expressions, `expr`, indexed by the type functor
  --    as given by `c`. We collapse `ty c : Set → Set` into a value in `Set` using
  --    `μ`.
  -- 2) An interpretation function (denotational semantics), `interp`, producing
  --    values as given by the value algebra in `c`, which we collapse into a
  --    concrete value type by using `cata`
  record Fragment (c : Canon) : Set₁ where
    field expr   : ISignature _ (μ (ty c)) (μ (ty c))
          interp : IAlgebra expr (cata (val c))

module _ where

  open ICanon
  open Values

  -- A notion of fragments, generalized to indexed values
  --
  record IFragment {Ix} (c : ICanon Ix) : Set₁ where
    field iexpr   : ISignature _ (μ (ity c)) (μ (ity c))
          iinterp : ∀ {i} → IAlgebra iexpr λ t → para (out (ival c)) t i

module _ where

  open Fragment

  -- Homogeneous fragment composition (i.e., composition of fragments with the
  -- same notions of types and values).
  -- This operation is straightforwardly implemented in terms of the sum
  -- operations for `ISignatures` and `IAlgebra`
  fcompose-homᵖ : ∀[ Fragment ⇒ Fragment ⇒ Fragment ]
  expr   (fcompose-homᵖ φ₁ φ₂) = expr   φ₁ :++: expr   φ₂
  interp (fcompose-homᵖ φ₁ φ₂) = interp φ₁ :⊕:  interp φ₂


module _ where

  open IFragment

  -- Homogenous composition for fragments with a notion of
  -- indexed values
  fcompose-hom : ∀ {Ix} → ∀[ IFragment {Ix} ⇒ IFragment ⇒ IFragment ]
  iexpr   (fcompose-hom φ₁ φ₂) = iexpr   φ₁ :++: iexpr   φ₂
  iinterp (fcompose-hom φ₁ φ₂) = iinterp φ₁ :⊕:  iinterp φ₂

{-
  A formulation of fragment composition directly using `Union`
  !! This is the version presented in the paper !!
-}
module _ where

  open Necessary
  open □
  open Fragment
  open Canon

  -- We can readily lift fcompose to operate on open fragments
  □-fcompose-homᵖ : ∀[ □ Fragment ⇒ □ Fragment ⇒ □ Fragment ]
  □-fcompose-homᵖ φ₁ φ₂ = □-distr-⇒ (□-lift fcompose-homᵖ φ₁) φ₂

  fcomposeᵖ : ∀ {c₁ c₂ c} → □ Fragment c₁ → □ Fragment c₂ → c₁ ∙ c₂ ≣ᵖ c → □ Fragment c
  fcomposeᵖ φ₁ φ₂ u =
    □-fcompose-homᵖ (future (duplicate φ₁) (∙-⊑ᵖ₁ u))
                    (future (duplicate φ₂) (∙-⊑ᵖ₂ u))

module _ where

  open Necessary
  open □

  -- The same is true for fragments with indexed values. The implementation of heterogeneous composition
  -- is identical, but has a slightly different type
  □-fcompose-hom : ∀ {Ix} → ∀[ □ (IFragment {Ix}) ⇒ □ IFragment ⇒ □ IFragment ]
  □-fcompose-hom φ₁ φ₂ = □-distr-⇒ (□-lift fcompose-hom φ₁) φ₂

  fcompose : ∀ {Ix c₁ c₂ c} → □ (IFragment {Ix}) c₁ → □ IFragment c₂ → c₁ ∙ c₂ ≣ c → □ IFragment c
  fcompose φ₁ φ₂ u =
    □-fcompose-hom (future (duplicate φ₁) (∙-⊑₁ u))
                   (future (duplicate φ₂) (∙-⊑₂ u))

  infixr 6 fcompose
  syntax fcompose φ₁ φ₂ sep = φ₁ ⊙⟨ sep ⟩ φ₂

{-
  A formulation of fragment composition in terms of separating conjunction
  (This version is *not* presented in the paper)
-}
module _ where

  -- non-dependent separating conjunction
  record _✴_ (P Q : Canon → Set₁) (c : Canon) : Set₁ where
    constructor _∙⟨_⟩_
    field {ca₁ ca₂} : Canon
          px        : P ca₁
          sep       : ca₁ ∙ ca₂ ≣ᵖ c
          qx        : Q ca₂

  open Necessary
  open □

  fcompose✴ : ∀[ (□ Fragment ✴ □ Fragment) ⇒ □ Fragment ]
  fcompose✴ (φ₁ ∙⟨ sep ⟩ φ₂) =
    □-distr-⇒ ((□-lift fcompose-homᵖ) ( weaken φ₁ (∙-⊑ᵖ₁ sep)))
                                      $ weaken φ₂ (∙-⊑ᵖ₂ sep)

{- Fragment closure -}
module _ where

  open Necessary
  open Fragment
  open IFragment
  open □
  open Canon
  open ICanon

  closeᵖ : ∀ {c} → (φ : □ Fragment c) → ∀[ μᴵ (expr (extract φ)) ⇒ cata (val c) ]
  closeᵖ = foldᴵ ∘ interp ∘ extract

  close : ∀ {Ix c} → (φ : □ (IFragment {Ix}) c) → ∀ {t} → μᴵ (iexpr (extract φ)) t → ∀[ para (out (ival c)) t ]
  close φ x = foldᴵ (iinterp (extract φ)) x
