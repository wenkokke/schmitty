{-# OPTIONS --safe --without-K --prop #-}

module Schmitty.Theory.Prop where

open import Level using (Level; Lift; lift)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Schmitty.Composable

private
  variable
    ℓ : Level
    σ : Signature ℓ

module PropCanon where

  data TPropShape : Set where
    PROP : TPropShape

  TPropΣ : Signature Level.zero
  TPropΣ = TPropShape ▹ λ where PROP → 0

  prop : ⦃ TPropΣ ≼ σ ⦄ → μ σ
  prop = inject (PROP , lift [])

{-
  PropVal : Algebra TPropΣ ? ?
  alg PropVal (PROP , lift []) = Prop

  propCanon : Canon
  Canon.ty  propCanon = TPropΣ
  Canon.val propCanon = PropVal

module PropFragment where

  -- Fragment for the core theory of SMTLIB
  --
  -- See: http://smtlib.cs.uiowa.edu/theories-Core.shtml
  module _ {Ix : Set → Set} ⦃ ix-rel : ∀ {X} → Rel₂ Level.zero (Ix X) ⦄ where

    open PropCanon using (TPropΣ; prop; PropVal; propCanon)

    data PropExprShape ⦃ _ : TPropΣ ≼ σ ⦄ : μ σ → Set where
      true     : PropExprShape prop
      false    : PropExprShape prop
      not      : PropExprShape prop
      =>       : PropExprShape prop
      and      : PropExprShape prop
      or       : PropExprShape prop
      xor      : PropExprShape prop
      ==       : (t : μ σ) → PropExprShape prop
      distinct : (t : μ σ) → PropExprShape prop
      ite      : (t : μ σ) → PropExprShape t

    PropExprΣ : ⦃ TPropΣ ≼ σ ⦄ → ISignature _ (μ σ) (μ σ)
    PropExprΣ = PropExprShape ▸ (λ where
      true         → []
      false        → []
      not          → prop ∷ []
      =>           → prop ∷ prop ∷ []
      and          → prop ∷ prop ∷ []
      or           → prop ∷ prop ∷ []
      xor          → prop ∷ prop ∷ []
      (== t)       → t ∷ t ∷ []
      (distinct t) → t ∷ t ∷ []
      (ite t)      → prop ∷ t ∷ t ∷ [])

    module _ {σ} {V : Values Ix σ} where

      -- TODO: How do we require that the composed type is decidable?
      -- TODO: Do we want to use *this* interpretation of propeans?
      --       Or do we want to interpret them in Set? Or Prop? Or Classical?
      interpProp : ∀ {Σ} → ⦃ _ : liftVal PropVal ⊑ V ⦄ → IAlgebra PropExprΣ λ t → (para (out V) t) Σ
      ialg interpProp (true       , lift [])               = ?
      ialg interpProp (false      , lift [])               = ?
      ialg interpProp (not        , lift (x ∷ []))         = ?
      ialg interpProp (=>         , lift (x ∷ y ∷ []))     = ?
      ialg interpProp (and        , lift (x ∷ y ∷ []))     = ?
      ialg interpProp (or         , lift (x ∷ y ∷ []))     = ?
      ialg interpProp (xor        , lift (x ∷ y ∷ []))     = ?
      ialg interpProp (== t       , lift (x ∷ y ∷ []))     = ?
      ialg interpProp (distinct t , lift (x ∷ y ∷ []))     = ?
      ialg interpProp (ite t      , lift (x ∷ y ∷ z ∷ [])) = ?

    open Necessary using (□)

    Propean : □ (IFragment {Ix}) (liftCanon propCanon)
    IFragment.iexpr   (□.future Propean r) = PropExprΣ
    IFragment.iinterp (□.future Propean r) = interpProp ⦃ r ⦄

-- -}
