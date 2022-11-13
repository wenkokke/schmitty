{-# OPTIONS --safe --without-K #-}

module Schmitty.Theory.Bool where

open import Level using (Level; Lift; lift)
open import Data.Product using (_×_; _,_)
open import Data.Bool as Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Schmitty.Composable

private
  variable
    ℓ : Level
    σ : Signature ℓ

module BoolCanon where

  data TBoolShape : Set where
    BOOL : TBoolShape

  TBoolΣ : Signature Level.zero
  TBoolΣ = TBoolShape ▹ λ where BOOL → 0

  bool : ⦃ TBoolΣ ≼ σ ⦄ → μ σ
  bool = inject (BOOL , lift [])

  BoolVal : Algebra TBoolΣ Set Set
  alg BoolVal (BOOL , lift []) = Bool

  boolCanon : Canon
  Canon.ty  boolCanon = TBoolΣ
  Canon.val boolCanon = BoolVal

module BoolFragment where

  -- Fragment for the core theory of SMTLIB
  --
  -- See: http://smtlib.cs.uiowa.edu/theories-Core.shtml
  module _ {Ix : Set → Set} ⦃ ix-rel : ∀ {X} → Rel₂ Level.zero (Ix X) ⦄ where

    open BoolCanon using (TBoolΣ; bool; BoolVal; boolCanon)

    data BoolExprShape ⦃ _ : TBoolΣ ≼ σ ⦄ : μ σ → Set where
      true     : BoolExprShape bool
      false    : BoolExprShape bool
      not      : BoolExprShape bool
      =>       : BoolExprShape bool
      and      : BoolExprShape bool
      or       : BoolExprShape bool
      xor      : BoolExprShape bool
      -- ==       : (t : μ σ) → BoolExprShape bool
      -- distinct : (t : μ σ) → BoolExprShape bool
      ite      : (t : μ σ) → BoolExprShape t

    BoolExprΣ : ⦃ TBoolΣ ≼ σ ⦄ → ISignature _ (μ σ) (μ σ)
    BoolExprΣ = BoolExprShape ▸ (λ where
      true         → []
      false        → []
      not          → bool ∷ []
      =>           → bool ∷ bool ∷ []
      and          → bool ∷ bool ∷ []
      or           → bool ∷ bool ∷ []
      xor          → bool ∷ bool ∷ []
      -- (== t)       → t ∷ t ∷ []
      -- (distinct t) → t ∷ t ∷ []
      (ite t)      → bool ∷ t ∷ t ∷ [])

    module _ {σ} {V : Values Ix σ} where

      -- TODO: How do we require that the composed type is decidable?
      -- TODO: Do we want to use *this* interpretation of booleans?
      --       Or do we want to interpret them in Set? Or Prop? Or Classical?
      interpBool : ∀ {Σ} → ⦃ _ : liftVal BoolVal ⊑ V ⦄ → IAlgebra BoolExprΣ λ t → (para (out V) t) Σ
      ialg interpBool (true       , lift [])               = ↑ true
      ialg interpBool (false      , lift [])               = ↑ false
      ialg interpBool (not        , lift (x ∷ []))         = ↑ (Bool.not (↓ x))
      ialg interpBool (=>         , lift (x ∷ y ∷ []))     = ↑ (Bool.not (↓ x) Bool.∨ ↓ y)
      ialg interpBool (and        , lift (x ∷ y ∷ []))     = ↑ (↓ x Bool.∧ ↓ y)
      ialg interpBool (or         , lift (x ∷ y ∷ []))     = ↑ (↓ x Bool.∨ ↓ y)
      ialg interpBool (xor        , lift (x ∷ y ∷ []))     = ↑ (↓ x Bool.xor ↓ y)
      -- ialg interpBool (== t       , lift (x ∷ y ∷ []))     = ↑ ?
      -- ialg interpBool (distinct t , lift (x ∷ y ∷ []))     = ↑ ?
      ialg interpBool (ite t      , lift (x ∷ y ∷ z ∷ [])) = Bool.if ↓ x then y else z

    open Necessary using (□)

    Boolean : □ (IFragment {Ix}) (liftCanon boolCanon)
    IFragment.iexpr   (□.future Boolean r) = BoolExprΣ
    IFragment.iinterp (□.future Boolean r) = interpBool ⦃ r ⦄
