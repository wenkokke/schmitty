{-# OPTIONS --safe --without-K #-}

module Schmitty.Theory.Core where

open import Level using (Level)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Function using (const)
open import Relation.Unary using (IUniversal)
open import Schmitty.Composable
open import Schmitty.Theory.Sort

private
  variable
    σ : SortSignature

data CoreSortShape : Set where
  BOOL : CoreSortShape

CoreSortΣ : SortSignature
CoreSortΣ = const CoreSortShape ▹ λ where
  BOOL → []

interpCoreSort : Algebra CoreSortΣ (const Set₁)
⟦ interpCoreSort ⟧α (BOOL , []) = Set

bool : ⦃ CoreSortΣ ≼ σ ⦄ → Sort σ
bool = inject (BOOL , [])

data CoreExprShape ⦃ _ : CoreSortΣ ≼ σ ⦄ : Sort σ → Set₁ where
  true  : CoreExprShape bool
  false : CoreExprShape bool
  not   : CoreExprShape bool
  =>    : CoreExprShape bool
  and   : CoreExprShape bool
  or    : CoreExprShape bool
  xor   : CoreExprShape bool
  ite   : (t : Sort σ) → CoreExprShape t

CoreExprΣ : ⦃ CoreSortΣ ≼ σ ⦄ → Signature (Level.suc Level.zero) (μ σ) (μ σ)
CoreExprΣ = ?

-- interpCoreExpr : Algebra CoreExpr
