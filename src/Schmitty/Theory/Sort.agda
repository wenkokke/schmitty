{-# OPTIONS --safe --without-K #-}

module Schmitty.Theory.Sort where

open import Level using (Level)
open import Schmitty.Composable using (Signature; μ)

record ★ : Set where
  constructor ☆

SortSignature : Set₁
SortSignature = Signature Level.zero ★ ★

Sort : SortSignature → Set
Sort σ = μ σ ☆
