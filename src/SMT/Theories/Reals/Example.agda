{-# OPTIONS --allow-exec #-}

module SMT.Theories.Reals.Example where

open import Data.Integer using (+_)
open import Data.Rational.Unnormalised using (_/_)
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Text.Parser.String
open import SMT.Theories.Reals as Reals
open import SMT.Script Reals.theory


module Example₁ where

  open import SMT.Backend.Z3 Reals.theory

  Γ : Ctxt
  Γ = REAL ∷ REAL ∷ []

  script : Script [] Γ (MODEL Γ ∷ [])
  script = declare-const REAL
         ∷ declare-const REAL
         ∷ assert (app₂ eq (# 0) (app₂ div (# 1) (lit (nat 2))))
         ∷ assert (app₂ gt (# 0) (lit (nat 1)))
         ∷ assert (app₂ gt (# 1) (lit (nat 1)))
         ∷ get-model
         ∷ []

  _ : z3 script ≡ ((+ 3 / 2 ∷ + 3 / 1 ∷ []) ∷ [])
  _ = refl



module Example₂ where

  open import SMT.Backend.CVC4 Reals.theory

  Γ : Ctxt
  Γ = REAL ∷ REAL ∷ []

  script : Script [] Γ (MODEL Γ ∷ [])
  script = declare-const REAL
         ∷ declare-const REAL
         ∷ assert (app₂ eq (# 0) (app₂ div (# 1) (lit (nat 2))))
         ∷ assert (app₂ gt (# 0) (lit (nat 1)))
         ∷ assert (app₂ gt (# 1) (lit (nat 1)))
         ∷ get-model
         ∷ []

  _ : cvc4 script ≡ ((+ 2 / 1 ∷ + 4 / 1 ∷ []) ∷ [])
  _ = refl
