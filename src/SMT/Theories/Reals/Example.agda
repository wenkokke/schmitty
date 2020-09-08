{-# OPTIONS --allow-exec #-}

module SMT.Theories.Reals.Example where

open import Data.Integer using (+_)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Text.Parser.String
open import SMT.Theories.Reals as Reals
open import SMT.Script Reals.theory Reals.reflectable


module Example₁ where

  open import SMT.Backend.Z3 Reals.theory Reals.reflectable

  Γ : Ctxt
  Γ = REAL ∷ REAL ∷ []

  script : Script [] Γ (MODEL Γ ∷ [])
  script = declare-const "x" REAL
         ∷ declare-const "y" REAL
         ∷ assert (app₂ eq (# 0) (app₂ div (# 1) (lit (nat 2))))
         ∷ assert (app₂ gt (# 0) (lit (nat 1)))
         ∷ assert (app₂ gt (# 1) (lit (nat 1)))
         ∷ get-model
         ∷ []

  _ : z3 script ≡ ((sat , 1.5 ∷ 3.0 ∷ []) ∷ [])
  _ = refl



module Example₂ where

  open import SMT.Backend.CVC4 Reals.theory Reals.reflectable

  Γ : Ctxt
  Γ = REAL ∷ REAL ∷ []

  script : Script [] Γ (MODEL Γ ∷ [])
  script = declare-const "x" REAL
         ∷ declare-const "y" REAL
         ∷ assert (app₂ eq (# 0) (app₂ div (# 1) (lit (nat 2))))
         ∷ assert (app₂ gt (# 0) (lit (nat 1)))
         ∷ assert (app₂ gt (# 1) (lit (nat 1)))
         ∷ get-model
         ∷ []

  _ : cvc4 script ≡ ((sat , 2.0 ∷ 4.0 ∷ []) ∷ [])
  _ = refl
