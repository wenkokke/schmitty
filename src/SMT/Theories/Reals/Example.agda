{-# OPTIONS --allow-exec #-}

module SMT.Theories.Reals.Example where

open import Data.Integer using (+_)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Text.Parser.String
open import SMT.Theories.Reals as Reals


module Z3 where

  open import SMT.Backend.Z3 Reals.reflectable

  script₁ : Script [] (REAL ∷ REAL ∷ []) (MODEL (REAL ∷ REAL ∷ []) ∷ [])
  script₁ = declare-const "x" REAL
         ∷ declare-const "y" REAL
         ∷ assert (app₂ eq (# 0) (app₂ div (# 1) (lit (nat 2))))
         ∷ assert (app₂ gt (# 0) (lit (nat 1)))
         ∷ assert (app₂ gt (# 1) (lit (nat 1)))
         ∷ get-model
         ∷ []

  _ : z3 script₁ ≡ ((sat , 1.5 ∷ 3.0 ∷ []) ∷ [])
  _ = refl



module CVC4 where

  open import SMT.Backend.CVC4 Reals.reflectable

  script₁ : Script [] (REAL ∷ REAL ∷ []) (MODEL (REAL ∷ REAL ∷ []) ∷ [])
  script₁ = declare-const "x" REAL
         ∷ declare-const "y" REAL
         ∷ assert (app₂ eq (# 0) (app₂ div (# 1) (lit (nat 2))))
         ∷ assert (app₂ gt (# 0) (lit (nat 1)))
         ∷ assert (app₂ gt (# 1) (lit (nat 1)))
         ∷ get-model
         ∷ []

  _ : cvc4 script₁ ≡ ((sat , 2.0 ∷ 4.0 ∷ []) ∷ [])
  _ = refl
