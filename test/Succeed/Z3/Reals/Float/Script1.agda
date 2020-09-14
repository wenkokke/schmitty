{-# OPTIONS --allow-exec #-}

module Succeed.Z3.Reals.Float.Script1 where

open import Data.Integer using (+_)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Text.Parser.String
open import SMT.Theories.Reals as Reals
open import SMT.Backend.Z3 Reals.reflectable

script : Script [] (REAL ∷ REAL ∷ []) (MODEL (REAL ∷ REAL ∷ []) ∷ [])
script = declare-const "x" REAL
       ∷ declare-const "y" REAL
       ∷ assert (app₂ eq (# 0) (app₂ div (# 1) (lit (nat 2))))
       ∷ assert (app₂ gt (# 0) (lit (nat 1)))
       ∷ assert (app₂ gt (# 1) (lit (nat 1)))
       ∷ get-model
       ∷ []

_ : z3 script ≡ ((sat , 1.5 ∷ 3.0 ∷ []) ∷ [])
_ = refl
