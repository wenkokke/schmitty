{-# OPTIONS --allow-exec #-}

module Succeed.Z3.Core.Script3 where

open import Data.List using (List; _∷_; [])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theories.Core as Core
open import SMT.Backend.Z3 Core.coreReflectable

-- |Parsing models.
script : Script [] (BOOL ∷ []) (MODEL (BOOL ∷ []) ∷ [])
script = declare-const "b" BOOL
       ∷ assert (# 0)
       ∷ get-model
       ∷ []

_ : z3 script ≡ (sat , UNIT ∷ []) ∷ []
_ = refl
