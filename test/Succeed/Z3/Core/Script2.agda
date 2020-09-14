{-# OPTIONS --allow-exec #-}

module Succeed.Z3.Core.Script2 where

open import Data.List using (List; _∷_; [])
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theories.Core as Core
open import SMT.Backend.Z3 Core.coreReflectable

-- |Pierce's law.
script : Script [] [] (SAT ∷ [])
script = assert ( forAll BOOL
                $ forAll BOOL
                $ app₂ implies (app₂ implies (app₂ implies (# 1) (# 0)) (# 1)) (# 1)
                )
       ∷ check-sat
       ∷ []

_ : z3 script ≡ sat ∷ []
_ = refl
