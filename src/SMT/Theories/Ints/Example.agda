{-# OPTIONS --allow-exec #-}

module SMT.Theories.Ints.Example where

open import Data.Environment using (Env; _∷_; [])
open import Data.Fin using (Fin; suc; zero)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)
open import Reflection.External
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import SMT.Theories.Ints as Ints
open import SMT.Script.Base Ints.theory
open import SMT.Script Ints.printable Ints.parsable
open import SMT.Backend.Z3 Ints.printable Ints.parsable

-- |Taken from <http://smtlib.cs.uiowa.edu/examples.shtml>
--
-- @
--   ; Integer arithmetic
--   (set-logic QF_LIA)
--   (declare-const x Int)
--   (declare-const y Int)
--   (assert (= (- x y) (+ x (- y) 1)))
--   (check-sat)
--   ; unsat
--   (exit)
-- @
--
script₁ : Script [] (INT ∷ INT ∷ []) (SAT ∷ [])
script₁ = declare-const INT
        ∷ declare-const INT
        ∷ assert (app₂ eq
                 (app₂ sub x y)
                 (app₂ add (app₂ add x (app₁ neg y)) (lit (int 1)))
                 )
        ∷ check-sat
        ∷ []
        where
          x = var (suc zero , refl)
          y = var (    zero , refl)

test₁ : runZ3 script₁ ≡ unsat ∷ []
test₁ = refl


