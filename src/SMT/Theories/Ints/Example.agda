{-# OPTIONS --allow-exec #-}

module SMT.Theories.Ints.Example where

open import Data.Environment using (Env; _∷_; [])
open import Data.Fin using (Fin; suc; zero)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; _∷_; [])
open import Data.Product as Prod using (∃-syntax; _×_; _,_)
open import Data.Unit
open import Reflection.External
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Text.Parser.String
open import SMT.Theories.Ints as Ints
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

test₁ : z3 script₁ ≡ unsat ∷ []
test₁ = refl

script₂ : Script [] (INT ∷ INT ∷ []) (MODEL (INT ∷ INT ∷ []) ∷ [])
script₂ = declare-const INT
        ∷ declare-const INT
        ∷ assert (app₂ eq x y)
        ∷ get-model
        ∷ []
        where
          x = var (suc zero , refl)
          y = var (    zero , refl)

vp₂ : ∀[ Parser (∃[ σ ] ((INT ∷ INT ∷ []) ∋ σ)) ]
vp₂ = varParser script₂

_ : vp₂ parses "x0"
_ = ! INT , suc zero , refl

_ : vp₂ parses "x1"
_ = ! INT , zero , refl

_ : vp₂ rejects "x2"
_ = _
