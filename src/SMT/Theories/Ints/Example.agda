{-# OPTIONS --allow-exec #-}

module SMT.Theories.Ints.Example where

open import Data.Fin using (Fin; suc; zero)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _*_; _-_; _≤_)
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Product as Prod using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Text.Parser.String
open import SMT.Logics
open import SMT.Theories.Ints as Ints


module Z3 where

  open import SMT.Backend.Z3 Ints.reflectable

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
  script₁ = declare-const "x" INT
         ∷ declare-const "y" INT
         ∷ assert (app₂ eq
                  (app₂ sub (# 0) (# 1))
                  (app₂ add (app₂ add (# 0) (app₁ neg (# 1))) (lit (nat 1)))
                  )
         ∷ check-sat
         ∷ []

  _ : z3 script₁ ≡ unsat ∷ []
  _ = refl


  -- |Parser test.
  script₂ : Script [] (INT ∷ INT ∷ []) (MODEL (INT ∷ INT ∷ []) ∷ [])
  script₂ = declare-const "x" INT
         ∷ declare-const "y" INT
         ∷ assert (app₂ eq (# 0) (# 1))
         ∷ get-model
         ∷ []

  pVar : ∀[ Parser (Var (INT ∷ INT ∷ [])) ]
  pVar = getVarParser script₂

  _ : pVar parses "x0"
  _ = ! INT , suc zero , refl

  _ : pVar parses "x1"
  _ = ! INT , zero , refl

  _ : pVar rejects "x2"
  _ = _

  pDefn : ∀[ Parser (Defn (INT ∷ INT ∷ [])) ]
  pDefn = mkDefnParser pVar

  _ : pDefn parses "(define-fun x0 () Int 0)"
  _ = ! INT , (suc zero , refl) , + 0

  _ : pDefn parses "(define-fun x1 () Int (- 1))"
  _ = ! INT , (zero , refl) , -[1+ 0 ]

  pDefns : ∀[ Parser (List⁺ (Defn (INT ∷ INT ∷ [])))]
  pDefns = mkDefnsParser pVar

  _ : pDefns parses "(model (define-fun x1 () Int 0) (define-fun x0 () Int 0))"
  _ = ! ((INT , (zero , refl) , + 0) ∷ (INT , (suc zero , refl) , + 0) ∷ [])

  pModel : ∀[ Parser (QualifiedModel (INT ∷ INT ∷ [])) ]
  pModel = mkModelParser pVar

  _ : pModel parses "sat (model (define-fun x1 () Int 0) (define-fun x0 () Int 0))"
  _ = ! sat , + 0 ∷ + 0 ∷ []

  _ : pModel parses "unsat (error \"line 5 column 10: model is not available\")"
  _ = ! unsat , _

  _ : z3 script₂ ≡ ((sat , + 0 ∷ + 0 ∷ []) ∷ [])
  _ = refl

  _ : (x y : ℤ) → x + y ≡ y + x
  _ = solveZ3


module CVC4 where

  open import SMT.Backend.CVC4 Ints.reflectable

  script₁ : Script [] (INT ∷ INT ∷ []) (MODEL (INT ∷ INT ∷ []) ∷ [])
  script₁ = set-logic QF-LIA
         ∷ declare-const "x" INT
         ∷ declare-const "y" INT
         ∷ assert (app₂ lt (# 0) (app₂ add (# 1) (lit (nat 10))))
         ∷ get-model
         ∷ []

  _ : cvc4 script₁ ≡ ((sat , + 0 ∷ + 0 ∷ []) ∷ [])
  _ = refl

  _ : (x y : ℤ) → x + y ≡ y + x
  _ = solveCVC4
