{-# OPTIONS --allow-exec #-}

module SMT.Theories.Ints.Example where

open import Data.Fin using (Fin; suc; zero)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Product as Prod using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Text.Parser.String
open import SMT.Logics
open import SMT.Theories.Ints as Ints

module Example₁ where

  open import SMT.Backend.Z3 Ints.theory

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
  script : Script [] (INT ∷ INT ∷ []) (SAT ∷ [])
  script = declare-const INT
         ∷ declare-const INT
         ∷ assert (app₂ eq
                  (app₂ sub (# 0) (# 1))
                  (app₂ add (app₂ add (# 0) (app₁ neg (# 1))) (lit (int 1)))
                  )
         ∷ check-sat
         ∷ []

  _ : z3 script ≡ unsat ∷ []
  _ = refl


module Example₂ where

  open import SMT.Backend.Z3 Ints.theory

  Γ : Ctxt
  Γ = INT ∷ INT ∷ []

  script : Script [] Γ (MODEL Γ ∷ [])
  script = declare-const INT
         ∷ declare-const INT
         ∷ assert (app₂ eq (# 0) (# 1))
         ∷ get-model
         ∷ []

  pVar : ∀[ Parser (Var Γ) ]
  pVar = getVarParser script

  _ : pVar parses "x0"
  _ = ! INT , suc zero , refl

  _ : pVar parses "x1"
  _ = ! INT , zero , refl

  _ : pVar rejects "x2"
  _ = _

  pDefn : ∀[ Parser (Defn Γ) ]
  pDefn = mkDefnParser pVar

  _ : pDefn parses "(define-fun x0 () Int 0)"
  _ = ! INT , (suc zero , refl) , + 0

  _ : pDefn parses "(define-fun x1 () Int (- 1))"
  _ = ! INT , (zero , refl) , -[1+ 0 ]


  pDefns : ∀[ Parser (List⁺ (Defn Γ))]
  pDefns = mkDefnsParser pVar

  _ : pDefns parses "(model (define-fun x1 () Int 0) (define-fun x0 () Int 0))"
  _ = ! ((INT , (zero , refl) , + 0) ∷ (INT , (suc zero , refl) , + 0) ∷ [])

  pModel : ∀[ Parser (Model Γ) ]
  pModel = mkModelParser pVar

  _ : pModel parses "sat (model (define-fun x1 () Int 0) (define-fun x0 () Int 0))"
  _ = ! + 0 ∷ + 0 ∷ []

  _ : z3 script ≡ ((+ 0 ∷ + 0 ∷ []) ∷ [])
  _ = refl


module Example₃ where

  open import SMT.Backend.CVC4 Ints.theory

  script : Script [] (INT ∷ INT ∷ []) (MODEL (INT ∷ INT ∷ []) ∷ [])
  script = set-logic QF-LIA
         ∷ declare-const INT
         ∷ declare-const INT
         ∷ assert (app₂ lt (# 0) (app₂ add (# 1) (lit (int 10))))
         ∷ get-model
         ∷ []

  _ : cvc4 script ≡ ((+ 0 ∷ + 0 ∷ []) ∷ [])
  _ = refl
