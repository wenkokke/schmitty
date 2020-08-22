{-# OPTIONS --allow-exec #-}

module SMT.Theories.Ints.Example where

open import Data.Fin using (Fin; suc; zero)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Product as Prod using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Text.Parser.String
open import SMT.Theories.Ints as Ints
open import SMT.Backend.Z3 Ints.printable Ints.parsable

module Example₁ where

  Γ : Ctxt
  Γ = INT ∷ INT ∷ []

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
  script : Script [] Γ (SAT ∷ [])
  script = declare-const INT
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

  _ : z3 script ≡ unsat ∷ []
  _ = refl

module Example₂ where

  Γ : Ctxt
  Γ = INT ∷ INT ∷ []

  script : Script [] Γ (MODEL Γ ∷ [])
  script = declare-const INT
         ∷ declare-const INT
         ∷ assert (app₂ eq x y)
         ∷ get-model
         ∷ []
         where
           x = var (suc zero , refl)
           y = var (    zero , refl)

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

