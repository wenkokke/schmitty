--------------------------------------------
-- Test generated output parsers for Ints --
--------------------------------------------

{-# OPTIONS --allow-exec #-}

module Test_OutputParser_Ints where

open import Data.Fin using (Fin; suc; zero)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Product as Prod using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Text.Parser.String
open import SMT.Theories.Ints as Ints
open import SMT.Script Ints.reflectable

-- |Parser test.
script : Script [] (INT ∷ INT ∷ []) (MODEL (INT ∷ INT ∷ []) ∷ [])
script = declare-const "x" INT
       ∷ declare-const "y" INT
       ∷ assert (app₂ eq (# 0) (# 1))
       ∷ get-model
       ∷ []


pVar : ∀[ Parser (Var (INT ∷ INT ∷ [])) ]
pVar = getVarParser script

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

_ : pDefns parses
    "(model (define-fun x1 () Int 0) (define-fun x0 () Int 0))"
_ = ! ((INT , (zero , refl) , + 0) ∷ (INT , (suc zero , refl) , + 0) ∷ [])


pModel : ∀[ Parser (QualifiedModel (INT ∷ INT ∷ [])) ]
pModel = mkModelParser pVar

_ : pModel parses
    "sat (model (define-fun x1 () Int 0) (define-fun x0 () Int 0))"
_ = ! sat , + 0 ∷ + 0 ∷ []

_ : pModel parses
    "unsat (error \"line 5 column 10: model is not available\")"
_ = ! unsat , _

-- Z3 error message:
_ : pModelError accepts
    "(error \"line 5 column 10: model is not available\")"
_ = _

-- CVC4 error message:
_ : pModelError accepts
    "(error \"Cannot get the current model unless immediately preceded by SAT/INVALID or UNKNOWN response.\")"
_ = _
