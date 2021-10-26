{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}

--------------------------------------------
-- Test generated output parsers for Ints --
--------------------------------------------

module Test_OutputParser_Ints where

open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product as Prod using (_,_)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Text.Parser.String
open import SMT.Theories.Ints as Ints
open import SMT.Script Ints.theory

-- |Parser test.
script : Script [] (INT ∷ INT ∷ []) (MODEL (INT ∷ INT ∷ []) ∷ [])
script = `declare-const "x" INT
       $ `declare-const "y" INT
       $ `assert (`app₂ eq (# 0) (# 1))
       $ `get-model
       $ []


pVar : ∀[ Parser (Var (INT ∷ INT ∷ [])) ]
pVar = getVarParser script

_ : pVar parses "x_0"
_ = ! INT , there (here refl)

_ : pVar parses "y_1"
_ = ! INT , here refl

_ : pVar rejects "x_2"
_ = _


pDefn : ∀[ Parser (Defn (INT ∷ INT ∷ [])) ]
pDefn = mkDefnParser pVar

_ : pDefn parses "(define-fun x_0 () Int 0)"
_ = ! INT , there (here refl) , + 0

_ : pDefn parses "(define-fun y_1 () Int (- 1))"
_ = ! INT , here refl , -[1+ 0 ]


pDefns : ∀[ Parser (List⁺ (Defn (INT ∷ INT ∷ [])))]
pDefns = mkDefnsParser pVar

_ : pDefns parses
    "(model (define-fun y_1 () Int 0) (define-fun x_0 () Int 0))"
_ = ! ((INT , here refl , + 0) ∷ (INT , there (here refl) , + 0) ∷ [])

_ : pDefns parses
    "((define-fun y_1 () Int 0) (define-fun x_0 () Int 0))"
_ = ! ((INT , here refl , + 0) ∷ (INT , there (here refl) , + 0) ∷ [])


pModel : ∀[ Parser (QualifiedModel (INT ∷ INT ∷ [])) ]
pModel = mkModelParser pVar

_ : pModel parses
    "sat (model (define-fun y_1 () Int 0) (define-fun x_0 () Int 0))"
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
