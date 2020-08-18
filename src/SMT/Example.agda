{-# OPTIONS --allow-exec #-}

module SMT.Example where

open import Data.Empty using (⊥)
open import Data.Fin using (suc; zero)
open import Data.List using (List; _∷_; [])
open import Data.String using (String)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Reflection.External
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theory

Sort : Set
Sort = ⊤

pattern BOOL = tt

data Literal : Sort → Set where
  true  : Literal BOOL
  false : Literal BOOL

data Identifier : {σ : Sort} → Signature σ → Set where
  implies : Identifier ((BOOL ∷ BOOL ∷ []) ↦ BOOL)

theory : Theory _ _ _
Theory.Sort       theory = Sort
Theory.BOOL       theory = BOOL
Theory.Literal    theory = Literal
Theory.Identifier theory = Identifier

showSort : Sort → String
showSort BOOL = "Bool"

showLiteral : {σ : Sort} (l : Literal σ) → String
showLiteral true  = "true"
showLiteral false = "false"

showIdentifier : {σ : Sort} {Σ : Signature σ} (x : Identifier Σ) → String
showIdentifier implies = "=>"

showableTheory : ShowableTheory _ _ _
ShowableTheory.theory         showableTheory = theory
ShowableTheory.showSort       showableTheory = showSort
ShowableTheory.showLiteral    showableTheory = showLiteral
ShowableTheory.showIdentifier showableTheory = showIdentifier

open import SMT.Script theory
open import SMT.Script.Show showableTheory
open import SMT.Backend.Z3 showableTheory

=> : ∀ {Γ} → Term Γ BOOL → Term Γ BOOL → Term Γ BOOL
=> x y = app implies (x ∷ y ∷ [])

term₁ : Term [] BOOL
term₁ = (forAll (forAll ((=> (=> (=> P Q) P) P))))
  where
    P = var (suc zero , refl)
    Q = var (    zero , refl)

_ : showTerm x′es term₁
  ≡ "(forall ((x0 Bool)) (forall ((x1 Bool)) (=> (=> (=> x0 x1) x0) x0)))"
_ = refl

script₁ : Script [] [] (SAT ∷ [])
script₁ = assert term₁ ∷ check-sat ∷ []

_ : showScript x′es script₁
  ≡ "(assert (forall ((x0 Bool)) (forall ((x1 Bool)) (=> (=> (=> x0 x1) x0) x0))))
\   \(check-sat)"
_ = refl

_ : runCmd (z3Cmd script₁)
  ≡ "sat\n"
_ = refl
