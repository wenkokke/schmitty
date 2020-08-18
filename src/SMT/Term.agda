open import Data.List using (List)

module SMT.Term
  {s i l}
  (Sort : Set s)
  (Bool : Sort)
  (Literal : Sort → Set l)
  (Identifier : List Sort → Sort → Set i)
  where

open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.List as List using (_∷_; []; _++_)
open import Data.Product using (∃-syntax; _,_)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    σ : Sort

Ctxt : Set s
Ctxt = List Sort

private
  variable
    Γ Δ Σ : Ctxt

_∋_ : (Γ : Ctxt) (σ : Sort) → Set s
Γ ∋ σ = ∃[ i ] (List.lookup Γ i ≡ σ)

-- |Type of SMT-LIB compatible terms.
--
--  NOTE: match expressions are omitted, since we have no plans at the moment
--        to support datatype sorts.
mutual
  data Term (Γ : Ctxt) : (σ : Sort) → Set (Level.suc (s ⊔ i ⊔ l)) where
    var    : ∀ {σ} (x : Γ ∋ σ) → Term Γ σ
    lit    : ∀ {σ} (l : Literal σ) → Term Γ σ
    app    : ∀ {σ} {Σ : List Sort} (x : Identifier Σ σ) (xs : Args Γ Σ) → Term Γ σ
    forAll : ∀ {σ} (x : Term (σ ∷ Γ) Bool) → Term Γ Bool
    exists : ∀ {σ} (x : Term (σ ∷ Γ) Bool) → Term Γ Bool

  data Args (Γ : Ctxt) : (Σ : Ctxt) → Set (Level.suc (s ⊔ i ⊔ l)) where
    []  : Args Γ []
    _∷_ : Term Γ σ → Args Γ Σ → Args Γ (σ ∷ Σ)
