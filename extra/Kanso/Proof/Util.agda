module Kanso.Proof.Util where

open import Data.Bool as Bool using (Bool; true; false; T; _∧_; _∨_)
open import Data.List as List using (List; _∷_; [])
open import Data.Product as Prod using (_×_; proj₁; proj₂; _,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit as Unit using (⊤; tt)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

open import Kanso.PropIso
open import Kanso.Boolean.Formula

_∈_ : PL-Formula → List PL-Formula → Bool
φ ∈ [] = false
φ ∈ (ψ ∷ Γ) = φ ≡pl ψ ∨ φ ∈ Γ

_∪_ : List PL-Formula → List PL-Formula → List PL-Formula
_∪_ = List._++_

_⊆_  : List PL-Formula → List PL-Formula → Bool
[] ⊆ Γ' = true
(γ ∷ Γ) ⊆ Γ' = γ ∈ Γ' ∧ Γ ⊆ Γ'

_∣_ : List PL-Formula → PL-Formula → List PL-Formula
[] ∣ _ = []
(φ ∷ φs) ∣ ψ with φ ≡pl ψ
...| true  = φs ∣ ψ
...| false = φ ∷ (φs ∣ ψ)

_⊇≈_ : List PL-Formula → List PL-Formula → Set
Γ₁ ⊇≈ Γ₂ = ∀ γ → T (γ ∈ Γ₂) → T (γ ∈ Γ₁)

lift-⊆ : ∀ Γ₁ Γ₂ → T (Γ₁ ⊆ Γ₂) → (Γ₂ ⊇≈ Γ₁)
lift-⊆ [] Γ₂ p        = λ _ ()
lift-⊆ (γ₁ ∷ Γ₁) Γ₂ p = λ γ → ∨-elim (λ γ=γ₁ → PropEq.subst (λ x → T (x ∈ Γ₂))
                                                     (PropEq.sym (lift-≡pl γ γ₁ γ=γ₁)) (∧-eliml p))
                                     (lift-⊆ Γ₁ Γ₂ (∧-elimr (γ₁ ∈ Γ₂) p) γ)

lem-seq-restrict-foldr : ∀ ξ Γ φ → ⟦ ξ ⊧ andpl Γ ⟧pl → ⟦ ξ ⊧ andpl (Γ ∣ φ) ⟧pl
lem-seq-restrict-foldr ξ []      φ p = tt
lem-seq-restrict-foldr ξ (γ ∷ Γ) φ p with γ ≡pl φ
...| true = lem-seq-restrict-foldr ξ Γ φ (proj₂ p)
...| false = Prod.map id (lem-seq-restrict-foldr ξ Γ φ) p

lem-seq-restrict-foldr' : ∀ ξ Γ φ → ⟦ ξ ⊧ φ ⟧pl → ⟦ ξ ⊧ andpl (Γ ∣ φ) ⟧pl → ⟦ ξ ⊧ andpl Γ ⟧pl
lem-seq-restrict-foldr' ξ []      φ p q = tt
lem-seq-restrict-foldr' ξ (γ ∷ Γ) φ p q with ex-mid (γ ≡pl φ)
...| inj₁ x rewrite Tb x = PropEq.subst (⟦_⊧_⟧pl ξ) (PropEq.sym (lift-≡pl γ φ x)) p
                                               , (lem-seq-restrict-foldr' ξ Γ φ p q)
...| inj₂ x rewrite ¬Tb x = Prod.map id (lem-seq-restrict-foldr' ξ Γ φ p) q

lem-seq : ∀ Γ₁ Γ₂ φ → Γ₁ ⊇≈ (φ ∷ Γ₂) → Γ₁ ⊇≈ Γ₂
lem-seq Γ₁ Γ₂ φ f = λ γ x → f γ (∨-intror (γ ≡pl φ) (γ ∈ Γ₂) x)

lem-seq-atom : ∀ ξ Γ φ → ⟦ ξ ⊧ andpl Γ ⟧pl → T (φ ∈ Γ) → ⟦ ξ ⊧ φ ⟧pl
lem-seq-atom ξ [] φ conj   = λ ()
lem-seq-atom ξ (γ ∷ Γ) φ c = ∨-elim (λ φ=γ → PropEq.subst (⟦_⊧_⟧pl ξ) (PropEq.sym (lift-≡pl φ γ φ=γ)) (proj₁ c))
                                    (lem-seq-atom ξ Γ φ (proj₂ c))

lem-seq-subst-foldr : ∀ ξ Γ₁ Γ₂ → Γ₁ ⊇≈ Γ₂ → ⟦ ξ ⊧ andpl Γ₁ ⟧pl → ⟦ ξ ⊧ andpl Γ₂ ⟧pl
lem-seq-subst-foldr ξ Γ₁ [] y p        = tt
lem-seq-subst-foldr ξ Γ₁ (γ₂ ∷ Γ₂) y p = lem-seq-atom ξ Γ₁ γ₂ p
                                                      (y γ₂ (∨-introl (γ₂ ≡pl γ₂) _ (id-≡pl γ₂)))
                                          , lem-seq-subst-foldr ξ Γ₁ Γ₂ (lem-seq Γ₁ Γ₂ γ₂ y) p

seq-split : ∀ ξ Γ₁ Γ₂ → ⟦ ξ ⊧ andpl (Γ₁ List.++ Γ₂) ⟧pl → ⟦ ξ ⊧ andpl Γ₁ ⟧pl × ⟦ ξ ⊧ andpl Γ₂ ⟧pl
seq-split ξ []        Γ₂ p++ = tt , p++
seq-split ξ (γ₁ ∷ Γ₁) Γ₂ p++ = Prod.map (λ x → (proj₁ p++) , x) id (seq-split ξ Γ₁ Γ₂ (proj₂ p++))

record [_⇒_] (A B : Set) : Set where
  constructor _⇒_
  field πΓ : List A
        πφ : B

open [_⇒_] public

mkconj : PL-Formula → List PL-Formula → PL-Formula
mkconj γ []       = γ
mkconj γ (x ∷ xs) = γ && mkconj x xs

⟦_⊧_⟧⇒ : Env → [ PL-Formula ⇒ PL-Formula ] → Set
⟦ ξ ⊧ [] ⇒ φ ⟧⇒       = ⟦ ξ ⊧ φ ⟧pl
⟦ ξ ⊧ (x ∷ xs) ⇒ φ ⟧⇒ = ⟦ ξ ⊧ mkconj x xs ⟧pl → ⟦ ξ ⊧ φ ⟧pl
