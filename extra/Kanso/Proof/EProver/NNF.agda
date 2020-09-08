module Kanso.Proof.EProver.NNF where

open import Data.Bool as Bool using (Bool; true; false)
open import Data.Nat as Nat using (ℕ)
open import Data.Product as Prod using (_×_; proj₁; proj₂; _,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit as Unit using (⊤; tt)
open import Function using (id)

open import Kanso.PropIso
open import Kanso.Boolean.Formula

mutual
  mknnf : PL-Formula → PL-Formula
  mknnf ¥true     = ¥true
  mknnf ¥false    = ¥false
  mknnf (y || y') = mknnf y || mknnf y'
  mknnf (y && y') = mknnf y && mknnf y'
  mknnf (y => y') = ¬mknnf y || mknnf y'
  mknnf (¥ y)     = ¥ y

  ¬mknnf : PL-Formula → PL-Formula
  ¬mknnf ¥true     = ¥false
  ¬mknnf ¥false    = ¥true
  ¬mknnf (y || y') = ¬mknnf y && ¬mknnf y'
  ¬mknnf (y && y') = ¬mknnf y || ¬mknnf y'
  ¬mknnf (y => y') = mknnf y && ¬mknnf y'
  ¬mknnf (¥ y)     = ~ (¥ y)

mutual
  lem-nnf→ : (φ : PL-Formula) → (ξ : ℕ → Bool) → ⟦ ξ ⊧ mknnf φ ⟧pl → ⟦ ξ ⊧ φ ⟧pl
  lem-nnf→ ¥true    ξ p = tt
  lem-nnf→ ¥false   ξ p = p
  lem-nnf→ (φ || ψ) ξ p = Sum.map (lem-nnf→ φ ξ) (lem-nnf→ ψ ξ) p
  lem-nnf→ (φ && ψ) ξ p = Prod.map (lem-nnf→ φ ξ) (lem-nnf→ ψ ξ) p
  lem-nnf→ (φ => ψ) ξ p = λ x → lem-nnf→ ψ ξ (lem-→ (Sum.map (lem-nnf'→ φ ξ) id p) x)
  lem-nnf→ (¥ v)    ξ p = p

  lem-nnf← : (φ : PL-Formula) → (ξ : ℕ → Bool) → ⟦ ξ ⊧ φ ⟧pl → ⟦ ξ ⊧ mknnf φ ⟧pl
  lem-nnf← ¥true    ξ p = p
  lem-nnf← ¥false   ξ p = p
  lem-nnf← (φ || ψ) ξ p = Sum.map (lem-nnf← φ ξ) (lem-nnf← ψ ξ) p
  lem-nnf← (φ && ψ) ξ p = Prod.map (lem-nnf← φ ξ) (lem-nnf← ψ ξ) p
  lem-nnf← (φ => ψ) ξ p = Sum.map (lem-nnf'← φ ξ) (lem-nnf← ψ ξ) (material-pl ξ φ ψ p)
  lem-nnf← (¥ v)    ξ p = p

  lem-nnf'→ : (φ : PL-Formula) → (ξ : ℕ → Bool) → ⟦ ξ ⊧ ¬mknnf φ ⟧pl → ⟦ ξ ⊧ ~ φ ⟧pl
  lem-nnf'→ ¥true    ξ p q = p
  lem-nnf'→ ¥false   ξ p q = q
  lem-nnf'→ (φ || ψ) ξ p q = [ lem-nnf'→ φ ξ (proj₁ p) , lem-nnf'→ ψ ξ (proj₂ p) ]′ q
  lem-nnf'→ (φ && ψ) ξ p q
    = [ (λ x → lem-nnf'→ φ ξ x (proj₁ q)) , (λ x → lem-nnf'→ ψ ξ x (proj₂ q)) ]′ p
  lem-nnf'→ (φ => ψ) ξ p q = lem-nnf'→ ψ ξ (proj₂ p) (q (lem-nnf→ φ ξ (proj₁ p)))
  lem-nnf'→ (¥ v)    ξ p q = p q

  lem-nnf'← : (φ : PL-Formula) → (ξ : ℕ → Bool) → ⟦ ξ ⊧ ~ φ ⟧pl → ⟦ ξ ⊧ ¬mknnf φ ⟧pl
  lem-nnf'← ¥true    ξ p = p tt
  lem-nnf'← ¥false   ξ p = tt
  lem-nnf'← (φ || ψ) ξ p = (lem-nnf'← φ ξ (λ x → p (inj₁ x))) , lem-nnf'← ψ ξ (λ x → p (inj₂ x))
  lem-nnf'← (φ && ψ) ξ p = Sum.map (lem-nnf'← φ ξ) (lem-nnf'← ψ ξ) (demorg ξ φ ψ p)
  lem-nnf'← (φ => ψ) ξ p = Prod.map (lem-nnf← φ ξ) (lem-nnf'← ψ ξ) (material-¬pl ξ φ ψ p)
  lem-nnf'← (¥ v)    ξ p = p
