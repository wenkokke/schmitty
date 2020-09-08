module Kanso.Boolean.Formula.DropEquivalence where

open import Data.Bool as Bool using (Bool; true; false; T; not; _∧_; _∨_)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Nat as Nat using (ℕ)
open import Data.Product as Prod using (_×_; proj₁; proj₂; _,_; Σ-syntax; curry)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit as Unit using (⊤; tt)
open import Function using (_∘_; id; _$_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

open import Kanso.Boolean.Formula
open import Kanso.Boolean.Formula.Equivalence
open import Kanso.PropIso

mutual
  lem-extend-env : ∀ ξ n φ b → T (not ((¥ n) isSubFormula φ))
                 → ⟦ ξ ⊧ φ ⟧pl → ⟦ envupdate ξ n b ⊧ φ ⟧pl
  lem-extend-env ξ n ¥true b n∉φ [φ] = [φ]
  lem-extend-env ξ n ¥false b n∉φ [φ] = [φ]
  lem-extend-env ξ n (y || y') b n∉φ [φ]
    = let π : T _ × T _
          π = lem-bool-∧-s (not (¥ n isSubFormula y)) _ (demorg1 (¥ n isSubFormula y) _ n∉φ)
      in Sum.map (lem-extend-env ξ n y b (proj₁ π)) (lem-extend-env ξ n y' b (proj₂ π)) [φ]
  lem-extend-env ξ n (y && y') b n∉φ [φ]
    = let π : T _ × T _
          π = lem-bool-∧-s (not (¥ n isSubFormula y)) _ (demorg1 (¥ n isSubFormula y) _ n∉φ)
      in Prod.map (lem-extend-env ξ n y b (proj₁ π)) (lem-extend-env ξ n y' b (proj₂ π)) [φ]
  lem-extend-env ξ n (y => y') b n∉φ [φ]
    = let π : T _ × T _
          π = lem-bool-∧-s (not (¥ n isSubFormula y)) _ (demorg1 (¥ n isSubFormula y) _ n∉φ)
      in lem-extend-env ξ n y' b (proj₂ π) ∘ [φ] ∘ lem-extend-env' ξ n y b (proj₁ π)
  lem-extend-env ξ n (¥ y) b n∉φ [φ] with n Nat.≡ᵇ y
  ...| true = ⊥-elim n∉φ
  ...| false = [φ]

  lem-extend-env' : ∀ ξ n φ b → T (not ((¥ n) isSubFormula φ))
                  → ⟦ envupdate ξ n b ⊧ φ ⟧pl → ⟦ ξ ⊧ φ ⟧pl
  lem-extend-env' ξ n ¥true b n∉φ [φ] = [φ]
  lem-extend-env' ξ n ¥false b n∉φ [φ] = [φ]
  lem-extend-env' ξ n (y || y') b n∉φ [φ]
    = let π : T _ × T _
          π = lem-bool-∧-s (not (¥ n isSubFormula y)) _ (demorg1 (¥ n isSubFormula y) _ n∉φ)
      in Sum.map (lem-extend-env' ξ n y b (proj₁ π)) (lem-extend-env' ξ n y' b (proj₂ π)) [φ]
  lem-extend-env' ξ n (y && y') b n∉φ [φ]
    = let π : T _ × T _
          π = lem-bool-∧-s (not (¥ n isSubFormula y)) _ (demorg1 (¥ n isSubFormula y) _ n∉φ)
      in Prod.map (lem-extend-env' ξ n y b (proj₁ π)) (lem-extend-env' ξ n y' b (proj₂ π)) [φ]
  lem-extend-env' ξ n (y => y') b n∉φ [φ]
    = let π : T _ × T _
          π = lem-bool-∧-s (not (¥ n isSubFormula y)) _ (demorg1 (¥ n isSubFormula y) _ n∉φ)
      in lem-extend-env' ξ n y' b (proj₂ π) ∘ [φ] ∘ lem-extend-env ξ n y b (proj₁ π)
  lem-extend-env' ξ n (¥ y) b n∉φ [φ] with n Nat.≡ᵇ y
  ...| true = ⊥-elim n∉φ
  ...| false = [φ]

private
  lem : ∀ n φ ψ
      → T (not ((¥ n) isSubFormula φ))
      → T (not ((¥ n) isSubFormula ψ))
      → Σ[ ξ ∈ Env ] ⟦ ξ ⊧ ψ ⟧pl
      → Σ[ ξ ∈ Env ] ⟦ ξ ⊧ ((¥ n) <ᵇ=> φ) && ψ ⟧pl
  lem n φ ψ n∉φ n∉ψ (ξ , [ψ]) = envupdate ξ n (eval-pl ξ φ)
                              , ((lem-extend-env ξ n φ (eval-pl ξ φ) n∉φ ∘ lem-eval' ξ φ ∘
                                     PropEq.subst T (lem-envupdate ξ n (eval-pl ξ φ)))
                                , PropEq.subst T (PropEq.sym (lem-envupdate ξ n (eval-pl ξ φ))) ∘ lem-eval ξ φ ∘
                                     lem-extend-env' ξ n φ (eval-pl ξ φ) n∉φ)
                              , lem-extend-env ξ n ψ (eval-pl ξ φ) n∉ψ [ψ]

  lem' : ∀ n φ ψ
       → T (not ((¥ n) isSubFormula φ))
       → T (not ((¥ n) isSubFormula ψ))
       → Σ[ ξ ∈ Env ] ⟦ ξ ⊧ ((¥ n) <ᵇ=> φ) && ψ ⟧pl
       → Σ[ ξ ∈ Env ] ⟦ ξ ⊧ ψ ⟧pl
  lem' n φ ψ n∉φ n∉ψ (ξ , [n<=>φ&&ψ]) = ξ , (proj₂ [n<=>φ&&ψ])

∨-false : ∀ b → b ∨ false ≡ b
∨-false true = refl
∨-false false = refl

¬⊂φ : ∀ φ n → (¥ n isSubFormula φ) ≡ (¥ n isSubFormula (~ φ))
¬⊂φ φ n rewrite ∨-false (¥ n isSubFormula φ) = refl

r : ∀ φ ψ n
  → T (not ((¥ n) isSubFormula φ))
  → T (not ((¥ n) isSubFormula ψ))
  → (∀ ξ → ⟦ ξ ⊧ (¥ n <ᵇ=> ψ) => φ ⟧pl)
  → ∀ ξ → ⟦ ξ ⊧ φ ⟧pl
r φ ψ n n∉φ n∉ψ f ξ =
  [ id , (λ [~φ] → ⊥-elim $ proj₂ (proj₂ (lem n ψ (~ φ) n∉ψ (PropEq.subst (λ b → T (not b)) (¬⊂φ φ n) n∉φ)
                                                            (_ , [~φ])))
                                  (f _ (proj₁ (proj₂ (lem n ψ (~ φ) n∉ψ
                                                          (PropEq.subst (λ b → T (not b)) (¬⊂φ φ n) n∉φ)
                                                          (_ , [~φ]))))))
  ]′ (ex-mid-pl ξ φ)

r' : ∀ φ ψ ρ n
  → T (not ((¥ n) isSubFormula φ))
  → T (not ((¥ n) isSubFormula ψ))
  → T (not ((¥ n) isSubFormula ρ))
  → (∀ ξ → ⟦ ξ ⊧ ((¥ n <ᵇ=> ψ) && ρ) => φ ⟧pl)
  → ∀ ξ → ⟦ ξ ⊧ ρ => φ ⟧pl
r' φ ψ ρ n n∉φ n∉ψ n∉ρ f = r (ρ => φ) ψ n (demorg2 (¥ n isSubFormula ρ) _
                             (∧-intro (not _) _ n∉ρ n∉φ)) n∉ψ (λ ξ' → curry (f ξ'))
