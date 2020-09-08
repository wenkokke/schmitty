module Kanso.Boolean.Formula.Substitute where


open import Data.Bool as Bool using (Bool; true; false)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Product as Prod using (_×_; proj₁; proj₂; _,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit as Unit using (⊤; tt)
open import Function using (id; const; _∘_)

open import Kanso.PropIso
open import Kanso.Boolean.Formula


substitute : PL-Formula → PL-Formula → PL-Formula → PL-Formula
substitute φ ψ ρ with φ ≡pl ρ
...| true = ψ
substitute φ ψ ¥true | false = ¥true
substitute φ ψ ¥false | false = ¥false
substitute φ ψ (y || y') | false = substitute φ ψ y || substitute φ ψ y'
substitute φ ψ (y && y') | false = substitute φ ψ y && substitute φ ψ y'
substitute φ ψ (y => y') | false = substitute φ ψ y => substitute φ ψ y'
substitute φ ψ (¥ y) | false = ¥ y


-- substitute φ for ψ in ρ
syntax substitute φ ψ ρ = ρ [ φ / ψ ]

mutual
  lem-subst : ∀ ξ φ ψ ρ → ⟦ ξ ⊧ ψ <ᵇ=> φ ⟧pl → ⟦ ξ ⊧ ρ ⟧pl → ⟦ ξ ⊧ ρ [ φ / ψ ] ⟧pl
  lem-subst ξ φ ψ ρ [φ↔ψ] [ρ] with ex-mid (φ ≡pl ρ)
  ...| inj₁ x  rewrite Tb x | lift-≡pl φ _ x = (proj₂ [φ↔ψ]) [ρ]
  lem-subst ξ φ ψ ¥true     [φ↔ψ] [ρ] | inj₂ x rewrite ¬Tb x = tt
  lem-subst ξ φ ψ ¥false    [φ↔ψ] [ρ] | inj₂ x rewrite ¬Tb x = [ρ]
  lem-subst ξ φ ψ (y || y') [φ↔ψ] [ρ] | inj₂ x rewrite ¬Tb x = Sum.map (lem-subst ξ φ ψ y [φ↔ψ])
                                                                       (lem-subst ξ φ ψ y' [φ↔ψ]) [ρ]
  lem-subst ξ φ ψ (y && y') [φ↔ψ] [ρ] | inj₂ x rewrite ¬Tb x = Prod.map (lem-subst ξ φ ψ y [φ↔ψ])
                                                                        (lem-subst ξ φ ψ y' [φ↔ψ]) [ρ]
  lem-subst ξ φ ψ (y => y') [φ↔ψ] [ρ] | inj₂ x rewrite ¬Tb x = lem-subst ξ φ ψ y' [φ↔ψ] ∘ [ρ] ∘ 
                                                                 lem-subst' ξ φ ψ y [φ↔ψ]
  lem-subst ξ φ ψ (¥ y)     [φ↔ψ] [ρ] | inj₂ x rewrite ¬Tb x = [ρ]

  lem-subst' : ∀ ξ φ ψ ρ → ⟦ ξ ⊧ ψ <ᵇ=> φ ⟧pl → ⟦ ξ ⊧ ρ [ φ / ψ ] ⟧pl → ⟦ ξ ⊧ ρ ⟧pl
  lem-subst' ξ φ ψ ρ [φ↔ψ] [ρ] with ex-mid (φ ≡pl ρ)
  ...| inj₁ x  rewrite Tb x | lift-≡pl φ _ x = (proj₁ [φ↔ψ]) [ρ]
  lem-subst' ξ φ ψ ¥true     [φ↔ψ] [ρ] | inj₂ x rewrite ¬Tb x = tt
  lem-subst' ξ φ ψ ¥false    [φ↔ψ] [ρ] | inj₂ x rewrite ¬Tb x = [ρ]
  lem-subst' ξ φ ψ (y || y') [φ↔ψ] [ρ] | inj₂ x rewrite ¬Tb x = Sum.map (lem-subst' ξ φ ψ y [φ↔ψ])
                                                                        (lem-subst' ξ φ ψ y' [φ↔ψ]) [ρ]
  lem-subst' ξ φ ψ (y && y') [φ↔ψ] [ρ] | inj₂ x rewrite ¬Tb x = Prod.map (lem-subst' ξ φ ψ y [φ↔ψ])
                                                                         (lem-subst' ξ φ ψ y' [φ↔ψ]) [ρ]
  lem-subst' ξ φ ψ (y => y') [φ↔ψ] [ρ] | inj₂ x rewrite ¬Tb x = lem-subst' ξ φ ψ y' [φ↔ψ] ∘ [ρ] ∘ 
                                                                  lem-subst ξ φ ψ y [φ↔ψ]
  lem-subst' ξ φ ψ (¥ y)     [φ↔ψ] [ρ] | inj₂ x rewrite ¬Tb x = [ρ]
