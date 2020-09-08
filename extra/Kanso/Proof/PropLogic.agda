module Kanso.Proof.PropLogic where

open import Data.Bool as Bool using (Bool; true; false; T; _∧_; _∨_)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.List as List using (List; _∷_; []; _++_)
open import Data.Nat as Nat using (ℕ)
open import Data.Product as Prod using (_×_; proj₁; proj₂; _,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.Unit as Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)
open import Function using (_∘_; id; const)

open import Kanso.PropIso
open import Kanso.Proof.List
open import Kanso.Proof.Util
open import Kanso.Boolean.Formula


data PropositionalRule : Set where
  ∧₊ →₋ efq raa ax : PropositionalRule
  ∧ˡ₋ ∧ʳ₋ ∨ˡ₊ ∨ʳ₊ →₊ : {φ : PL-Formula} → PropositionalRule
  ∨₋ : {φ ψ : PL-Formula} → PropositionalRule

proparity : PropositionalRule → ℕ
proparity ∧₊  = 2 -- and intro
proparity ∧ˡ₋ = 1 -- and elim l
proparity ∧ʳ₋ = 1 -- and elim r
proparity →₊  = 1 -- imp intro
proparity →₋  = 2 -- imp elim
proparity ∨ˡ₊ = 1 -- or intro l
proparity ∨ʳ₊ = 1 -- or intro r
proparity ∨₋  = 3 -- or elim
proparity efq = 1 -- efq
proparity raa = 1 -- raa
proparity ax  = 0 -- axiom

propcorrect : (k : PropositionalRule) → Vec [ PL-Formula ⇒ PL-Formula ] (proparity k)
            → [ PL-Formula ⇒ PL-Formula ] → Bool
propcorrect ∧₊ (Γ₁ ⇒ φ₁ ∷ Γ₂ ⇒ φ₂ ∷ []) (Γ₃ ⇒ φ₃) = (φ₃ ≡pl (φ₁ && φ₂)) ∧ ((Γ₁ ∪ Γ₂) ⊆ Γ₃)
propcorrect (∧ˡ₋ {φ₃}) (Γ₁ ⇒ φ₁ ∷ []) (Γ₂ ⇒ φ₂)   = (φ₁ ≡pl (φ₂ && φ₃)) ∧ (Γ₁ ⊆ Γ₂)
propcorrect (∧ʳ₋ {φ₃}) (Γ₁ ⇒ φ₁ ∷ []) (Γ₂ ⇒ φ₂)   = (φ₁ ≡pl (φ₃ && φ₂)) ∧ (Γ₁ ⊆ Γ₂)
propcorrect (→₊ {φ₃}) (Γ₁ ⇒ φ₁ ∷ []) (Γ₂ ⇒ φ₂)    = (φ₂ ≡pl (φ₃ => φ₁)) ∧ ((Γ₁ ∣ φ₃) ⊆ Γ₂)
propcorrect →₋ (Γ₁ ⇒ φ₁ ∷ Γ₂ ⇒ φ₂ ∷ []) (Γ₃ ⇒ φ₃) = (φ₁ ≡pl (φ₂ => φ₃)) ∧ ((Γ₁ ∪ Γ₂) ⊆ Γ₃)
propcorrect (∨ˡ₊ {φ₃}) (Γ₁ ⇒ φ₁ ∷ []) (Γ₂ ⇒ φ₂)   = (φ₂ ≡pl (φ₁ || φ₃)) ∧ (Γ₁ ⊆ Γ₂)
propcorrect (∨ʳ₊ {φ₃}) (Γ₁ ⇒ φ₁ ∷ []) (Γ₂ ⇒ φ₂)   = (φ₂ ≡pl (φ₃ || φ₁)) ∧ (Γ₁ ⊆ Γ₂)
propcorrect (∨₋ {φ₅} {φ₆}) (Γ₁ ⇒ φ₁ ∷ Γ₂ ⇒ φ₂ ∷ Γ₃ ⇒ φ₃ ∷ []) (Γ₄ ⇒ φ₄)
  = (φ₂ ≡pl φ₃) ∧ (φ₂ ≡pl φ₄) ∧ (φ₁ ≡pl (φ₅ || φ₆)) ∧ ((Γ₁ ∪ ((Γ₂ ∣ φ₅) ∪ (Γ₃ ∣ φ₆))) ⊆ Γ₄)
propcorrect efq (Γ₁ ⇒ φ₁ ∷ []) (Γ₂ ⇒ φ₂)          = (φ₁ ≡pl ¥false) ∧ (Γ₁ ⊆ Γ₂)
propcorrect raa (Γ₁ ⇒ φ₁ ∷ []) (Γ₂ ⇒ φ₂)          = (φ₁ ≡pl ¥false) ∧ ((Γ₁ ∣ ~ φ₂) ⊆ Γ₂)
propcorrect ax [] (Γ ⇒ φ) = φ ∈ Γ

propsound : (k : PropositionalRule) → (seq : Vec [ PL-Formula ⇒ PL-Formula ] (proparity k))
          → (conc : [ PL-Formula ⇒ PL-Formula ]) → T (propcorrect k seq conc)
          → Vec* (λ x → ∀ ξ → ⟦ ξ ⊧ andpl (πΓ x) => πφ x ⟧pl) seq
          → ∀ ξ → ⟦ ξ ⊧ andpl (πΓ conc) => πφ conc ⟧pl
propsound ∧₊ (Γ₁ ⇒ φ₁ ∷ Γ₂ ⇒ φ₂ ∷ []) (Γ₃ ⇒ φ₃) p (q1 ∷ q2 ∷ []) ξ hyp
  rewrite lift-≡pl φ₃ _ (∧-eliml p)
  = Prod.map (q1 ξ) (q2 ξ) (seq-split ξ Γ₁ Γ₂ (lem-seq-subst-foldr ξ Γ₃ (Γ₁ ++ Γ₂)
                        (lift-⊆ (Γ₁ ++ Γ₂) Γ₃ (∧-elimr (φ₃ ≡pl (φ₁ && φ₂)) p)) hyp))
propsound (∧ˡ₋ {φ₃}) (Γ₁ ⇒ φ₁ ∷ []) (Γ₂ ⇒ φ₂) p (q ∷ []) ξ hyp rewrite lift-≡pl φ₁ _ (∧-eliml p)
  = proj₁ (q ξ (lem-seq-subst-foldr ξ Γ₂ Γ₁ (lift-⊆ Γ₁ Γ₂ (∧-elimr (φ₁ ≡pl (φ₂ && φ₃)) p)) hyp))
propsound (∧ʳ₋ {φ₃}) (Γ₁ ⇒ φ₁ ∷ []) (Γ₂ ⇒ φ₂) p (q ∷ []) ξ hyp rewrite lift-≡pl φ₁ _ (∧-eliml p)
  = proj₂ (q ξ (lem-seq-subst-foldr ξ Γ₂ Γ₁ (lift-⊆ Γ₁ Γ₂ (∧-elimr (φ₁ ≡pl (φ₃ && φ₂)) p)) hyp))
propsound (→₊ {φ₃}) (Γ₁ ⇒ φ₁ ∷ []) (Γ₂ ⇒ φ₂) p (q ∷ []) ξ hyp rewrite lift-≡pl φ₂ _ (∧-eliml p)
  = λ x → q ξ (lem-seq-restrict-foldr' ξ Γ₁ φ₃ x (lem-seq-subst-foldr ξ Γ₂ (Γ₁ ∣ φ₃)
                                       (lift-⊆ (Γ₁ ∣ φ₃) Γ₂ (∧-elimr (φ₂ ≡pl (φ₃ => φ₁)) p)) hyp))
propsound →₋ (Γ₁ ⇒ φ₁ ∷ Γ₂ ⇒ φ₂ ∷ []) (Γ₃ ⇒ φ₃) p (q1 ∷ q2 ∷ []) ξ hyp
  rewrite lift-≡pl φ₁ _ (∧-eliml p)
  = let π = seq-split ξ Γ₁ Γ₂ (lem-seq-subst-foldr ξ Γ₃ (Γ₁ ++ Γ₂)
                                (lift-⊆ (Γ₁ ++ Γ₂) Γ₃ (∧-elimr (φ₁ ≡pl (φ₂ => φ₃)) p)) hyp)
    in q1 ξ (proj₁ π) (q2 ξ (proj₂ π))
propsound (∨ˡ₊ {φ₃}) (Γ₁ ⇒ φ₁ ∷ []) (Γ₂ ⇒ φ₂) p (q ∷ []) ξ hyp rewrite lift-≡pl φ₂ _ (∧-eliml p)
  = inj₁ (q ξ (lem-seq-subst-foldr ξ Γ₂ Γ₁ (lift-⊆ Γ₁ Γ₂ ((∧-elimr (φ₂ ≡pl (φ₁ || φ₃))) p)) hyp))
propsound (∨ʳ₊ {φ₃}) (Γ₁ ⇒ φ₁ ∷ []) (Γ₂ ⇒ φ₂) p (q ∷ []) ξ hyp rewrite lift-≡pl φ₂ _ (∧-eliml p)
  = inj₂ (q ξ (lem-seq-subst-foldr ξ Γ₂ Γ₁ (lift-⊆ Γ₁ Γ₂ ((∧-elimr (φ₂ ≡pl (φ₃ || φ₁))) p)) hyp))
propsound (∨₋ {φ₅} {φ₆}) (Γ₁ ⇒ φ₁ ∷ Γ₂ ⇒ φ₂ ∷ Γ₃ ⇒ φ₃ ∷ []) (Γ₄ ⇒ φ₄) p (q1 ∷ q2 ∷ q3 ∷ []) ξ hyp
  rewrite PropEq.sym (lift-≡pl φ₂ _ (∧-eliml p))
        | PropEq.sym (lift-≡pl φ₂ φ₄ ((∧-eliml ∘ ∧-elimr (φ₂ ≡pl φ₃)) p))
        | lift-≡pl φ₁ (φ₅ || φ₆) ((∧-eliml ∘ ∧-elimr (φ₂ ≡pl φ₄) ∘ ∧-elimr (φ₂ ≡pl φ₃)) p)
  = let Γ₄' = lem-seq-subst-foldr ξ Γ₄ (Γ₁ ++ Γ₂ ∣ φ₅ ++ Γ₃ ∣ φ₆) (lift-⊆ (Γ₁ ++ Γ₂ ∣ φ₅ ++ Γ₃ ∣ φ₆)
               Γ₄ ((∧-elimr (φ₁ ≡pl (φ₅ || φ₆)) ∘ ∧-elimr (φ₂ ≡pl φ₄) ∘ ∧-elimr (φ₂ ≡pl φ₃)) p)) hyp
    in [ (λ x → q2 ξ (lem-seq-restrict-foldr' ξ Γ₂ φ₅ x
             (proj₁ (seq-split ξ (Γ₂ ∣ φ₅) _ (proj₂ (seq-split ξ Γ₁ _ Γ₄'))))))
       , (λ x → q3 ξ (lem-seq-restrict-foldr' ξ Γ₃ φ₆ x
             (proj₂ (seq-split ξ (Γ₂ ∣ φ₅) _ (proj₂ (seq-split ξ Γ₁ _ Γ₄'))))))
       ]′ (q1 ξ (proj₁ (seq-split ξ Γ₁ _ Γ₄')))
propsound efq (Γ₁ ⇒ φ₁ ∷ []) (Γ₂ ⇒ φ₂) p (q ∷ []) ξ hyp rewrite lift-≡pl φ₁ _ (∧-eliml p)
  = ⊥-elim (q ξ (lem-seq-subst-foldr ξ Γ₂ Γ₁ (lift-⊆ Γ₁ Γ₂ (∧-elimr (φ₁ ≡pl ¥false) p)) hyp))
propsound raa (Γ₁ ⇒ φ₁ ∷ []) (Γ₂ ⇒ φ₂) p (q ∷ []) ξ hyp rewrite lift-≡pl φ₁ _ (∧-eliml p)
  = stbl-pl ξ φ₂ (λ x → q ξ (lem-seq-restrict-foldr' ξ Γ₁ (~ φ₂) x (lem-seq-subst-foldr ξ Γ₂
            (Γ₁ ∣ ~ φ₂) (lift-⊆ (Γ₁ ∣ (φ₂ => ¥false)) Γ₂ (∧-elimr (φ₁ ≡pl ¥false) p)) hyp)))
propsound ax [] ([] ⇒ φ) () q ξ hyp
propsound ax [] ((γ ∷ Γ) ⇒ φ) p q ξ hyp = ∨-elim (λ x → PropEq.subst (⟦_⊧_⟧pl ξ) (PropEq.sym (lift-≡pl φ _ x))
  (proj₁ hyp)) (λ k → propsound ax [] (Γ ⇒ φ) k [] ξ (proj₂ hyp)) p

proplogic : RuleSystem PropositionalRule [ PL-Formula ⇒ PL-Formula ] Env
                                         (λ ξ x → ⟦ ξ ⊧ andpl (πΓ x) => πφ x ⟧pl)
proplogic = record { arity = proparity; correct = propcorrect; sound = propsound }

private
  module test where
  open RuleSystem

  𝛗 = ¥ 0

  derivation : ProofList proplogic
  derivation = node ax ((𝛗 ∷ ~ (𝛗 || ~ 𝛗) ∷ []) ⇒ ~ (𝛗 || ~ 𝛗)) []
             ∷ node ax ((𝛗 ∷ ~ (𝛗 || ~ 𝛗) ∷ []) ⇒ 𝛗) []
             ∷ node (∨ˡ₊ {~ 𝛗}) ((𝛗 ∷ ~ (𝛗 || ~ 𝛗) ∷ []) ⇒ (𝛗 || ~ 𝛗)) (1 ∷ [])
             ∷ node →₋ ((𝛗 ∷ ~ (𝛗 || ~ 𝛗) ∷ []) ⇒ ¥false) (0 ∷ 2 ∷ [])
{-4-}        ∷ node (→₊ {𝛗}) ((~ (𝛗 || ~ 𝛗) ∷ []) ⇒ ~ 𝛗) (3 ∷ [])
             ∷ node ax ((~ 𝛗 ∷ ~ (𝛗 || ~ 𝛗) ∷ []) ⇒ ~ (𝛗 || ~ 𝛗)) []
             ∷ node ax ((~ 𝛗 ∷ ~ (𝛗 || ~ 𝛗) ∷ []) ⇒ ~ 𝛗) []
             ∷ node (∨ʳ₊ {𝛗}) ((~ 𝛗 ∷ ~ (𝛗 || ~ 𝛗) ∷ []) ⇒ (𝛗 || ~ 𝛗)) (6 ∷ [])
{-8-}        ∷ node →₋ ((~ 𝛗 ∷ ~ (𝛗 || ~ 𝛗) ∷ []) ⇒ ¥false) (5 ∷ 7 ∷ [])
             ∷ node raa ((~ (𝛗 || ~ 𝛗) ∷ []) ⇒ 𝛗) (8 ∷ [])
             ∷ node →₋ ((~ (𝛗 || ~ 𝛗) ∷ []) ⇒ ¥false) (4 ∷ 9 ∷ [])
             ∷ node raa ([] ⇒ (𝛗 || ~ 𝛗)) (10 ∷ [])
             ∷ []

  p¬p : ∀ ξ → ⟦ ξ ⊧ 𝛗 || ~ 𝛗 ⟧pl
  p¬p ξ = sound-list proplogic derivation tt tt ξ tt
