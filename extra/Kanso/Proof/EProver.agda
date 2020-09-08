module Kanso.Proof.EProver where

open import Data.Bool as Bool using (Bool; true; false; T; not; _∧_; _∨_)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.List as List using (List; _∷_; []; _++_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ)
open import Data.Product as Prod using (_×_; proj₁; proj₂; _,_; curry)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.Unit as Unit using (⊤; tt)
open import Function using (_$_; _∘_; id; const)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

open import Kanso.PropIso
open import Kanso.Boolean.Formula
open import Kanso.Boolean.Formula.Equivalence
open import Kanso.Boolean.Formula.Substitute
open import Kanso.Boolean.Formula.DropEquivalence
open import Kanso.Boolean.Formula.Distribute
open import Kanso.Boolean.Formula.RemoveConstants
open import Kanso.Proof.EProver.PM
open import Kanso.Proof.EProver.NNF
open import Kanso.Proof.List
open import Kanso.Proof.Util


private
  Formula : Set
  Formula = [ PL-Formula ⇒ PL-Formula ]

{- TO DO: combine refute1 with refute2 -}
mutual
  refute1 : ∀ ξ φ ψ → ⟦ ξ ⊧ ψ ⟧pl → ⟦ ξ ⊧ φ ⟧pl → ⟦ ξ ⊧ φ [ (~ ψ) / ¥false ] ⟧pl
  refute1 ξ φ ψ [ψ] [φ] with ex-mid ((~ ψ) ≡pl φ)
  ...| inj₁ x rewrite Tb x | PropEq.sym (lift-≡pl (~ ψ) φ x) = [φ] [ψ]
  refute1 ξ ¥true ψ     [ψ] [φ] | inj₂ x = tt
  refute1 ξ ¥false ψ    [ψ] [φ] | inj₂ x = [φ]
  refute1 ξ (y || y') ψ [ψ] [φ] | inj₂ x = Sum.map  (refute1 ξ y ψ [ψ]) (refute1 ξ y' ψ [ψ]) [φ]
  refute1 ξ (y && y') ψ [ψ] [φ] | inj₂ x = Prod.map (refute1 ξ y ψ [ψ]) (refute1 ξ y' ψ [ψ]) [φ]
  refute1 ξ (y => y') ψ [ψ] [φ] | inj₂ x rewrite ¬Tb x
    = (refute1 ξ y' ψ [ψ]) ∘ [φ] ∘ (refute1' ξ y ψ [ψ])
  refute1 ξ (¥ y) ψ     [ψ] [φ] | inj₂ x = [φ]

  refute1' : ∀ ξ φ ψ → ⟦ ξ ⊧ ψ ⟧pl → ⟦ ξ ⊧ φ [ (~ ψ) / ¥false ] ⟧pl → ⟦ ξ ⊧ φ ⟧pl
  refute1' ξ φ ψ [ψ] [φ] with ex-mid ((~ ψ) ≡pl φ)
  ...| inj₁ x rewrite Tb x | PropEq.sym (lift-≡pl (~ ψ) φ x) = const [φ]
  refute1' ξ ¥true ψ     [ψ] [φ] | inj₂ x = tt
  refute1' ξ ¥false ψ    [ψ] [φ] | inj₂ x = [φ]
  refute1' ξ (y || y') ψ [ψ] [φ] | inj₂ x = Sum.map  (refute1' ξ y ψ [ψ]) (refute1' ξ y' ψ [ψ]) [φ]
  refute1' ξ (y && y') ψ [ψ] [φ] | inj₂ x = Prod.map (refute1' ξ y ψ [ψ]) (refute1' ξ y' ψ [ψ]) [φ]
  refute1' ξ (y => y') ψ [ψ] [φ] | inj₂ x rewrite ¬Tb x
    = (refute1' ξ y' ψ [ψ]) ∘ [φ] ∘ (refute1 ξ y ψ [ψ])
  refute1' ξ (¥ y) ψ     [ψ] [φ] | inj₂ x = [φ]

mutual
  refute2 : ∀ ξ φ ψ → ⟦ ξ ⊧ ~ ψ ⟧pl → ⟦ ξ ⊧ φ ⟧pl → ⟦ ξ ⊧ φ [ ψ / ¥false ] ⟧pl
  refute2 ξ φ ψ [ψ] [φ] with ex-mid (ψ ≡pl φ)
  ...| inj₁ x rewrite Tb x | PropEq.sym (lift-≡pl ψ φ x) = [ψ] [φ]
  refute2 ξ ¥true ψ     [ψ] [φ] | inj₂ x rewrite ¬Tb x = tt
  refute2 ξ ¥false ψ    [ψ] [φ] | inj₂ x rewrite ¬Tb x = [φ]
  refute2 ξ (y || y') ψ [ψ] [φ] | inj₂ x rewrite ¬Tb x
    = Sum.map (refute2 ξ y ψ [ψ]) (refute2 ξ y' ψ [ψ]) [φ]
  refute2 ξ (y && y') ψ [ψ] [φ] | inj₂ x rewrite ¬Tb x
    = Prod.map (refute2 ξ y ψ [ψ]) (refute2 ξ y' ψ [ψ]) [φ]
  refute2 ξ (y => y') ψ [ψ] [φ] | inj₂ x rewrite ¬Tb x
    = (refute2 ξ y' ψ [ψ]) ∘ [φ] ∘ (refute2' ξ y ψ [ψ])
  refute2 ξ (¥ y) ψ     [ψ] [φ] | inj₂ x rewrite ¬Tb x = [φ]

  refute2' : ∀ ξ φ ψ → ⟦ ξ ⊧ ~ ψ ⟧pl → ⟦ ξ ⊧ φ [ ψ / ¥false ] ⟧pl → ⟦ ξ ⊧ φ ⟧pl
  refute2' ξ φ ψ [ψ] [φ] with ex-mid (ψ ≡pl φ)
  refute2' ξ φ ψ         [ψ] [φ] | inj₁ x rewrite Tb x | PropEq.sym (lift-≡pl ψ φ x) = ⊥-elim [φ]
  refute2' ξ ¥true ψ     [ψ] [φ] | inj₂ x rewrite ¬Tb x = tt
  refute2' ξ ¥false ψ    [ψ] [φ] | inj₂ x rewrite ¬Tb x = [φ]
  refute2' ξ (y || y') ψ [ψ] [φ] | inj₂ x rewrite ¬Tb x
    = Sum.map (refute2' ξ y ψ [ψ]) (refute2' ξ y' ψ [ψ]) [φ]
  refute2' ξ (y && y') ψ [ψ] [φ] | inj₂ x rewrite ¬Tb x
    = Prod.map (refute2' ξ y ψ [ψ]) (refute2' ξ y' ψ [ψ]) [φ]
  refute2' ξ (y => y') ψ [ψ] [φ] | inj₂ x rewrite ¬Tb x
    = refute2' ξ y' ψ [ψ] ∘ [φ] ∘ refute2 ξ y ψ [ψ]
  refute2' ξ (¥ y) ψ     [ψ] [φ] | inj₂ x rewrite ¬Tb x = [φ]

apply-Γ : ∀ ξ Γ → ⟦ ξ ⊧ Γ ⟧⇒ → ⟦ ξ ⊧ andpl (πΓ Γ) => πφ Γ ⟧pl
apply-Γ ξ ([] ⇒ φ)            pθ pΓ = pθ
apply-Γ ξ ((x ∷ []) ⇒ φ)      pθ pΓ = pθ (proj₁ pΓ)
apply-Γ ξ ((x ∷ x' ∷ xs) ⇒ φ) pθ pΓ = apply-Γ ξ ((x' ∷ xs) ⇒ φ)
                                              (curry pθ (proj₁ pΓ)) (proj₂ pΓ)

apply-Γ' : ∀ ξ Γ → ⟦ ξ ⊧ andpl (πΓ Γ) => πφ Γ ⟧pl → ⟦ ξ ⊧ Γ ⟧⇒
apply-Γ' ξ ([] ⇒ φ)           p = p tt
apply-Γ' ξ ((γ ∷ []) ⇒ φ)     p = λ x → (curry p) x tt
apply-Γ' ξ ((γ ∷ γ' ∷ Γ) ⇒ φ) p = λ x → apply-Γ' ξ ((γ' ∷ Γ) ⇒ φ)
                                                 (curry p (proj₁ x)) (proj₂ x)

_isSubConjunct_ : PL-Formula → PL-Formula → Bool
_isSubConjunct_ φ ψ with φ ≡ᵇpl ψ
...| true = true
φ isSubConjunct ¥true     | false = false
φ isSubConjunct ¥false    | false = false
φ isSubConjunct (y || y') | false = false
φ isSubConjunct (y && y') | false = φ isSubConjunct y ∨ φ isSubConjunct y'
φ isSubConjunct (y => y') | false = false
φ isSubConjunct ¥ y       | false = false

lemSubConjunct : ∀ ξ φ ψ → T (φ isSubConjunct ψ) → ⟦ ξ ⊧ ψ ⟧pl → ⟦ ξ ⊧ φ ⟧pl
lemSubConjunct ξ φ ψ p [ψ] with ex-mid (φ ≡ᵇpl ψ)
...| inj₁ x = lift-≡ᵇpl← φ ψ x ξ [ψ]
lemSubConjunct ξ φ ¥true     p [ψ] | inj₂ x rewrite ¬Tb x = ⊥-elim p
lemSubConjunct ξ φ ¥false    p [ψ] | inj₂ x rewrite ¬Tb x = ⊥-elim p
lemSubConjunct ξ φ (y || y') p [ψ] | inj₂ x rewrite ¬Tb x = ⊥-elim p
lemSubConjunct ξ φ (y && y') p [ψ] | inj₂ x rewrite ¬Tb x =
                                              [ (λ x → (lemSubConjunct ξ φ y) x (proj₁ [ψ])) ,
                                                (λ x → (lemSubConjunct ξ φ y') x (proj₂ [ψ])) ]′
                                                (lem-bool-∨-s (φ isSubConjunct y) _ p)
lemSubConjunct ξ φ (y => y') p [ψ] | inj₂ x rewrite ¬Tb x = ⊥-elim p
lemSubConjunct ξ φ (¥ y)     p [ψ] | inj₂ x rewrite ¬Tb x = ⊥-elim p

data ERule : Set where
  fof_nnf fof_simplification split_conjunct cn axiom unsat distribute : ERule
  apply_def rw sr pm fresh : ERule

e-arity : ERule → ℕ
e-arity fof_nnf            = 1 -- negated normal form (fol)
e-arity fof_simplification = 1 -- constsant removal (fol)
e-arity axiom              = 0 -- assumption
e-arity apply_def          = 2 -- rewrite a formula with an equivalence, one way
e-arity split_conjunct     = 1 -- split a n-ary conjunction
e-arity rw                 = 2 -- re-write, refute leaving constant
e-arity sr                 = 2 -- simply reflect, refute removing constant where possible
e-arity pm                 = 2 -- paramodulate, refute two clauses
e-arity cn                 = 1 -- clause normalise, remove constants
e-arity unsat              = 1 -- reducto ad adsurdum
e-arity distribute         = 1 -- place a formula in cnf by niave distribution
e-arity fresh              = 1 -- virtual rule, discharges equivalences from introduced definitions

correct-apply : Formula → Formula → Formula → Bool
correct-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ((φ₂a => φ₂b) && (φ₂b' => φ₂a'))) (Γ₃ ⇒ φ₃)
  = φ₂a ≡pl φ₂a' ∧ φ₂b ≡pl φ₂b' ∧ φ₃ ≡pl (φ₁ [ φ₂b / φ₂a ]) ∧ (Γ₁ ++ Γ₂) ⊆ Γ₃
correct-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ φ₂) (Γ₃ ⇒ φ₃) = false

correct-fresh : Formula → Formula → Bool
correct-fresh ((((¥ n => ψ) && (ψ' => ¥ n')) ∷ Γ₁) ⇒ φ₁) (Γ₂ ⇒ φ₂)
  = φ₁ ≡pl φ₂ ∧ (n Nat.≡ᵇ n') ∧ ψ ≡pl ψ' ∧ not (¥ n isSubFormula φ₂)
    ∧ not (¥ n isSubFormula andpl Γ₂)
    ∧ not (¥ n isSubFormula ψ) ∧ Γ₁ ⊆ Γ₂
correct-fresh (_ ⇒ φ₁) (Γ₂ ⇒ φ₂) = false

correct-rw :  Formula → Formula → Formula → Bool
correct-rw (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (φ₂ => ¥false)) (Γ₃ ⇒ φ₃) = φ₃ ≡ᵇpl (φ₁ [ φ₂ / ¥false ])
                                                         ∧ (Γ₁ ++ Γ₂) ⊆ Γ₃
correct-rw (Γ₁ ⇒ φ₁) (Γ₂ ⇒ φ₂) (Γ₃ ⇒ φ₃) = φ₃ ≡ᵇpl (φ₁ [ ~ φ₂ / ¥false ])
                                             ∧ (Γ₁ ++ Γ₂) ⊆ Γ₃

correct-sr : Formula → Formula → Formula → Bool
correct-sr (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (φ₂ => ¥false)) (Γ₃ ⇒ φ₃)
  = φ₃ ≡ᵇpl const-removal (φ₁ [ φ₂ / ¥false ]) ∧ (Γ₁ ++ Γ₂) ⊆ Γ₃
correct-sr (Γ₁ ⇒ φ₁) (Γ₂ ⇒ φ₂) (Γ₃ ⇒ φ₃) = φ₃ ≡ᵇpl const-removal (φ₁ [ ~ φ₂ / ¥false ])
                                             ∧ (Γ₁ ++ Γ₂) ⊆ Γ₃

correct-pm : Formula → Formula → Formula → Bool
correct-pm (Γ₁ ⇒ φ₁) (Γ₂ ⇒ φ₂) (Γ₃ ⇒ φ₃)
  = conflict-negleft φ₁ φ₂ ∧ φ₃ ≡ᵇpl const-removal (pm' φ₁ φ₂) ∧ (Γ₁ ++ Γ₂) ⊆ Γ₃

e-correct : (k : ERule) → Vec Formula (e-arity k) → Formula → Bool
e-correct fof_nnf            (Γ₁ ⇒ φ ∷ xs) (Γ₂ ⇒ ψ)  = ψ ≡ᵇpl const-removal (mknnf φ) ∧ Γ₁ ⊆ Γ₂
e-correct fof_simplification (Γ₁ ⇒ φ₁ ∷ _) (Γ₂ ⇒ φ₂) = φ₂ ≡ᵇpl const-removal φ₁ ∧ Γ₁ ⊆ Γ₂
e-correct distribute         (Γ₁ ⇒ φ₁ ∷ _) (Γ₂ ⇒ φ₂) = φ₂ ≡ᵇpl mkdist φ₁ ∧ Γ₁ ⊆ Γ₂
e-correct axiom              seq           (Γ₁ ⇒ φ₁) = φ₁ ∈ Γ₁
e-correct apply_def          (a ∷ b ∷ _)   c         = correct-apply a b c
e-correct split_conjunct     (Γ₁ ⇒ φ₁ ∷ _) (Γ₂ ⇒ φ₂) = φ₂ isSubConjunct φ₁ ∧ Γ₁ ⊆ Γ₂
e-correct rw                 (a ∷ b ∷ _)   c         = correct-rw a b c
e-correct sr                 (a ∷ b ∷ _)   c         = correct-sr a b c
e-correct pm                 (a ∷ b ∷ _)   c         = correct-pm a b c
e-correct cn                 (Γ₁ ⇒ φ₁ ∷ _) (Γ₂ ⇒ φ₂) = φ₂ ≡ᵇpl const-removal φ₁ ∧ Γ₁ ⊆ Γ₂
e-correct unsat              (Γ₁ ⇒ φ₁ ∷ _) (Γ₂ ⇒ φ₂) = φ₁ ≡pl ¥false ∧ (Γ₁ ∣ (~ φ₂)) ⊆ Γ₂
e-correct fresh              (a ∷ _)       b         = correct-fresh a b

sound-apply : (a b c : Formula) → (∀ ξ → ⟦ ξ ⊧ a ⟧⇒) → (∀ ξ → ⟦ ξ ⊧ b ⟧⇒) → T (correct-apply a b c)
            → ∀ ξ → ⟦ ξ ⊧ c ⟧⇒
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ((φ₂a => φ₂b) && (φ₂b' => φ₂a'))) (Γ₃ ⇒ φ₃) pa pb p ξ
  rewrite (lift-≡pl φ₃ _ (∧-eliml (∧-elimr (φ₂b ≡pl φ₂b') (∧-elimr (φ₂a ≡pl φ₂a') p))))
  = apply-Γ' ξ (Γ₃ ⇒ (φ₁ [ φ₂b / φ₂a ]) )
             (λ [Γ₃] → lem-subst ξ φ₂b φ₂a φ₁ (Prod.map id
                         (λ x' x0 → PropEq.subst (⟦_⊧_⟧pl ξ) (PropEq.sym (lift-≡pl φ₂a _ (∧-eliml p)))
                                          (x' (PropEq.subst (⟦_⊧_⟧pl ξ) (lift-≡pl φ₂b _
                                                     (∧-eliml (∧-elimr (φ₂a ≡pl φ₂a') p))) x0)))
                         (apply-Γ ξ (Γ₂ ⇒ ((φ₂a => φ₂b) && (φ₂b' => φ₂a'))) (pb ξ)
                                  (proj₂ (seq-split ξ Γ₁ Γ₂ (lem-seq-subst-foldr ξ Γ₃ (Γ₁ ∪ Γ₂)
                                         (lift-⊆ (Γ₁ ∪ Γ₂) Γ₃ ((∧-elimr
                                         (φ₃ ≡pl (φ₁ [ φ₂b / φ₂a ])) (∧-elimr (φ₂b ≡pl φ₂b')
                                         (∧-elimr (φ₂a ≡pl φ₂a') p))))) [Γ₃])))))
                       (apply-Γ ξ (Γ₁ ⇒ φ₁) (pa ξ) (proj₁ (seq-split ξ Γ₁ Γ₂
                               (lem-seq-subst-foldr ξ Γ₃ (Γ₁ ∪ Γ₂) (lift-⊆ (Γ₁ ∪ Γ₂) Γ₃
                                (∧-elimr (φ₃ ≡pl (φ₁ [ φ₂b / φ₂a ])) (∧-elimr
                                (φ₂b ≡pl φ₂b') (∧-elimr (φ₂a ≡pl φ₂a') p)))) [Γ₃])))))
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ¥true)                     (Γ₃ ⇒ φ₃) pa pb p ξ = ⊥-elim p
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ¥false)                    (Γ₃ ⇒ φ₃) pa pb p ξ = ⊥-elim p
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y || y'))                 (Γ₃ ⇒ φ₃) pa pb p ξ = ⊥-elim p
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (¥true && y'))             (Γ₃ ⇒ φ₃) pa pb p ξ = ⊥-elim p
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (¥false && y'))            (Γ₃ ⇒ φ₃) pa pb p ξ = ⊥-elim p
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ((y || y') && y0))         (Γ₃ ⇒ φ₃) pa pb p ξ = ⊥-elim p
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ((y && y') && y0))         (Γ₃ ⇒ φ₃) pa pb p ξ = ⊥-elim p
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ((y => y') && ¥true))      (Γ₃ ⇒ φ₃) pa pb p ξ = ⊥-elim p
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ((y => y') && ¥false))     (Γ₃ ⇒ φ₃) pa pb p ξ = ⊥-elim p
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ((y => y') && (y0 || y1))) (Γ₃ ⇒ φ₃) pa pb p ξ = ⊥-elim p
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ((y => y') && (y0 && y1))) (Γ₃ ⇒ φ₃) pa pb p ξ = ⊥-elim p
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ((y => y') && ¥ y0))       (Γ₃ ⇒ φ₃) pa pb p ξ = ⊥-elim p
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (¥ y && y'))               (Γ₃ ⇒ φ₃) pa pb p ξ = ⊥-elim p
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y => y'))                 (Γ₃ ⇒ φ₃) pa pb p ξ = ⊥-elim p
sound-apply (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ¥ y)                       (Γ₃ ⇒ φ₃) pa pb p ξ = ⊥-elim p

sound-fresh : (a b : Formula) → (∀ ξ → ⟦ ξ ⊧ andpl (πΓ a) => πφ a ⟧pl) → T (correct-fresh a b)
            → ∀ ξ → ⟦ ξ ⊧ andpl (πΓ b) => πφ b ⟧pl
sound-fresh ([] ⇒ φ₁) (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh ((¥true ∷ Γ₁) ⇒ φ₁)                             (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh ((¥false ∷ Γ₁) ⇒ φ₁)                            (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh ((y || y' ∷ Γ₁) ⇒ φ₁)                           (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh ((¥true && y' ∷ Γ₁) ⇒ φ₁)                       (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh ((¥false && y' ∷ Γ₁) ⇒ φ₁)                      (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh (((y || y') && y0 ∷ Γ₁) ⇒ φ₁)                   (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh (((y && y') && y0 ∷ Γ₁) ⇒ φ₁)                   (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh (((¥true => y') && y0 ∷ Γ₁) ⇒ φ₁)               (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh (((¥false => y') && y0 ∷ Γ₁) ⇒ φ₁)              (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh ((((y || y') => y0) && y1 ∷ Γ₁) ⇒ φ₁)           (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh ((((y && y') => y0) && y1 ∷ Γ₁) ⇒ φ₁)           (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh ((((y => y') => y0) && y1 ∷ Γ₁) ⇒ φ₁)           (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh (((¥ y => y') && ¥true ∷ Γ₁) ⇒ φ₁)              (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh (((¥ y => y') && ¥false ∷ Γ₁) ⇒ φ₁)             (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh (((¥ y => y') && (y0 || y1) ∷ Γ₁) ⇒ φ₁)         (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh (((¥ y => y') && (y0 && y1) ∷ Γ₁) ⇒ φ₁)         (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh (((¥ y => y') && (y0 => ¥true) ∷ Γ₁) ⇒ φ₁)      (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh (((¥ y => y') && (y0 => ¥false) ∷ Γ₁) ⇒ φ₁)     (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh (((¥ y => y') && (y0 => (y1 || y2)) ∷ Γ₁) ⇒ φ₁) (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh (((¥ y => y') && (y0 => (y1 && y2)) ∷ Γ₁) ⇒ φ₁) (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh (((¥ y => y') && (y0 => (y1 => y2)) ∷ Γ₁) ⇒ φ₁) (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh (((¥ n => ψ) && (ψ' => ¥ n') ∷ Γ₁) ⇒ φ₁) (Γ₂ ⇒ φ₂) pa p ξ [Γ₂]
  rewrite lift-≡pl φ₁ _ (∧-eliml p)
  = r' φ₂ ψ (andpl Γ₂) n
       (∧-eliml (∧-elimr (ψ ≡pl ψ') (∧-elimr (n Nat.≡ᵇ n') (∧-elimr (φ₁ ≡pl φ₂) p))))
       (∧-eliml (∧-elimr  (not (¥ n isSubFormula andpl Γ₂))
                          (∧-elimr (not (¥ n isSubFormula φ₂))
                                   (∧-elimr (ψ ≡pl ψ')
                                            (∧-elimr (n Nat.≡ᵇ n') (∧-elimr (φ₁ ≡pl φ₂) p))))))
       (∧-eliml (∧-elimr (not (¥ n isSubFormula φ₂))
                         (∧-elimr (ψ ≡pl ψ') (∧-elimr (n Nat.≡ᵇ n') (∧-elimr (φ₁ ≡pl φ₂) p)))))
       (λ ξ' x → pa ξ' (Prod.map (Prod.map id (λ x0 x1 → PropEq.subst (T ∘ ξ')
                    (lift-≡ᵇ n n' ((∧-eliml (∧-elimr (φ₁ ≡pl φ₂) p))))
                    (x0 (PropEq.subst (⟦_⊧_⟧pl ξ') (PropEq.sym (lift-≡pl ψ _ ((∧-eliml (∧-elimr (n Nat.≡ᵇ n')
                        (∧-elimr (φ₁ ≡pl φ₂) p)))))) x1))))
                                 (lem-seq-subst-foldr ξ' Γ₂ Γ₁ (lift-⊆ Γ₁ Γ₂
                        (∧-elimr (not (¥ n isSubFormula ψ)) (∧-elimr (not (¥ n
                        isSubFormula andpl Γ₂)) (∧-elimr (not (¥ n isSubFormula φ₂))
                        (∧-elimr (ψ ≡pl ψ') (∧-elimr (n Nat.≡ᵇ n') (∧-elimr (φ₁ ≡pl φ₂) p)))))))) x))
       ξ [Γ₂]
sound-fresh (((¥ y => y') && ¥ y0 ∷ Γ₁) ⇒ φ₁)               (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh ((¥ y && y' ∷ Γ₁) ⇒ φ₁)                         (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh ((y => y' ∷ Γ₁) ⇒ φ₁)                           (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p
sound-fresh ((¥ y ∷ Γ₁) ⇒ φ₁)                               (Γ₂ ⇒ φ₂) pa p ξ [Γ₂] = ⊥-elim p

sound-rw' : (a b c : Formula)
          → (∀ ξ → ⟦ ξ ⊧ andpl (πΓ a) => πφ a ⟧pl) → (∀ ξ → ⟦ ξ ⊧ andpl (πΓ b) => πφ b ⟧pl)
          → T (πφ c ≡ᵇpl ((πφ a) [ ~ (πφ b) / ¥false ]) ∧ ((πΓ a) ++ (πΓ b)) ⊆ (πΓ c))
          → ∀ ξ → ⟦ ξ ⊧ andpl (πΓ c) => πφ c ⟧pl
sound-rw' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ φ₂) (Γ₃ ⇒ φ₃) pa pb p ξ [Γ₃]
  = lift-≡ᵇpl← φ₃ ( φ₁ [ (~ φ₂) / ¥false ] ) (∧-eliml p) ξ
               (refute1 ξ φ₁ φ₂
                 (pb ξ (proj₂ (seq-split ξ Γ₁ Γ₂ (lem-seq-subst-foldr ξ Γ₃ (Γ₁ ∪ Γ₂)
                     (lift-⊆ (Γ₁ ∪ Γ₂) Γ₃ (∧-elimr (φ₃ ≡ᵇpl (φ₁ [ ~ φ₂ / ¥false ])) p))
                     [Γ₃]))))
                 (pa ξ (proj₁ (seq-split ξ Γ₁ Γ₂ (lem-seq-subst-foldr ξ Γ₃ (Γ₁ ∪ Γ₂)
                     (lift-⊆ (Γ₁ ∪ Γ₂) Γ₃ (∧-elimr (φ₃ ≡ᵇpl (φ₁ [ ~ φ₂ / ¥false ])) p))
                     [Γ₃])))))

sound-rw : (a b c : Formula)
         → (∀ ξ → ⟦ ξ ⊧ andpl (πΓ a) => πφ a ⟧pl) → (∀ ξ → ⟦ ξ ⊧ andpl (πΓ b) => πφ b ⟧pl)
         → T (correct-rw a b c )
         → ∀ ξ → ⟦ ξ ⊧ List.foldr _&&_ ¥true (πΓ c) => πφ c ⟧pl
sound-rw (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ¥true)             (Γ₃ ⇒ φ₃) = sound-rw' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-rw (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ¥false)            (Γ₃ ⇒ φ₃) = sound-rw' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-rw (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y || y'))         (Γ₃ ⇒ φ₃) = sound-rw' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-rw (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y && y'))         (Γ₃ ⇒ φ₃) = sound-rw' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-rw (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y => ¥true))      (Γ₃ ⇒ φ₃) = sound-rw' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-rw (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y => (y' || y0))) (Γ₃ ⇒ φ₃) = sound-rw' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-rw (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y => (y' && y0))) (Γ₃ ⇒ φ₃) = sound-rw' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-rw (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y => (y' => y0))) (Γ₃ ⇒ φ₃) = sound-rw' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-rw (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y => ¥ y'))       (Γ₃ ⇒ φ₃) = sound-rw' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-rw (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ¥ y)               (Γ₃ ⇒ φ₃) = sound-rw' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)

sound-rw (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (φ₂ => ¥false)) (Γ₃ ⇒ φ₃) = λ pa pb p ξ [Γ₃] →
  lift-≡ᵇpl← φ₃ ( φ₁ [ φ₂ / ¥false ] ) (∧-eliml p) ξ
               (refute2 ξ φ₁ φ₂
                 (pb ξ (proj₂ (seq-split ξ Γ₁ Γ₂ (lem-seq-subst-foldr ξ Γ₃ (Γ₁ ∪ Γ₂)
                     (lift-⊆ (Γ₁ ∪ Γ₂) Γ₃ (∧-elimr (φ₃ ≡ᵇpl (φ₁ [ φ₂ / ¥false ])) p)) [Γ₃]))))
                 (pa ξ (proj₁ (seq-split ξ Γ₁ Γ₂ (lem-seq-subst-foldr ξ Γ₃ (Γ₁ ∪ Γ₂)
                     (lift-⊆ (Γ₁ ∪ Γ₂) Γ₃ (∧-elimr (φ₃ ≡ᵇpl (φ₁ [ φ₂ / ¥false ])) p)) [Γ₃])))))

sound-sr' : (a b c : Formula)
         → (∀ ξ → ⟦ ξ ⊧ andpl (πΓ a) => πφ a ⟧pl) → (∀ ξ → ⟦ ξ ⊧ andpl (πΓ b) => πφ b ⟧pl)
         → T (πφ c ≡ᵇpl const-removal ((πφ a) [ ~ (πφ b) / ¥false ])
                 ∧ (((πΓ a) ++ (πΓ b)) ⊆ (πΓ c)))
         → ∀ ξ → ⟦ ξ ⊧ andpl (πΓ c) => πφ c ⟧pl
sound-sr' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ φ₂) (Γ₃ ⇒ φ₃) pa pb p ξ [Γ₃]
  = lift-≡ᵇpl← φ₃ (const-removal (φ₁ [ (~ φ₂) / ¥false ]))
     (∧-eliml p) ξ (lem-no-const ξ  (φ₁ [ (~ φ₂) / ¥false ]) (refute1 ξ φ₁ φ₂
       (pb ξ (proj₂ (seq-split ξ Γ₁ Γ₂ (lem-seq-subst-foldr ξ Γ₃ (Γ₁ ∪ Γ₂)
         (lift-⊆ (Γ₁ ∪ Γ₂) Γ₃ (∧-elimr (φ₃ ≡ᵇpl const-removal (φ₁ [ ~ φ₂ / ¥false ]))p))
         [Γ₃]))))
       (pa ξ (proj₁ (seq-split ξ Γ₁ Γ₂ (lem-seq-subst-foldr ξ Γ₃ (Γ₁ ∪ Γ₂)
         (lift-⊆ (Γ₁ ∪ Γ₂) Γ₃ (∧-elimr (φ₃ ≡ᵇpl const-removal (φ₁ [ ~ φ₂ / ¥false ]))p))
         [Γ₃])))) ))

sound-sr : (a b c : Formula)
         → (∀ ξ → ⟦ ξ ⊧ andpl (πΓ a) => πφ a ⟧pl) → (∀ ξ → ⟦ ξ ⊧ andpl (πΓ b) => πφ b ⟧pl)
         → T (correct-sr a b c) → ∀ ξ → ⟦ ξ ⊧ andpl (πΓ c) => πφ c ⟧pl
sound-sr (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ¥true)          (Γ₃ ⇒ φ₃) = sound-sr' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-sr (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ¥false)         (Γ₃ ⇒ φ₃) = sound-sr' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-sr (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y || y'))      (Γ₃ ⇒ φ₃) = sound-sr' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-sr (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y && y'))      (Γ₃ ⇒ φ₃) = sound-sr' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-sr (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y => ¥true))   (Γ₃ ⇒ φ₃) = sound-sr' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-sr (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (φ₂ => ¥false)) (Γ₃ ⇒ φ₃) = λ  pa pb p ξ [Γ₃] →
  lift-≡ᵇpl← φ₃ (const-removal (φ₁ [ φ₂ / ¥false ]))
    (∧-eliml p) ξ
    (lem-no-const ξ (φ₁ [ φ₂ / ¥false ])
      (refute2 ξ φ₁ φ₂ (pb ξ (proj₂ (seq-split ξ Γ₁ Γ₂ (lem-seq-subst-foldr ξ Γ₃ (Γ₁ ∪ Γ₂)
        (lift-⊆ (Γ₁ ∪ Γ₂) Γ₃ (∧-elimr (φ₃ ≡ᵇpl const-removal (φ₁ [ φ₂ / ¥false ])) p))
        [Γ₃]))))
      (pa ξ (proj₁ (seq-split ξ Γ₁ Γ₂ (lem-seq-subst-foldr ξ Γ₃ (Γ₁ ∪ Γ₂)
          (lift-⊆ (Γ₁ ∪ Γ₂) Γ₃ (∧-elimr (φ₃ ≡ᵇpl const-removal (φ₁ [ φ₂ / ¥false ])) p))
          [Γ₃])))) ))
sound-sr (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y => (y' || y0))) (Γ₃ ⇒ φ₃) = sound-sr' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-sr (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y => (y' && y0))) (Γ₃ ⇒ φ₃) = sound-sr' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-sr (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y => (y' => y0))) (Γ₃ ⇒ φ₃) = sound-sr' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-sr (Γ₁ ⇒ φ₁) (Γ₂ ⇒ (y => ¥ y'))       (Γ₃ ⇒ φ₃) = sound-sr' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)
sound-sr (Γ₁ ⇒ φ₁) (Γ₂ ⇒ ¥ y)               (Γ₃ ⇒ φ₃) = sound-sr' (Γ₁ ⇒ φ₁) (Γ₂ ⇒ _) (Γ₃ ⇒ φ₃)

sound-pm : (a b c : Formula)
         → (∀ ξ → ⟦ ξ ⊧ andpl (πΓ a) => πφ a ⟧pl) → (∀ ξ → ⟦ ξ ⊧ andpl (πΓ b) => πφ b ⟧pl)
         → T (correct-pm a b c )
         → ∀ ξ → ⟦ ξ ⊧ andpl (πΓ c) => πφ c ⟧pl
sound-pm (Γ₁ ⇒ φ₁) (Γ₂ ⇒ φ₂) (Γ₃ ⇒ φ₃) pa pb p ξ [Γ₃]
  = lift-≡ᵇpl← φ₃ (const-removal (pm' φ₁ φ₂)) (∧-eliml (∧-elimr (conflict-negleft φ₁ φ₂) p))
    ξ (lem-no-const ξ (pm' φ₁ φ₂) (lem-pm φ₁ φ₂ (∧-eliml p) ξ (pa ξ (proj₁ (seq-split ξ Γ₁ Γ₂
      (lem-seq-subst-foldr ξ Γ₃ (Γ₁ ∪ Γ₂) (lift-⊆ (Γ₁ ∪ Γ₂) Γ₃ (∧-elimr (φ₃ ≡ᵇpl
      const-removal (pm' φ₁ φ₂)) (∧-elimr (conflict-negleft φ₁ φ₂) p))) [Γ₃])))) (pb ξ (proj₂
      (seq-split ξ Γ₁ Γ₂ (lem-seq-subst-foldr ξ Γ₃ (Γ₁ ∪ Γ₂) (lift-⊆ (Γ₁ ∪ Γ₂) Γ₃ (∧-elimr
      (φ₃ ≡ᵇpl const-removal (pm' φ₁ φ₂)) (∧-elimr (conflict-negleft φ₁ φ₂) p)))
      [Γ₃])))) ))

e-sound : (k : ERule)
       → (seq : Vec Formula (e-arity k))
       → (conc : Formula)
       → T (e-correct k seq conc)
       → Vec* (λ x → ∀ ξ → ⟦ ξ ⊧ x ⟧⇒) seq
       → ∀ ξ → ⟦ ξ ⊧ conc ⟧⇒
e-sound fof_nnf (Γ₁ ⇒ φ₁ ∷ _) (Γ₂ ⇒ φ₂) correct (v ∷ _) ξ
  = apply-Γ' ξ (Γ₂ ⇒ φ₂)
             (λ x → lift-≡ᵇpl← φ₂ (const-removal (mknnf φ₁)) (∧-eliml correct) ξ
               (lem-no-const ξ (mknnf φ₁) (lem-nnf← φ₁ ξ
                 (apply-Γ ξ (Γ₁ ⇒ φ₁) (v ξ)
                   (lem-seq-subst-foldr ξ Γ₂ Γ₁ (lift-⊆ Γ₁ Γ₂ (∧-elimr
                     (φ₂ ≡ᵇpl const-removal (mknnf φ₁)) correct)) x)))))
e-sound fof_simplification (Γ₁ ⇒ φ₁ ∷ _) (Γ₂ ⇒ φ₂) correct (v ∷ _) ξ
  = apply-Γ' ξ (Γ₂ ⇒ φ₂)
             (λ x → lift-≡ᵇpl← φ₂ (const-removal φ₁) (∧-eliml correct) ξ
               (lem-no-const ξ φ₁ (apply-Γ ξ (Γ₁ ⇒ φ₁) (v ξ)
                 (lem-seq-subst-foldr ξ Γ₂ Γ₁ (lift-⊆ Γ₁ Γ₂ (∧-elimr
                   (φ₂ ≡ᵇpl const-removal φ₁) correct)) x))))
e-sound distribute (Γ₁ ⇒ φ₁ ∷ _) (Γ₂ ⇒ φ₂) correct (v ∷ _) ξ
  = apply-Γ' ξ (Γ₂ ⇒ φ₂)
             (λ x → lift-≡ᵇpl← φ₂ (mkdist φ₁) (∧-eliml correct) ξ (lem-mkdist ξ φ₁
               (apply-Γ ξ (Γ₁ ⇒ φ₁) (v ξ) (lem-seq-subst-foldr ξ Γ₂ Γ₁
                 (lift-⊆ Γ₁ Γ₂ (∧-elimr (φ₂ ≡ᵇpl mkdist φ₁) correct)) x))))
e-sound split_conjunct (Γ₁ ⇒ φ₁ ∷ _) (Γ₂ ⇒ φ₂) correct (v ∷ _) ξ
  = apply-Γ' ξ (Γ₂ ⇒ φ₂) (λ x → lemSubConjunct ξ φ₂ φ₁ (∧-eliml correct)
     (apply-Γ ξ (Γ₁ ⇒ φ₁) (v ξ) (lem-seq-subst-foldr ξ Γ₂ Γ₁ (lift-⊆ Γ₁ Γ₂
       (∧-elimr (φ₂ isSubConjunct φ₁) correct)) x)))
e-sound cn (Γ₁ ⇒ φ₁ ∷ _) (Γ₂ ⇒ φ₂) correct (v ∷ _) ξ
  = apply-Γ' ξ (Γ₂ ⇒ φ₂) (λ x → lift-≡ᵇpl← φ₂ (const-removal φ₁) (∧-eliml correct) ξ
      (lem-no-const ξ φ₁ (apply-Γ ξ (Γ₁ ⇒ φ₁) (v ξ) (lem-seq-subst-foldr ξ Γ₂ Γ₁
        (lift-⊆ Γ₁ Γ₂ (∧-elimr (φ₂ ≡ᵇpl const-removal φ₁) correct)) x))))
e-sound axiom seq ([] ⇒ φ) () v ξ
e-sound axiom seq ((γ ∷ Γ) ⇒ φ) correct v ξ
  = apply-Γ' ξ ((γ ∷ Γ) ⇒ φ) (∨-elim (λ x → PropEq.subst (⟦_⊧_⟧pl ξ) (PropEq.sym (lift-≡pl φ _ x)) ∘ proj₁)
             (λ x x' → apply-Γ ξ (Γ ⇒ φ) (e-sound axiom seq (Γ ⇒ φ) x v ξ) (proj₂ x')) correct)
e-sound apply_def (a ∷ b ∷ _) c correct (v₁ ∷ v₂ ∷ _) ξ = sound-apply a b c v₁ v₂ correct ξ
e-sound rw (a ∷ b ∷ _) c correct (v₁ ∷ v₂ ∷ _) ξ
  = apply-Γ' ξ c (sound-rw a b c (λ ξ' → apply-Γ ξ' a (v₁ ξ'))
                                 (λ ξ' → apply-Γ ξ' b (v₂ ξ')) correct ξ)
e-sound sr (a ∷ b ∷ _) c correct (v₁ ∷ v₂ ∷ _) ξ
  = apply-Γ' ξ c (sound-sr a b c (λ ξ' → apply-Γ ξ' a (v₁ ξ'))
                                 (λ ξ' → apply-Γ ξ' b (v₂ ξ')) correct ξ)
e-sound pm (a ∷ b ∷ _) c correct (v₁ ∷ v₂ ∷ _) ξ
  = apply-Γ' ξ c (sound-pm a b c (λ ξ' → apply-Γ ξ' a (v₁ ξ'))
                                 (λ ξ' → apply-Γ ξ' b (v₂ ξ')) correct ξ)
e-sound unsat (Γ₁ ⇒ φ₁ ∷ _) (Γ₂ ⇒ φ₂) correct (v ∷ _) ξ
  = apply-Γ' ξ (Γ₂ ⇒ φ₂) λ x → stbl-pl ξ φ₂
      (λ x' → PropEq.subst id (PropEq.cong (⟦_⊧_⟧pl ξ) (lift-≡pl φ₁ _ (∧-eliml correct)))
                      (apply-Γ ξ (Γ₁ ⇒ φ₁) (v ξ)
                       (lem-seq-restrict-foldr' ξ Γ₁ (~ φ₂) x'
                        (lem-seq-subst-foldr ξ Γ₂ (Γ₁ ∣ ~ φ₂)
                         (lift-⊆ (Γ₁ ∣ ~ φ₂) Γ₂ (∧-elimr (φ₁ ≡pl ¥false) correct)) x))))
e-sound fresh (a ∷ _) b correct (v ∷ _) ξ
  = apply-Γ' ξ b (sound-fresh a b (λ ξ' → apply-Γ ξ' a (v ξ')) correct ξ)

E : RuleSystem ERule Formula Env ⟦_⊧_⟧⇒
E = record { arity = e-arity; correct = e-correct; sound = e-sound }

concE : ProofNode E → Formula
concE = conc {_} {_} {_} {_} {E}

correct-list'♭ : (l : ProofList E) → T (not (List.null l)) → Bool
correct-list'♭ l x = correct-list E l ∧ (List.null $ πΓ $ concE $ lastnode l x)

semantics-elist' : (l : ProofList E) → (x : T (not (List.null l))) → Set
semantics-elist' l x = ∀ ξ → ⟦ ξ ⊧ concE $ lastnode l x ⟧⇒

aux-reconst : (l : ProofList E) → (x : T (not (List.null l)))
            → (p : T (correct-list'♭ l x)) → semantics-elist' l x
aux-reconst l x p = sound-list E l x (∧-eliml p)

lemKK : ∀ ξ θ → ⟦ ξ ⊧ θ ⟧⇒ → T (List.null (πΓ θ)) → ⟦ ξ ⊧ πφ θ ⟧pl
lemKK ξ ([] ⇒ φ) p q = p
lemKK ξ ((x ∷ xs) ⇒ φ) p q = ⊥-elim q

correct-elist-φ♭ : (l : Maybe (ProofList E)) → (φ : PL-Formula) → Bool
correct-elist-φ♭ (just l) φ with ex-mid (not (List.null l))
...| inj₁ x = correct-list'♭ l x ∧ (φ ≡pl πφ (concE $ lastnode l x))
...| inj₂ x = false
correct-elist-φ♭ nothing φ = false

aux-reconstruct : ∀ φ l x → T (correct-list'♭ l x ∧ (φ ≡pl πφ (concE $ lastnode l x)))
                → Taut-pl φ
aux-reconstruct φ l x pτ ξ
  rewrite lift-≡pl φ _ (∧-elimr (correct-list'♭ l x) pτ)
  = lemKK ξ (concE $ lastnode l x) (aux-reconst l x (∧-eliml pτ) ξ)
          (∧-elimr (correct-list E l) (∧-eliml pτ))

reconstruct : ∀ φ l → T (correct-elist-φ♭ l φ) → Taut-pl φ
reconstruct φ nothing ()
reconstruct φ (just l) p with ex-mid (not (List.null l))
...| inj₁ x = aux-reconstruct φ l x p
...| inj₂ x = ⊥-elim p


----------------------------------------------------------------------------
-- private primitive primExternal : {A : Set} → String → String → Maybe A --
--                                                                        --
-- createList : PL-Formula → Maybe (ProofList E)                          --
-- createList φ = primExternal {ProofList E} "eprover-list" (tptp φ)      --
--                                                                        --
-- correctness : ∀ φ → Set                                                --
-- correctness φ = T (correct-elist-φ♭ (createList φ) φ)                  --
--                                                                        --
-- soundness : ∀ φ → correctness φ → Taut-pl φ                            --
-- soundness φ p = reconstruct φ (createList φ) p                         --
----------------------------------------------------------------------------
