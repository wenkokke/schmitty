module Kanso.Proof.EProver.PM where

open import Data.Bool as Bool using (Bool; true; false; T; _∧_; _∨_)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Product as Prod using (_×_; proj₁; proj₂; _,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit as Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

open import Kanso.PropIso
open import Kanso.Boolean.Formula

_isSubDisjunct_ : PL-Formula → PL-Formula → Bool
_isSubDisjunct_ φ ψ with φ ≡pl ψ
...| true = true
φ isSubDisjunct ¥true     | false = false
φ isSubDisjunct ¥false    | false = false
φ isSubDisjunct (y && y') | false = false
φ isSubDisjunct (y || y') | false = φ isSubDisjunct y ∨ φ isSubDisjunct y'
φ isSubDisjunct (y => y') | false = false
φ isSubDisjunct ¥ y       | false = false

subst-disjunct : (φ₁ φ₂ ψ : PL-Formula) → PL-Formula
subst-disjunct φ₁ φ₂ ψ with φ₁ ≡pl ψ
subst-disjunct φ₁ φ₂ ψ | true = φ₂
subst-disjunct φ₁ φ₂ (ψ₁ || ψ₂) | false = (subst-disjunct φ₁ φ₂ ψ₁) || (subst-disjunct φ₁ φ₂ ψ₂)
subst-disjunct φ₁ φ₂ ψ | false = ψ

conflict-negleft : PL-Formula → PL-Formula → Bool
conflict-negleft φ ¥true = ~ (¥true) isSubDisjunct φ
conflict-negleft φ ¥false = ~ (¥false) isSubDisjunct φ
conflict-negleft φ (ψ || ψ₁) = conflict-negleft φ ψ ∨ conflict-negleft φ ψ₁
conflict-negleft φ (ψ && ψ₁) = ~ (ψ && ψ₁) isSubDisjunct φ
conflict-negleft φ (ψ => ψ₁) = ~ (ψ => ψ₁) isSubDisjunct φ
conflict-negleft φ (¥ x) = ~ (¥ x) isSubDisjunct φ

-- assume conflict-negleft φ₁ φ₂ for pm'
pm' : (φ₁ φ₂ : PL-Formula)
    → PL-Formula
pm' φ₁ (φ₂ || φ₃) with conflict-negleft φ₁ φ₂
...| true  = (pm' φ₁ φ₂) || φ₃
...| false = (pm' φ₁ φ₃) || φ₂ -- this is implied by assumption
pm' φ₁ φ₂ = subst-disjunct (~ φ₂) ¥false φ₁

lem-subst-d : ∀ φ₁ φ₂ ψ ξ
            → ¬ T (φ₁ isSubDisjunct ψ)
            → ⟦ ξ ⊧ ψ ⟧pl
            → ⟦ ξ ⊧ subst-disjunct φ₁ φ₂ ψ ⟧pl
lem-subst-d φ₁ φ₂ ψ ξ p [ψ] with φ₁ ≡pl ψ
lem-subst-d φ₁ φ₂ ψ ξ p [ψ] | true = ⊥-elim (p tt)
lem-subst-d φ₁ φ₂ ¥true ξ p [ψ] | false = [ψ]
lem-subst-d φ₁ φ₂ ¥false ξ p [ψ] | false = [ψ]
lem-subst-d φ₁ φ₂ (ψ || ψ₁) ξ p [ψ] | false
  = Sum.map (lem-subst-d φ₁ φ₂ ψ ξ (λ x → p (∨-introl _ _ x)))
            (lem-subst-d φ₁ φ₂ ψ₁ ξ (λ x → p (∨-intror (φ₁ isSubDisjunct ψ) _ x))) [ψ]
lem-subst-d φ₁ φ₂ (ψ && ψ₁) ξ p [ψ] | false = [ψ]
lem-subst-d φ₁ φ₂ (ψ => ψ₁) ξ p [ψ] | false = [ψ]
lem-subst-d φ₁ φ₂ (¥ x) ξ p [ψ] | false = [ψ]

lem-pm : ∀ φ₁ φ₂
          → T (conflict-negleft φ₁ φ₂)
          → ∀ ξ
          → ⟦ ξ ⊧ φ₁ ⟧pl
          → ⟦ ξ ⊧ φ₂ ⟧pl
          → ⟦ ξ ⊧ pm' φ₁ φ₂ ⟧pl
lem-pm φ₁ ¥true p ξ [φ₁] [φ₂] with ex-mid ( (¥true => ¥false) ≡pl φ₁)
lem-pm φ₁ ¥true p ξ [φ₁] [φ₂] | inj₁ x rewrite Tb x
  = PropEq.subst (λ k → ⟦ ξ ⊧ k ⟧pl) (PropEq.sym (lift-≡pl (¥true => ¥false) φ₁ x)) [φ₁] [φ₂]
lem-pm ¥true ¥true () ξ [φ₁] [φ₂] | inj₂ y
lem-pm ¥false ¥true () ξ [φ₁] [φ₂] | inj₂ y
lem-pm (φ₁ || φ₂) ¥true p ξ [φ₁] [φ₂] | inj₂ y
  = [ (λ x → inj₁ ([ (λ xx → lem-pm φ₁ ¥true xx ξ x [φ₂]) ,
                     (λ xx → lem-subst-d (¥true => ¥false) ¥false φ₁ ξ xx x)
                  ]′ (ex-mid ((¥true => ¥false) isSubDisjunct φ₁)))) ,
      (λ x → inj₂ ([ (λ xx → lem-pm φ₂ ¥true xx ξ x [φ₂]) ,
                     (λ xx → lem-subst-d (¥true => ¥false) ¥false φ₂ ξ xx x)
                   ]′ (ex-mid ((¥true => ¥false) isSubDisjunct φ₂))))
    ]′ [φ₁]
lem-pm (φ₁ && φ₂) ¥true () ξ [φ₁] [φ₂] | inj₂ y
lem-pm (φ₁ => φ₂) ¥true p ξ [φ₁] [φ₂] | inj₂ y rewrite ¬Tb y = ⊥-elim p
lem-pm (¥ x) ¥true () ξ [φ₁] [φ₂] | inj₂ y

lem-pm φ₁ ¥false p ξ [φ₁] [φ₂] with ex-mid ( (¥false => ¥false) ≡pl φ₁)
lem-pm φ₁ ¥false p ξ [φ₁] [φ₂] | inj₁ x rewrite Tb x
  = PropEq.subst (λ k → ⟦ ξ ⊧ k ⟧pl) (PropEq.sym (lift-≡pl (¥false => ¥false) φ₁ x)) [φ₁] [φ₂]
lem-pm ¥true ¥false () ξ [φ₁] [φ₂] | inj₂ y
lem-pm ¥false ¥false () ξ [φ₁] [φ₂] | inj₂ y
lem-pm (φ₁ || φ₂) ¥false p ξ (inj₁ x) [φ₂] | inj₂ y
  with ex-mid ((¥false => ¥false) isSubDisjunct φ₁)
lem-pm (φ₁ || φ₂) ¥false p ξ (inj₁ x₁) [φ₂] | inj₂ y | inj₁ x
  = inj₁ (lem-pm φ₁ ¥false x ξ x₁ [φ₂])
lem-pm (φ₁ || φ₂) ¥false p ξ (inj₁ x) [φ₂] | inj₂ y₁ | inj₂ y
  = inj₁ (lem-subst-d (¥false => ¥false) ¥false φ₁ ξ y x)
lem-pm (φ₁ || φ₂) ¥false p ξ (inj₂ y₁) [φ₂] | inj₂ y
  with ex-mid ((¥false => ¥false) isSubDisjunct φ₂)
lem-pm (φ₁ || φ₂) ¥false p ξ (inj₂ y₁) [φ₂] | inj₂ y | inj₁ x
  = inj₂ (lem-pm φ₂ ¥false x ξ y₁ [φ₂])
lem-pm (φ₁ || φ₂) ¥false p ξ (inj₂ y₂) [φ₂] | inj₂ y₁ | inj₂ y
  = inj₂ (lem-subst-d (¥false => ¥false) ¥false φ₂ ξ y y₂)
lem-pm (φ₁ && φ₂) ¥false () ξ [φ₁] [φ₂] | inj₂ y
lem-pm (φ₁ => φ₂) ¥false p ξ [φ₁] [φ₂] | inj₂ y rewrite ¬Tb y = ⊥-elim p
lem-pm (¥ x) ¥false () ξ [φ₁] [φ₂] | inj₂ y

lem-pm φ₁ (φ₂ || φ₃) p ξ [φ₁] (inj₁ x) with ex-mid (conflict-negleft φ₁ φ₂)
lem-pm φ₁ (φ₂ || φ₃) p ξ [φ₁] (inj₁ x₁) | inj₁ x rewrite Tb x = inj₁ (lem-pm φ₁ φ₂ x ξ [φ₁] x₁)
lem-pm φ₁ (φ₂ || φ₃) p ξ [φ₁] (inj₁ x) | inj₂ y rewrite ¬Tb y = inj₂ x
lem-pm φ₁ (φ₂ || φ₃) p ξ [φ₁] (inj₂ y) with ex-mid (conflict-negleft φ₁ φ₂)
lem-pm φ₁ (φ₂ || φ₃) p ξ [φ₁] (inj₂ y) | inj₁ x rewrite Tb x = inj₂ y
lem-pm φ₁ (φ₂ || φ₃) p ξ [φ₁] (inj₂ y₁) | inj₂ y rewrite ¬Tb y = inj₁ (lem-pm φ₁ φ₃ p ξ [φ₁] y₁)

lem-pm φ₁ (φ₃ && φ₄) p ξ [φ₁] [φ₂] with ex-mid ( ((φ₃ && φ₄) => ¥false) ≡pl φ₁)
lem-pm φ₁ (φ₃ && φ₄) p ξ [φ₁] [φ₂] | inj₁ x rewrite Tb x
  = PropEq.subst (⟦_⊧_⟧pl ξ) (PropEq.sym (lift-≡pl ((φ₃ && φ₄) => ¥false) φ₁ x)) [φ₁] [φ₂]
lem-pm ¥true (φ₃ && φ₄) () ξ [φ₁] [φ₂] | inj₂ y
lem-pm ¥false (φ₃ && φ₄) () ξ [φ₁] [φ₂] | inj₂ y
lem-pm (φ₁ || φ₂) (φ₃ && φ₄) p ξ [φ₁] [φ₂] | inj₂ y
  = [ (λ x → inj₁ ([ (λ xx → lem-pm φ₁ (φ₃ && φ₄) xx ξ x [φ₂]) ,
                     (λ xx → lem-subst-d ((φ₃ && φ₄) => ¥false) ¥false φ₁ ξ xx x)
                   ]′ (ex-mid (((φ₃ && φ₄) => ¥false) isSubDisjunct φ₁)))) ,
      (λ x → inj₂ ([ (λ xx → lem-pm φ₂ (φ₃ && φ₄) xx ξ x [φ₂]) ,
                     (λ xx → lem-subst-d ((φ₃ && φ₄) => ¥false) ¥false φ₂ ξ xx x)
                   ]′ (ex-mid (((φ₃ && φ₄) => ¥false) isSubDisjunct φ₂))))
    ]′ ([φ₁])
lem-pm (φ₁ && φ₂) (φ₃ && φ₄) () ξ [φ₁] [φ₂] | inj₂ y
lem-pm (φ₁ => φ₂) (φ₃ && φ₄) p ξ [φ₁] [φ₂] | inj₂ y rewrite ¬Tb y = ⊥-elim p
lem-pm (¥ x) (φ₃ && φ₄) () ξ [φ₁] [φ₂] | inj₂ y

lem-pm φ₁ (φ₃ => φ₄) p ξ [φ₁] [φ₂] with ex-mid ( ((φ₃ => φ₄) => ¥false) ≡pl φ₁)
lem-pm φ₁ (φ₃ => φ₄) p ξ [φ₁] [φ₂] | inj₁ x rewrite Tb x
  = PropEq.subst (λ k → ⟦ ξ ⊧ k ⟧pl) (PropEq.sym (lift-≡pl ((φ₃ => φ₄) => ¥false) φ₁ x)) [φ₁] [φ₂]
lem-pm ¥true (φ₃ => φ₄) () ξ [φ₁] [φ₂] | inj₂ y
lem-pm ¥false (φ₃ => φ₄) () ξ [φ₁] [φ₂] | inj₂ y
lem-pm (φ₁ || φ₂) (φ₃ => φ₄) p ξ [φ₁] [φ₂] | inj₂ y
  = [ (λ x → inj₁ ([ (λ xx → lem-pm φ₁ (φ₃ => φ₄) xx ξ x [φ₂]) ,
                     (λ xx → lem-subst-d ((φ₃ => φ₄) => ¥false) ¥false φ₁ ξ xx x)
                   ]′ (ex-mid (((φ₃ => φ₄) => ¥false) isSubDisjunct φ₁)))) ,
      (λ x → inj₂ ([ (λ xx → lem-pm φ₂ (φ₃ => φ₄) xx ξ x [φ₂]) ,
                     (λ xx → lem-subst-d ((φ₃ => φ₄) => ¥false) ¥false φ₂ ξ xx x)
                   ]′ (ex-mid (((φ₃ => φ₄) => ¥false) isSubDisjunct φ₂)))) ]′ [φ₁]
lem-pm (φ₁ && φ₂) (φ₃ => φ₄) () ξ [φ₁] [φ₂] | inj₂ y
lem-pm (φ₁ => φ₂) (φ₃ => φ₄) p ξ [φ₁] [φ₂] | inj₂ y rewrite ¬Tb y = ⊥-elim p
lem-pm (¥ x) (φ₃ => φ₄) () ξ [φ₁] [φ₂] | inj₂ y

lem-pm φ₁ (¥ n) p ξ [φ₁] [φ₂] with ex-mid ( ((¥ n) => ¥false) ≡pl φ₁)
lem-pm φ₁ (¥ n) p ξ [φ₁] [φ₂] | inj₁ x rewrite Tb x
  = PropEq.subst (⟦_⊧_⟧pl ξ) (PropEq.sym (lift-≡pl ((¥ n) => ¥false) φ₁ x)) [φ₁] [φ₂]
lem-pm ¥true (¥ n) () ξ [φ₁] [φ₂] | inj₂ y
lem-pm ¥false (¥ n) () ξ [φ₁] [φ₂] | inj₂ y
lem-pm (φ₁ || φ₂) (¥ n) p ξ [φ₁] [φ₂] | inj₂ y
  = [ (λ x → inj₁ ([ (λ xx → lem-pm φ₁ (¥ n) xx ξ x [φ₂]) ,
                     (λ xx → lem-subst-d ((¥ n) => ¥false) ¥false φ₁ ξ xx x)
                  ]′ (ex-mid (((¥ n) => ¥false) isSubDisjunct φ₁)))) ,
      (λ x → inj₂ ([ (λ xx → lem-pm φ₂ (¥ n) xx ξ x [φ₂]) ,
                     (λ xx → lem-subst-d ((¥ n) => ¥false) ¥false φ₂ ξ xx x)
    ]′ (ex-mid (((¥ n) => ¥false) isSubDisjunct φ₂)))) ]′ ([φ₁])
lem-pm (φ₁ && φ₂) (¥ n) () ξ [φ₁] [φ₂] | inj₂ y
lem-pm (φ₁ => φ₂) (¥ n) p ξ [φ₁] [φ₂] | inj₂ y rewrite ¬Tb y = ⊥-elim p
lem-pm (¥ x) (¥ n) () ξ [φ₁] [φ₂] | inj₂ y
