module Kanso.Proof.List where

open import Algebra
open import Data.Bool as Bool using (Bool; true; false; T; not; _∧_; _∨_)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.List as List using (List; _∷_; []; [_]; _++_; length)
import Data.List.Properties as List using (++-assoc)
open import Data.Nat as Nat using (ℕ; suc; zero; _<ᵇ_)
open import Data.Product as Prod using (_×_; proj₁; proj₂; _,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Vec as Vec using (Vec; lookup; _∷_; [])
open import Data.Unit as Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)

open import Kanso.PropIso

data Vec* {A : Set} (F : A → Set) : {n : ℕ} → Vec A n → Set where
  []  : Vec* F []
  _∷_ : {n : ℕ} {a : A} {v : Vec A n} (x : F a) (xs : Vec* F v) → Vec* F (a ∷ v)

infixr 5 _∷_

data List* {A : Set} (F : A → Set) : List A → Set where
  [] : List* F []
  _∷_ : {a : A} {l : List A} (x : F a) (xs : List* F l) → List* F (a ∷ l)

_++*_ : {A : Set} → {F : A → Set} → {l1 l2 : List A} → List* F l1 → List* F l2 → List* F (l1 ++ l2)
[] ++* m = m
(x ∷ l₁) ++* m = x ∷ l₁ ++* m

_vlt_ : ∀ {n} → Vec ℕ n → ℕ → Bool
[] vlt _ = true
(n ∷ ns) vlt m = (n <ᵇ m) ∧ ns vlt m

lookup′ : {A : Set} → (l : List A) → (n : ℕ) → T (n <ᵇ length l) → A
lookup′ [] n ()
lookup′ (x ∷ l) zero p = x
lookup′ (x ∷ l) (suc n) p = lookup′ l n p

lookup* : ∀ {A l F} → List* {A} F l → (n : ℕ) → (p : T (n <ᵇ length l)) → F (lookup′ l n p)
lookup* [] n ()
lookup* (x ∷ l) zero p = x
lookup* (x ∷ l) (suc n) p = lookup* l n p

lastnode : {A : Set} → (l : List A) → T (not (List.null l)) → A
lastnode [] ()
lastnode (n ∷ []) p = n
lastnode (n ∷ x ∷ ns) p = lastnode (x ∷ ns) tt

lastnode* : ∀ {A l F} → List* {A} F l → (q : T (not (List.null l))) → F (lastnode l q)
lastnode* [] ()
lastnode* (n ∷ []) p = n
lastnode* (n ∷ x ∷ ns) p = lastnode* (x ∷ ns) tt

record RuleSystem (Δ Φ Ξ : Set) (⟦_⊧_⟧ : Ξ → Φ → Set) : Set₁ where
  field
    arity : Δ → ℕ
    correct : (k : Δ) → Vec Φ (arity k) → Φ → Bool
    sound : (k : Δ) → (seq : Vec Φ (arity k))
                    → (conc : Φ)
                    → T (correct k seq conc)
                    → Vec* (λ φ → ∀ ξ → ⟦ ξ ⊧ φ ⟧) seq
                    → ∀ ξ → ⟦ ξ ⊧ conc ⟧

  record ProofNode : Set where
    constructor
      node
    field
      rule : Δ
      conc : Φ
      seq : Vec ℕ (arity rule)

  open ProofNode public

  ProofList : Set
  ProofList = List ProofNode

  hypothesis : (l : ProofList) → ∀ {n} → (v : Vec ℕ n) → T (v vlt (length l)) → Vec ProofNode n
  hypothesis l [] p = []
  hypothesis l (x ∷ v) p = lookup′ l x (∧-eliml p) ∷ (hypothesis l v (∧-elimr (x <ᵇ length l) p))

  correct-rule : ProofList → ProofNode → Bool
  correct-rule l n with ex-mid (seq n vlt length l)
  ...| inj₁ x = correct (rule n) (Vec.map conc (hypothesis l (seq n) x)) (conc n)
  ...| inj₂ x = false

  correct-list' : ProofList → ProofList → Bool
  correct-list' done [] = true
  correct-list' done (n ∷ todo) = correct-rule done n ∧ correct-list' (done ++ [ n ]) todo

  ProvedList : (l : ProofList) → Set
  ProvedList = List* (\ n → ∀ ξ → ⟦ ξ ⊧ conc n ⟧)
  hypothesis' : (l : ProofList) → ∀ {n} → (seq : Vec ℕ n)
              → ProvedList l
              → (x : T (seq vlt (length l)))
              → Vec* (λ φ → ∀ ξ → ⟦ ξ ⊧ φ ⟧) (Vec.map conc (hypothesis l seq x))
  hypothesis' l [] p q = []
  hypothesis' l (x ∷ s) p q = (lookup* p x (∧-eliml q))
                                ∷ (hypothesis' l s p (∧-elimr (x <ᵇ length l) q))

  sound-rule : ∀ l n → (p : T (correct-rule l n)) → (q : ProvedList l) → ∀ ξ → ⟦ ξ ⊧ conc n ⟧
  sound-rule l n p q with ex-mid (seq n vlt List.foldr (λ _ → suc) 0 l)
  sound-rule l n p q | inj₁ x = sound (rule n) (Vec.map conc (hypothesis l (seq n) x))
                                      (conc n) p (hypothesis' l (seq n) q x)
  sound-rule l n p q | inj₂ y = ⊥-elim p

  sound-list' : (l1 : ProofList)
              → (l2 : ProofList)
              → (p : T (correct-list' l1 l2))
              → (q : ProvedList l1)
              → ProvedList (l1 ++ l2)
  sound-list' l1 [] p q = q ++* []
  sound-list' l1 (n ∷ l2) p q rewrite PropEq.sym (List.++-assoc l1 [ n ] l2)
    = sound-list' (l1 ++ [ n ]) l2 (∧-elimr (correct-rule l1 n) p)
                  (q ++* (sound-rule l1 n (∧-eliml p) q ∷ []))

  correct-list : (l : ProofList) → Bool
  correct-list l = correct-list' [] l

  sound-list : (l : ProofList)
             → (x : T (not (List.null l)))
             → (p : T (correct-list l))
             → ∀ ξ → ⟦ ξ ⊧ conc (lastnode l x) ⟧
  sound-list l x p = lastnode* (sound-list' [] l p []) x

open RuleSystem public
