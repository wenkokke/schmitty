--
-- Derived from https://github.com/ajrouvoet/ternary.agda/blob/master/src/Relation/Ternary/Construct/Sets/Union.agda
--
-- This module defines universe-polymorphic variants of the some defintions
-- from the module above. To make this development sel-contained only the
-- used definitions are ported

{-# OPTIONS --without-K --safe #-}

module Schmitty.Composable.Union where

open import Level using (Level; Lift; lift)
open import Data.Product using (_×_; _,_; proj₁; proj₂; curry)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Maybe using (Maybe; nothing; just)
open import Data.These using (These; this; that; these)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Function using (id; _$_; _∘_)
open import Schmitty.Composable.Signature using (Signature; _≼_; ⟦_⟧)

module _ where

  ∅ : ∀ {a ℓ} {A : Set a} → Pred A ℓ
  ∅ = λ _ → Lift _ ⊥

module _ where

  -- Eliminator for the `These` type
  ⟪_,_,_⟫ : ∀ {ℓ p} {A : Set ℓ} {B : Set ℓ}
            → (A → Set p)
            → (B → Set p)
            → (A × B → Set p)
            → These A B → Set p
  ⟪ P , Q , R ⟫ = Data.These.fold P Q (curry R)

  -- (potentially overlapping) unions on `Set`
  record Union {ℓ} (A : Set ℓ) (B : Set ℓ) (C : Set ℓ) : Set (Level.suc ℓ) where
    field inja : A → C
          injb : B → C
          from : C → These A B

          a-inv : {x : A} → ⟪ _≡ x , ∅    , (_≡ x) ∘ proj₁ ⟫ (from (inja x))
          b-inv : {y : B} → ⟪ ∅    , _≡ y , (_≡ y) ∘ proj₂ ⟫ (from (injb y))

          from-inv : {z : C} → ⟪ (_≡ z) ∘ inja
                               , (_≡ z) ∘ injb
                               , (λ (x , y) → inja x ≡ z × injb y ≡ z)
                               ⟫ (from z)

{- Some auxiliary functions that are helpful in dealing with `Union` -}
module _ {ℓ} {A B C : Set ℓ} (u : Union A B C) where

  open Union

  {- A useful view on the pattern `⟪_,_,_⟫ ∘ from`, that remembers
     some equations -}
  module _ (P : Pred A ℓ) (Q : Pred B ℓ) (R : Pred (A × B) ℓ) where

    data From⟨_,_,_⟩ c : Set ℓ where
      this    : ∀ a → (i : from u c ≡ this a) → (px : P a) → From⟨_,_,_⟩ c
      that    : ∀ b → (i : from u c ≡ that b) → (qx : Q b) → From⟨_,_,_⟩ c
      these : ∀ a b → (i : from u c ≡ these a b) → (rx : R (a , b)) → From⟨_,_,_⟩ c

  -- The result of `from ∘ inja` can only ever be `this` or `these`
  a-inv' : (a : A) → From⟨ (λ a' → a ≡ a') , (λ _ → Lift _ ⊥) , (λ (a' , _) → a ≡ a') ⟩ (inja u a)
  a-inv' a with from u (inja u a) | Eq.inspect (from u) (inja u a) | a-inv u {a}
  ... | this  a'   | Eq.[ eq ] | eq′ = this a' eq (Eq.sym $ eq′)
  ... | these a' b | Eq.[ eq ] | eq′ = these a' b eq (Eq.sym $ eq′)

  -- The result of `from ∘ injb` can only ever by `that` or `these`
  b-inv' : (b : B) → From⟨ (λ _ → Lift _ ⊥) , (λ b' → b ≡ b') , (λ (_ , b') → b ≡ b') ⟩ (injb u b)
  b-inv' b with from u (injb u b) | Eq.inspect (from u) (injb u b) | b-inv u {b}
  ... | that    b' | Eq.[ eq ] | eq′ = that b' eq (Eq.sym $ eq′)
  ... | these a b' | Eq.[ eq ] | eq′ = these a b' eq (Eq.sym $ eq′)

  -- Apply from to a value `c`, but include some equations that remember how the
  -- result of `from c` relates to `c`.
  from-inv' : (c : C) → From⟨ (λ a → c ≡ inja u a) , (λ b → c ≡ injb u b) , (λ (a , b) → c ≡ inja u a × c ≡ injb u b) ⟩ c
  from-inv' c with from u c | Eq.inspect (from u) c | from-inv u {c}
  ... | this  a   | Eq.[ eq ] | eq′ = this a eq (Eq.sym $ eq′)
  ... | that    b | Eq.[ eq ] | eq′ = that b eq (Eq.sym $ eq′)
  ... | these a b | Eq.[ eq ] | eq′₁ , eq′₂ = these a b eq ((Eq.sym $ eq′₁) , (Eq.sym $ eq′₂))

{- Trivial unions -}
module _ where

  -- Every type forms a union with itself --- i.e., the union where every value
  -- overlaps.
  union-copy : ∀ {a} {A : Set a} → Union A A A
  Union.inja  union-copy   = id
  Union.injb  union-copy   = id
  Union.from  union-copy x = these x x
  Union.a-inv union-copy   = Eq.refl
  Union.b-inv union-copy   = Eq.refl
  proj₁ (Union.from-inv union-copy) = Eq.refl
  proj₂ (Union.from-inv union-copy) = Eq.refl

  -- Disjoint union is always a valid union of any two types --- i.e., the union
  -- where none of the values overlap
  union-disjoint : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} → Union A B (A ⊎ B)
  Union.inja union-disjoint  = inj₁
  Union.injb union-disjoint  = inj₂
  Union.from union-disjoint  = [ this , that ]
  Union.a-inv union-disjoint = Eq.refl
  Union.b-inv union-disjoint = Eq.refl
  Union.from-inv union-disjoint {inj₁ x} = Eq.refl
  Union.from-inv union-disjoint {inj₂ y} = Eq.refl

{- Some properties about the relation between signature subtyping and `Union` -}
module _ where

  open _≼_
  open Union

  just≡ : ∀ {a} {A : Set a} {x x′ : A} → just x ≡ just x′ → x ≡ x′
  just≡ Eq.refl = Eq.refl

  nothing≠just : ∀ {a} {A : Set a} {x : A} → nothing ≡ just x → ⊥
  nothing≠just ()

  -- If there is a union between (the semantics of) signatures `σ₁`, `σ₂` and
  -- `σ`, then `σ₁` is a subsignature of `σ`.
  ∙-≼₁ : ∀ {ℓ} {σ₁ σ₂ σ : Signature ℓ} → ((X : Set ℓ) → Union (⟦ σ₁ ⟧ X) (⟦ σ₂ ⟧ X) (⟦ σ ⟧ X)) → σ₁ ≼ σ
  inj  (∙-≼₁ u) = inja (u _)
  proj (∙-≼₁ u) = Data.These.fold just (λ _ → nothing) (λ x _ → just x) ∘ from (u _)
  proj-inj (∙-≼₁ u) {x = x} with a-inv' (u _) x
  ... | this  a   i Eq.refl rewrite i = Eq.refl
  ... | these a b i Eq.refl rewrite i = Eq.refl
  inj-proj (∙-≼₁ u) {x = x} {y = y} eq with from-inv' (u _) y
  ... | this  a   i Eq.refl        rewrite i = Eq.cong (inja (u _)) (just≡ (Eq.sym eq))
  ... | that    b i Eq.refl        rewrite i = ⊥-elim (nothing≠just eq)
  ... | these a b i (Eq.refl , rx) rewrite i = Eq.cong (inja (u _)) (just≡ (Eq.sym eq))

  -- If there is a union between (the semantics of) signatures `σ₁`, `σ₂` and
  -- `σ`, then `σ₂` is a subsignature of `σ`.
  ∙-≼₂ : ∀ {ℓ} {σ₁ σ₂ σ : Signature ℓ} → ((X : Set ℓ) → Union (⟦ σ₁ ⟧ X) (⟦ σ₂ ⟧ X) (⟦ σ ⟧ X)) → σ₂ ≼ σ
  inj  (∙-≼₂ u) = injb (u _)
  proj (∙-≼₂ u) = Data.These.fold (λ _ → nothing) just (λ _ y → just y) ∘ from (u _)
  proj-inj (∙-≼₂ u) {x = x} with b-inv' (u _) x
  ... | that  b   i Eq.refl rewrite i = Eq.refl
  ... | these a b i Eq.refl rewrite i = Eq.refl
  inj-proj (∙-≼₂ u) {x = x} {y = y} eq with from-inv' (u _) y
  ... | this  a   i Eq.refl         rewrite i = ⊥-elim (nothing≠just eq)
  ... | that    b i Eq.refl         rewrite i = Eq.cong (injb (u _)) (just≡ (Eq.sym eq))
  ... | these a b i (Eq.refl , snd) rewrite i = Eq.trans (Eq.cong (injb (u _)) (just≡ (Eq.sym eq))) (Eq.sym snd)
