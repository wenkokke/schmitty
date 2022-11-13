{-# OPTIONS --safe --without-K #-}

module Schmitty.Composable.Canon where

open import Level using (Level)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.These using (These; this; that)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Unary using (IUniversal; _⇒_; _⊢_)
open import Function using (_∘_ ; _$_ ; _↔_ ; Inverse)
open import Function.Construct.Identity using (id-↔)
open import Function.Construct.Composition using (_∘-↔_)
open import Schmitty.Composable.Signature
     using (Signature; Shape; Arity; map-sig; ⟦_⟧; μ; ⟨_⟩; _:+:_;
            Algebra; alg; cata; map-cata; para; map-para; _⊕_;
            _≼_; ≼-refl; ≼-trans; inject)
open import Schmitty.Composable.Union using (Union; ∙-≼₁; ∙-≼₂; union-copy)
open import Schmitty.Composable.Core using (Pred; Rel₂)


private
  variable
    ℓ ℓ′    : Level
    σ σ₁ σ₂ : Signature ℓ

{- Canonical forms -}
module _ where

  open import Relation.Unary.Closure.Base (_≼_ {ℓ = Level.zero})

  record Canon : Set₁ where
    constructor canon
    field
      ty : Signature _
      val : Algebra ty Set Set

module _ where

  record Values (Ix : Set ℓ → Set ℓ) (σ : Signature ℓ) : Set (Level.suc ℓ) where
    constructor mk
    field
      out : ∀ {T} → Algebra σ (T × Pred (Ix T)) (Pred (Ix T))

  open Values public

  fold : {Ix : Set → Set} → Values Ix σ → μ σ → Ix (μ σ) → Set
  fold V = para (out V)

  liftVal : ∀ {σ} {Ix} → Algebra σ Set Set → Values Ix σ
  alg (out (liftVal V)) x i = alg V (map-sig (λ (v , R) → R i) x)

  record ICanon (Ix : Set → Set) : Set₁ where
    constructor icanon
    field
      ity   : Signature _
      ival  : Values Ix ity

  liftCanon : ∀ {Ix} → Canon → ICanon Ix
  liftCanon (canon ty val) = icanon ty (liftVal val)

open Canon
open ICanon

{- A subvalue relation -}
module _ where

  open _≼_
  open Algebra

  -- Pointwise equivalence for predicates
  _⇔_ : ∀ {a ℓ} {A : Set a} → (A → Set ℓ) → (A → Set ℓ) → A → Set ℓ
  (P ⇔ Q) x = P x ↔ Q x

  -- A notion of subvalues for `Canon`.
  --
  -- A `σ₁`-indexed value `V` is a subvalue of a `σ₂`-indexed value `W`, iff:
  -- * `σ₁` is a subsignature of `σ₂`
  -- * For all syntactic types defined by `σ₁`, `V` and `W` agree on what the associated
  --   values should be (i.e., we have a proof that they will always calculate isomorphic
  --   Agda types for those syntactic types)
  --
  record _⊑ᵖ_ {σ₁ σ₂} (V : Algebra σ₁ Set Set) (W : Algebra σ₂ Set Set) : Set₁ where
    field
      ⦃ type-subᵖ ⦄ :
        σ₁ ≼ σ₂

      canonicalᵖ :
        ∀ {X} {R : X → Set} →
          ∀[ (alg V ∘ map-sig R) ⇔
             (alg W ∘ map-sig R ∘ inj type-subᵖ)
           ]

module _ {Ix : Set → Set} where

  open _≼_
  open Algebra

  -- A notion of subvalues for `ICanon`
  --
  -- This notion is entirely similar to the notion of subvalues for `Canon`, though
  -- the types change slightly due to the generalization to indexed value types.
  --
  record _⊑_ {σ₁ σ₂} (V : Values Ix σ₁) (W : Values Ix σ₂) : Set₁ where
    field
      ⦃ type-sub ⦄ :
        σ₁ ≼ σ₂

      canonical :
        ∀ {A} {t : ⟦ σ₁ ⟧ A} {R : A → Pred (Ix A)} →
          ∀[ alg (out V) (map-sig (λ x → x , R x) t ) ⇔
             alg (out W) (map-sig (λ x → x , R x) (inj type-sub t))
           ]



  ------------------------------------------------------------------------------
  --- _⊑ᵖ_ is a preorder

module _ where

  open _⊑ᵖ_

  ⊑ᵖ-refl : ∀ {V : Algebra σ Set Set} → V ⊑ᵖ V
  type-subᵖ  ⊑ᵖ-refl = ≼-refl
  canonicalᵖ ⊑ᵖ-refl = id-↔ _

  ⊑ᵖ-trans : ∀ {U : Algebra σ₁ Set Set}
               {V : Algebra σ₂ Set Set}
               {W : Algebra σ  Set Set}
             → U ⊑ᵖ V → V ⊑ᵖ W → U ⊑ᵖ W
  type-subᵖ  (⊑ᵖ-trans r₁ r₂) = ≼-trans (type-subᵖ r₁) (type-subᵖ r₂)
  canonicalᵖ (⊑ᵖ-trans r₁ r₂) = canonicalᵖ r₁ ∘-↔ canonicalᵖ r₂


  -- Register `Canon` for usage with `□` using `_⊑ᵖ_`
  instance canon-rel : Rel₂ _ Canon
  Rel₂.R     canon-rel c₁ c₂ = val c₁ ⊑ᵖ val c₂
  Rel₂.refl  canon-rel       = ⊑ᵖ-refl
  Rel₂.trans canon-rel       = ⊑ᵖ-trans

  ------------------------------------------------------------------------------
  --- _⊑_ is a preorder

module _ {Ix : Set → Set} where

  open _⊑_

  private
    variable
      U V W : Values Ix σ

  ⊑-refl : V ⊑ V
  type-sub   ⊑-refl = ≼-refl
  canonical  ⊑-refl = id-↔ _

  ⊑-trans : U ⊑ V → V ⊑ W → U ⊑ W
  type-sub  (⊑-trans r₁ r₂)         = ≼-trans (type-sub r₁) (type-sub r₂)
  canonical (⊑-trans r₁ r₂) {R = R} = canonical r₁ {R = R} ∘-↔ canonical r₂ {R = R}

  -- Register `ICanon` for usage with `□`, using `_⊑_`
  instance icanon-rel : Rel₂ _ (ICanon Ix)
  Rel₂.R     icanon-rel c₁ c₂ = ival c₁ ⊑ ival c₂
  Rel₂.refl  icanon-rel       = ⊑-refl
  Rel₂.trans icanon-rel       = ⊑-trans

{- Overlapping unions for indexed canons -}
module _ where

  open Union
  open _≼_
  open _⊑_

  -- Canon union
  --
  -- A canon `c` is a union of canons `c₁` and `c₂` iff:
  -- * The types in `c` are a union of the types in `c₁` and `c₂`
  -- * For all syntactic types defined by both `c₁` and `c`, the values in `c₁`
  --   and `c` agree on what the associated values should be
  -- * For all syntactic types defined by both `c₂` and `c`, the values in `c₂`
  --   and `c` agree on what the associated values should be
  --
  record _∙_≣ᵖ_ (c₁ c₂ c : Canon) : Set₁ where
    field
      type-unionᵖ :
        (X : Set) → Union (⟦ ty c₁ ⟧ X) (⟦ ty c₂ ⟧ X) (⟦ ty c ⟧ X)

      canonicalₗᵖ :
        ∀ {X} {R : X → Set} →
          ∀[ (alg (val c₁) ∘ map-sig R) ⇔
            (alg (val c ) ∘ map-sig R ∘ inj (∙-≼₁ type-unionᵖ))
          ]

      canonicalᵣᵖ :
        ∀ {X} {R : X → Set} →
          ∀[ (alg (val c₂) ∘ map-sig R) ⇔
             (alg (val c ) ∘ map-sig R ∘ inj (∙-≼₂ type-unionᵖ))
           ]


{- Overlapping unions for indexed canons -}
module _ {Ix : Set → Set} where

  open Union
  open _≼_
  open _⊑_

  -- Unions of indexed canons
  --
  -- Again, this definition is morally the same as the union type for plain canons as defined above,
  -- but here too we have to change some types here and there to account for the additional generality
  -- if indexed value types.
  --
  record _∙_≣_ (c₁ c₂ c : ICanon Ix) : Set₁ where
    field
      type-union :
        (X : Set) → Union (⟦ ity c₁ ⟧ X) (⟦ ity c₂ ⟧ X) (⟦ ity c ⟧ X)

      canonicalₗ :
        ∀ {A} {t : ⟦ ity c₁ ⟧ A} {R : A → Pred (Ix A)} →
          ∀[ alg (out (ival c₁)) (map-sig (λ x → x , R x) t ) ⇔
             alg (out (ival c )) (map-sig (λ x → x , R x) (inj (∙-≼₁ type-union) t))
           ]

      canonicalᵣ :
        ∀ {A} {t : ⟦ ity c₂ ⟧ A} {R : A → Pred (Ix A)} →
          ∀[ alg (out (ival c₂)) (map-sig (λ x → x , R x) t ) ⇔
             alg (out (ival c )) (map-sig (λ x → x , R x) (inj (∙-≼₂ type-union) t))
           ]

{- Trivial unions on non-indexed canons -}
module _ where

  open Union
  open _∙_≣ᵖ_

  ∙-copyᵖ : ∀ {c} → c ∙ c ≣ᵖ c
  type-unionᵖ ∙-copyᵖ _ = union-copy
  canonicalₗᵖ ∙-copyᵖ = id-↔ _
  canonicalᵣᵖ ∙-copyᵖ = id-↔ _

  union-sig-disjoint : ∀ {ℓ} {X : Set ℓ} → Union (⟦ σ₁ ⟧ X) (⟦ σ₂ ⟧ X) (⟦ σ₁ :+: σ₂ ⟧ X)
  inja     union-sig-disjoint (s , as)      = inj₁ s , as
  injb     union-sig-disjoint (s , as)      = inj₂ s , as
  from     union-sig-disjoint (inj₁ s , as) = this (s , as)
  from     union-sig-disjoint (inj₂ s , as) = that (s , as)
  a-inv    union-sig-disjoint               = Eq.refl
  b-inv    union-sig-disjoint               = Eq.refl
  from-inv union-sig-disjoint {inj₁ _ , _}  = Eq.refl
  from-inv union-sig-disjoint {inj₂ _ , _}  = Eq.refl

  ∙-disjointᵖ : ∀ {c₁ c₂} → c₁ ∙ c₂ ≣ᵖ canon _ (val c₁ ⊕ val c₂)
  type-unionᵖ ∙-disjointᵖ _ = union-sig-disjoint
  canonicalₗᵖ ∙-disjointᵖ   = id-↔ _
  canonicalᵣᵖ ∙-disjointᵖ   = id-↔ _

{- Trivial unions on indexed canons -}
module _ {Ix : Set → Set} where

  open Union
  open _∙_≣_

  private
    variable
      c c₁ c₂ c₃ : ICanon Ix

  -- Every canon forms a union with itself --- i.e., the union where all types
  -- and values are overlapping
  ∙-copy : c ∙ c ≣ c
  type-union ∙-copy _ = union-copy
  canonicalₗ ∙-copy   = id-↔ _
  canonicalᵣ ∙-copy   = id-↔ _

  -- For every two canons `c₁` and `c₂`, the canon that has as types the sum of
  -- the types in `c₁` and `c₂`, and as values a sum of the values in `c₁` and
  -- `c₂` is a valid union --- i.e., the union where not of the types and values
  -- are overlapping
  ∙-disjoint : c₁ ∙ c₂ ≣ icanon (ity c₁ :+: ity c₂) (mk (out (ival c₁) ⊕ out (ival c₂)))
  type-union ∙-disjoint _ = union-sig-disjoint
  canonicalₗ ∙-disjoint = id-↔ _
  canonicalᵣ ∙-disjoint = id-↔ _


{- Some properties about the relation between canon unions and value subtyping -}
module _ where

  open _∙_≣ᵖ_
  open _⊑ᵖ_

  -- If `c` is a union of the canons `c₁` and `c₂`, then the value type in `c₁`
  -- is a subtype of the values in `c`.
  ∙-⊑ᵖ₁ : ∀ {c₁ c₂ c} → c₁ ∙ c₂ ≣ᵖ c → val c₁ ⊑ᵖ val c
  type-subᵖ  (∙-⊑ᵖ₁ sep)          = ∙-≼₁ (type-unionᵖ sep)
  canonicalᵖ (∙-⊑ᵖ₁ sep) {R = R}  = canonicalₗᵖ sep {R = R}

  -- If `c` is a union of the canons `c₁` and `c₂`, then the value type in `c₂`
  -- is a subtype of the values in `c`
  ∙-⊑ᵖ₂ : ∀ {c₁ c₂ c} → c₁ ∙ c₂ ≣ᵖ c → val c₂ ⊑ᵖ val c
  type-subᵖ  (∙-⊑ᵖ₂ sep)         = ∙-≼₂ (type-unionᵖ sep)
  canonicalᵖ (∙-⊑ᵖ₂ sep) {R = R} = canonicalᵣᵖ sep {R = R}

{- Some properties about the relation between indexed canon unions and indexed value subtyping -}
module _ {Ix : Set → Set} where

  open _∙_≣_
  open _⊑_

  private
    variable
      c c₁ c₂ c₃ : ICanon Ix

  -- If `c` is a union of the canons `c₁` and `c₂`, then the value type in `c₁`
  -- is a subtype of the values in `c`.
  ∙-⊑₁ : c₁ ∙ c₂ ≣ c → ival c₁ ⊑ ival c
  type-sub  (∙-⊑₁ sep)          = ∙-≼₁ (type-union sep)
  canonical (∙-⊑₁ sep) {R = R}  = canonicalₗ sep {R = R}

  -- If `c` is a union of the canons `c₁` and `c₂`, then the value type in `c₂`
  -- is a subtype of the values in `c`
  ∙-⊑₂ : c₁ ∙ c₂ ≣ c → ival c₂ ⊑ ival c
  type-sub  (∙-⊑₂ sep)         = ∙-≼₂ (type-union sep)
  canonical (∙-⊑₂ sep) {R = R} = canonicalᵣ sep {R = R}

{- Up- and downcast of indexed value types using indexed value subtyping -}
module _ where

  open _≼_ ⦃...⦄
  open _⊑ᵖ_ ⦃...⦄
  open Inverse

  -- A lemma about the definition of `map-cata`, that proves that it behaves like
  -- `map` for Vectors
  map-cata-def : ∀ {V : Algebra σ Set Set} {n} (xs : Vec (μ σ) n)
                 → map-cata V xs ≡ Vec.map (cata V) xs
  map-cata-def []              = Eq.refl
  map-cata-def {V = V} (x ∷ v) = Eq.cong (_ ∷_) (map-cata-def {V = V} v)


  -- Value upcast using _⊑ᵖ_
  ↑ᵖ : ∀ {V : Algebra σ₁ Set Set} {W : Algebra σ Set Set} → ⦃ _ : V ⊑ᵖ W ⦄ → ∀ {t : ⟦ σ₁ ⟧ (μ σ)}
       → ∀[  alg V ∘ (map-sig (cata W))
          ⇒  cata W ∘ inject
          ]
  ↑ᵖ {W = W} x = Eq.subst (λ v → alg W (_ , Level.lift v))
                          (Eq.sym $ map-cata-def {V = W} _) (f canonicalᵖ x)

  -- Value downcast using _⊑_
  --
  -- NB: unlike the `proj` field in signature subtypes, this is a total
  -- function!
  -- This follows from the `canonical`, which field asserts that `W` does
  -- not add any new canonical forms for any syntactic type on which `V` is
  -- also defined.
  ↓ᵖ : ∀ {V : Algebra σ₁ Set Set} {W : Algebra σ Set Set} → ⦃ _ : V ⊑ᵖ W ⦄ → ∀ {t : ⟦ σ₁ ⟧ (μ σ)}
       → ∀[  cata W ∘ inject
          ⇒  alg V ∘ (map-sig (cata W))
          ]
  ↓ᵖ {W = W} x = f⁻¹ canonicalᵖ (Eq.subst (λ v → alg W (_ , Level.lift v))
                                (map-cata-def {V = W} _) x)

{- Up- and downcast of indexed value types using indexed value subtyping -}
module _ {Ix : Set → Set} {V : Values Ix σ₁} {W : Values Ix σ₂}  where

  open _≼_ ⦃...⦄
  open _⊑_ ⦃...⦄
  open Inverse

  -- A lemma about the definition of `map-para`, that proves that it behaves like
  -- `map` for Vectors
  map-para-def : ∀ {V : Values Ix σ} {n} (xs : Vec (μ σ) n)
                 → Vec.zip xs (map-para (out V) xs) ≡ Vec.map (λ v → v , para (out V) v) xs
  map-para-def []              = Eq.refl
  map-para-def {V = V} (x ∷ v) = Eq.cong (_ ∷_) (map-para-def {V = V} v)


  -- Value upcast using _⊑_
  ↑ : ∀ ⦃ _ : V ⊑ W ⦄
      → ∀ {t} → ∀[  alg (out V) (map-sig (λ x → x , para (out W) x) t)
                 ⇒  para (out W) (inject t)
                 ]
  ↑ x = Eq.subst (λ v → alg (out W) (_ , Level.lift v) _)
                 (Eq.sym $ map-para-def {V = W} _) (f canonical x)


  -- Value downcast using _⊑_
  --
  -- NB: unlike the `proj` field in signature subtypes, this is a total
  -- function!
  -- This follows from the `canonical`, which field asserts that `W` does
  -- not add any new canonical forms for any syntactic type on which `V` is
  -- also defined.
  ↓ : ⦃ _ : V ⊑ W ⦄
      → ∀ {t} → ∀[  para (out W) (inject t)
                 ⇒  alg (out V) (map-sig (λ x → x , para (out W) x) t)
                 ]
  ↓ x = f⁻¹ canonical (Eq.subst (λ v → alg (out W) (_ , Level.lift v) _)
                                (map-para-def {V = W} _) x)
