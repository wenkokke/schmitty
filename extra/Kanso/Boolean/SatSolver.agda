module Kanso.Boolean.SatSolver where

open import Data.Bool as Bool using (Bool; true; false; T) renaming (_∧_ to _∧ᵇ_; _∨_ to _∨ᵇ_)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Product as Prod using (Σ; _×_; proj₁; proj₂; _,_; uncurry)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit as Unit using (⊤; tt)
open import Function using (_$_; _∘_)

open import Kanso.PropIso renaming (_⟶_ to _⇒ᵇ_)
open import Kanso.Boolean.Formula

varbound : PL-Formula → ℕ
varbound ¥true     = 0
varbound ¥false    = 0
varbound (y || y') = max (varbound y) (varbound y')
varbound (y && y') = max (varbound y) (varbound y')
varbound (y => y') = max (varbound y) (varbound y')
varbound (¥ y)     = suc y

lem-varbound : ∀ φ → T (bound (varbound φ) φ)
lem-varbound ¥true  = tt
lem-varbound ¥false = tt
lem-varbound (y || y')
  = elim-max _ _ (λ k → T (bound k (y || y')))
      (λ p → ∧-intro _ _ (lem-varbound y) (injbound y' (varbound y') _ (<ᵇ-¬ _ (varbound y') p)
                                                       (lem-varbound y')))
      (λ p → ∧-intro _ _ (injbound y (varbound y) _ (<ᵇ-rsuc (varbound y) _ p) (lem-varbound y))
                         (lem-varbound y'))
lem-varbound (y && y')
  = elim-max _ _ (λ k → T (bound k (y && y')))
      (λ p → ∧-intro _ _ (lem-varbound y) (injbound y' (varbound y') _
                                                    (<ᵇ-¬ _ (varbound y') p) (lem-varbound y')))
      (λ p → ∧-intro _ _ (injbound y (varbound y) _ (<ᵇ-rsuc (varbound y) _ p) (lem-varbound y))
                         (lem-varbound y'))
lem-varbound (y => y')
  = elim-max _ _ (λ k → T (bound k (y => y')))
      (λ p → ∧-intro _ _ (lem-varbound y) (injbound y' (varbound y') _
                                                    (<ᵇ-¬ _ (varbound y') p) (lem-varbound y')))
      (λ p → ∧-intro _ _ (injbound y (varbound y) _ (<ᵇ-rsuc (varbound y) _ p) (lem-varbound y))
                         (lem-varbound y'))
lem-varbound (¥ y) = <ᵇ-ord y

Boolean : ℕ → Set -- formulae bounded by n variables
Boolean n = Σ PL-Formula (T ∘ bound n)

⟦_⊧_⟧b : ∀ {n} → Env → Boolean n → Set
⟦ ξ ⊧ φ ⟧b = ⟦ ξ ⊧ proj₁ φ ⟧pl

BooleanFormula : Set
BooleanFormula = Σ ℕ Boolean

mkbooleanformula : PL-Formula → BooleanFormula
mkbooleanformula φ = varbound φ , φ , lem-varbound φ

Taut : BooleanFormula → Set
Taut φ = ∀ ξ → ⟦ ξ ⊧ proj₂ φ ⟧b

{-# TERMINATING #-}
inst : ∀ {n} → Boolean n → Boolean (suc n) → Boolean n
inst b (¥true   , proj₂) = ¥true , proj₂
inst b (¥false  , proj₂) = ¥false , proj₂
inst b (y || y' , proj₂)
  = uncurry (λ x y0 → uncurry (λ x' y1 → x || x' , ∧-intro (bound _ x) _ y0 y1)
                                (inst b (y' , ∧-elimr (bound (suc _) y) proj₂)))
             (inst b (y , ∧-eliml proj₂))
inst b (y && y' , proj₂)
  =  uncurry (λ x y0 → uncurry (λ x' y1 → x && x' , ∧-intro (bound _ x) _ y0 y1)
                                 (inst b (y' , ∧-elimr (bound (suc _) y) proj₂)))
              (inst b (y , ∧-eliml proj₂))
inst b (y => y' , proj₂)
  =  uncurry (λ x y0 → uncurry (λ x' y1 → x => x' , ∧-intro (bound _ x) _ y0 y1)
                                 (inst b (y' , ∧-elimr (bound (suc _) y) proj₂)))
              (inst b (y , ∧-eliml proj₂))
inst b (¥ zero     , proj₂) = b
inst b (¥ (suc n') , proj₂) = (¥ n') , proj₂

abstract
  {-# TERMINATING #-}
  taut : BooleanFormula → Bool
  taut (zero  , ¥true   , p) = true
  taut (zero  , ¥false  , p) = false
  taut (zero  , y || y' , p) = taut (0 , y , ∧-eliml p) Bool.∨ taut (0 , y' , ∧-elimr (bound 0 y) p)
  taut (zero  , y && y' , p) = taut (0 , y , ∧-eliml p) Bool.∧ taut (0 , y' , ∧-elimr (bound 0 y) p)
  taut (zero  , y => y' , p) = taut (0 , y , ∧-eliml p) ⇒ᵇ taut (0 , y' , ∧-elimr (bound 0 y) p)
  taut (zero  , ¥ y     , ())
  taut (suc n , φ       , p)
    = uncurry (λ x y0 → uncurry (λ x' y1 → taut (n , x , y0) ∧ᵇ taut (n , x' , y1))
                                  (inst (¥true , tt) (φ , p)))
               (inst (¥false , tt) (φ , p))

const-pl : Bool → ∀ n → Boolean n
const-pl true n  = ¥true , tt
const-pl false n = ¥false , tt

mutual
  {-# TERMINATING #-}
  lem-inst : ∀ {n : ℕ} (φ : Boolean (suc n)) (ξ : Env) → ⟦ ξ ⊧ φ ⟧b
           → ⟦ ξ ∘ suc ⊧ inst (const-pl (ξ 0) n) φ ⟧b
  lem-inst (¥true   , b) ξ p = p
  lem-inst (¥false  , b) ξ p = p
  lem-inst (y || y' , b) ξ p = Sum.map  (lem-inst (y , ∧-eliml b) ξ)
                                        (lem-inst (y' , ∧-elimr (bound _ y) b) ξ) p
  lem-inst (y && y' , b) ξ p = Prod.map (lem-inst (y , ∧-eliml b) ξ)
                                        (lem-inst (y' , ∧-elimr (bound _ y) b) ξ) p
  lem-inst (y => y' , b) ξ p = lem-inst (y' , ∧-elimr (bound _ y) b) ξ ∘ p ∘
                                 lem-inst' (y , ∧-eliml b) ξ
  lem-inst (¥ zero  , b) ξ p with ξ 0
  ...| true = p
  ...| false = p
  lem-inst (¥ (suc n') , b) ξ p = p

  {-# TERMINATING #-}
  lem-inst' : ∀ {n : ℕ} (φ : Boolean (suc n)) (ξ : Env) → ⟦ ξ ∘ suc ⊧ inst (const-pl (ξ 0) n) φ ⟧b
            → ⟦ ξ ⊧ φ ⟧b
  lem-inst' (¥true   , b) ξ p = p
  lem-inst' (¥false  , b) ξ p = p
  lem-inst' (y || y' , b) ξ p = Sum.map  (lem-inst' (y , ∧-eliml b) ξ)
                                         (lem-inst' (y' , ∧-elimr (bound _ y) b) ξ) p
  lem-inst' (y && y' , b) ξ p = Prod.map (lem-inst' (y , ∧-eliml b) ξ)
                                         (lem-inst' (y' , ∧-elimr (bound _ y) b) ξ) p
  lem-inst' (y => y' , b) ξ p = lem-inst' (y' , ∧-elimr (bound _ y) b) ξ ∘ p ∘
                                  lem-inst (y , ∧-eliml b) ξ
  lem-inst' (¥ zero  , b) ξ p with ξ 0
  ...| true = p
  ...| false = p
  lem-inst' (¥ (suc n') , b) ξ p = p

{-# TERMINATING #-}
lem-ξ-zero : (φ : Boolean 0) → (ξ ζ : Env) → ⟦ ξ ⊧ φ ⟧b → ⟦ ζ ⊧ φ ⟧b
lem-ξ-zero (¥true   , b) ξ ζ p = p
lem-ξ-zero (¥false  , b) ξ ζ p = p
lem-ξ-zero (y || y' , b) ξ ζ p = Sum.map  (lem-ξ-zero (y , ∧-eliml b) ξ ζ)
                                          (lem-ξ-zero (y' , ∧-elimr (bound _ y) b) ξ ζ) p
lem-ξ-zero (y && y' , b) ξ ζ p = Prod.map (lem-ξ-zero (y , ∧-eliml b) ξ ζ)
                                          (lem-ξ-zero (y' , ∧-elimr (bound _ y) b) ξ ζ) p
lem-ξ-zero (y => y' , b) ξ ζ p = lem-ξ-zero (y' , ∧-elimr (bound _ y) b) ξ ζ ∘ p ∘
                                   lem-ξ-zero (y , ∧-eliml b) ζ ξ
lem-ξ-zero (¥ y     , b) ξ ζ p = ⊥-elim b

private
  trivenv : Env
  trivenv _ = true

mutual
  abstract
    {-# TERMINATING #-}
    sound : (φ : BooleanFormula) → T (taut φ) → Taut φ
    sound (zero , ¥true , b) p ξ   = p
    sound (zero , ¥false , b) p ξ  = p
    sound (zero , y || y' , b) p ξ = ∨-elim (λ x → inj₁ (sound (0 , y , _) x ξ))
                                            (λ x → inj₂ (sound (0 , y' , _) x ξ)) p
    sound (zero , y && y' , b) p ξ = ∧-elim (λ x x' → (sound (0 , y , _) x ξ) ,
                                                      (sound (0 , y' , _) x' ξ)) p
    sound (zero , y => y' , b) p ξ = λ x → sound (0 , y' , _) (lem-⟶-s (taut (0 , y , _)) _ p
                                                 (comp (0 , y , _)
                                                   (λ ξ' → lem-ξ-zero (y , ∧-eliml b) ξ ξ' x))) ξ
    sound (zero , ¥ y , b) p ξ     = ⊥-elim b
    sound (suc n , φ , b) p ξ      = lem-inst' (φ , b) ξ (sound (n , inst (const-pl (ξ 0) n)(φ , b))
                                                           (aux p) (λ _ → ξ(suc _)))
      where
        aux : T (taut (n , inst (¥false , tt) (φ , b)) ∧ᵇ taut (n , inst (¥true , tt) (φ , b)))
            → T (taut (n , inst (const-pl (ξ 0) n) (φ , b)))
        aux p with ξ 0
        ...| true  = ∧-elimr (taut (n , _ , _)) p
        ...| false = ∧-eliml p

    {-# TERMINATING #-}
    comp : (φ : BooleanFormula) → Taut φ → T (taut φ)
    comp (zero , ¥true   , b) p = tt
    comp (zero , ¥false  , b) p = p trivenv
    comp (zero , y || y' , b) p
      = lem-bool-∨-c (taut (0 , y , _)) _
                     (Sum.map (λ x → comp (0 , y , _)
                                          (λ ξ → lem-ξ-zero (y , ∧-eliml b) trivenv ξ x))
                              (λ x → comp (0 , y' , _)
                                          (λ ξ → lem-ξ-zero (y' , ∧-elimr(bound 0 y)b) trivenv ξ x))
                              (p trivenv))
    comp (zero , y && y' , b) p = ∧-intro (taut (0 , y , _)) _
                                          (comp (0 , y , _) (λ ξ → proj₁ (p ξ)))
                                          (comp (0 , y' , _) (λ ξ → proj₂ (p ξ)))
    comp (zero , y => y' , b) p = lem-⟶-c (taut (0 , y , _)) _
                                          (λ x → comp (0 , y' , _)
                                                 (λ ξ → p ξ (sound (0 , y , _) x ξ)))
    comp (zero , ¥ y , b) p     = ⊥-elim b
    comp (suc n , φ , b) p
      = ∧-intro (taut (n , inst (¥false , tt) (φ , b))) _
                (comp (n , inst (¥false , tt) (φ , b))
                      (λ ξ → lem-inst (φ , b) (extendξ ξ false) $ p $ extendξ ξ false))
                (comp (n , inst (¥true , tt) (φ , b))
                      (λ ξ → lem-inst (φ , b) (extendξ ξ true) $ p $ extendξ ξ true))
      where
       extendξ : Env → Bool → Env
       extendξ ξ b zero    = b
       extendξ ξ b (suc x) = ξ x

-----------------------------------------------------------
-- {- External Interface -}                              --
-- open import Boolean.CommonBinding                     --
-- open import Data.String                               --
--                                                       --
-- atptool : String                                      --
-- atptool = "z3"                                        --
--                                                       --
-- {-# BUILTIN ATPTOOL atptool #-}                       --
--                                                       --
-- decproc : PL-Formula → Bool                           --
-- decproc = taut ∘ mkbooleanformula                     --
--                                                       --
-- {-# BUILTIN ATPDECPROC decproc #-}                    --
--                                                       --
-- {-# BUILTIN ATPSEMANTICS Taut-pl #-}                  --
--                                                       --
-- sound' : (φ : PL-Formula) → T (decproc φ) → Taut-pl φ --
-- sound' = sound ∘ mkbooleanformula                     --
--                                                       --
-- {-# BUILTIN ATPSOUND sound' #-}                       --
--                                                       --
-- comp' :  (φ : PL-Formula) → Taut-pl φ → T (decproc φ) --
-- comp' = comp ∘ mkbooleanformula                       --
--                                                       --
-- {-# BUILTIN ATPCOMPLETE comp' #-}                     --
-----------------------------------------------------------
