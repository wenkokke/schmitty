module Kanso.Boolean.Formula where

open import Data.Bool using (T; Bool; false; true; _∧_; _∨_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; []; _++_; length; foldr)
open import Data.List.Properties using (++-assoc)
open import Data.Nat using (ℕ; suc; zero; pred; _+_; _≡ᵇ_; _<ᵇ_)
open import Data.Product as Prod using (_×_; proj₁; proj₂; _,_; curry)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Function using (id; _∘_; _$_; const)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

open import Kanso.PropIso

infixr 8 _&&_
infixr 7 _||_

data PL-Formula : Set where
  ¥true ¥false : PL-Formula
  _||_ _&&_ _=>_ : PL-Formula → PL-Formula → PL-Formula
  ¥ : ℕ → PL-Formula

~ : PL-Formula → PL-Formula
~ φ = φ => ¥false

_<ᵇ=>_ : PL-Formula → PL-Formula → PL-Formula
φ <ᵇ=> ψ = (φ => ψ) && (ψ => φ)

Env : Set
Env = ℕ → Bool

⟦_⊧_⟧pl : (ξ : Env) → PL-Formula → Set
⟦ ξ ⊧ ¥true ⟧pl = ⊤
⟦ ξ ⊧ ¥false ⟧pl = ⊥
⟦ ξ ⊧ φ || ψ ⟧pl = ⟦ ξ ⊧ φ ⟧pl ⊎ ⟦ ξ ⊧ ψ ⟧pl
⟦ ξ ⊧ φ && ψ ⟧pl = ⟦ ξ ⊧ φ ⟧pl × ⟦ ξ ⊧ ψ ⟧pl
⟦ ξ ⊧ φ => ψ ⟧pl = ⟦ ξ ⊧ φ ⟧pl → ⟦ ξ ⊧ ψ ⟧pl
⟦ ξ ⊧ ¥ v ⟧pl = T (ξ v)

Taut-pl : PL-Formula → Set
Taut-pl φ = ∀ ξ → ⟦ ξ ⊧ φ ⟧pl

elim-pl : {A : Set} → (t f : A) → (v : ℕ → A) → (or and iff : A → A → A) → PL-Formula → A
elim-pl t f v or and iff ¥true     = t
elim-pl t f v or and iff ¥false    = f
elim-pl t f v or and iff (y || y') = or (elim-pl t f v or and iff y) (elim-pl t f v or and iff y')
elim-pl t f v or and iff (y && y') = and (elim-pl t f v or and iff y) (elim-pl t f v or and iff y')
elim-pl t f v or and iff (y => y') = iff (elim-pl t f v or and iff y) (elim-pl t f v or and iff y')
elim-pl t f v or and iff (¥ y)     = v y

_≡pl_ : PL-Formula → PL-Formula → Bool
¥true     ≡pl ¥true     = true
¥true     ≡pl _         = false
¥false    ≡pl ¥false    = true
¥false    ≡pl _         = false
(y || y') ≡pl (z || z') = y ≡pl z ∧ y' ≡pl z'
(y || y') ≡pl _         = false
(y && y') ≡pl (z && z') = y ≡pl z ∧ y' ≡pl z'
(y && y') ≡pl _         = false
(y => y') ≡pl (z => z') = y ≡pl z ∧ y' ≡pl z'
(y => y') ≡pl _         = false
¥ y       ≡pl ¥ z       = y ≡ᵇ z
¥ y       ≡pl _         = false

lift-≡pl : ∀ φ ψ → T (φ ≡pl ψ) → φ ≡ ψ
lift-≡pl ¥true     ¥true p       = refl
lift-≡pl ¥true     ¥false    ()
lift-≡pl ¥true     (y || y') ()
lift-≡pl ¥true     (y && y') ()
lift-≡pl ¥true     (y => y') ()
lift-≡pl ¥true     (¥ y)     ()
lift-≡pl ¥false    ¥true     ()
lift-≡pl ¥false    ¥false p      = refl
lift-≡pl ¥false    (y || y') ()
lift-≡pl ¥false    (y && y') ()
lift-≡pl ¥false    (y => y') ()
lift-≡pl ¥false    (¥ y)     ()
lift-≡pl (y || y') ¥true     ()
lift-≡pl (y || y') ¥false    ()
lift-≡pl (y || y') (y0 || y1) p rewrite lift-≡pl y y0 $ proj₁ $ lem-bool-∧-s (y ≡pl y0) _ p
                                      | lift-≡pl y' y1 $ proj₂ $ lem-bool-∧-s (y ≡pl y0) _ p = refl
lift-≡pl (y || y') (y0 && y1) ()
lift-≡pl (y || y') (y0 => y1) ()
lift-≡pl (y || y') (¥ y0)     ()
lift-≡pl (y && y') ¥true      ()
lift-≡pl (y && y') ¥false     ()
lift-≡pl (y && y') (y0 || y1) ()
lift-≡pl (y && y') (y0 && y1) p rewrite lift-≡pl y y0 $ proj₁ $ lem-bool-∧-s (y ≡pl y0) _ p
                                      | lift-≡pl y' y1 $ proj₂ $ lem-bool-∧-s (y ≡pl y0) _ p = refl
lift-≡pl (y && y') (y0 => y1) ()
lift-≡pl (y && y') (¥ y0)     ()
lift-≡pl (y => y') ¥true      ()
lift-≡pl (y => y') ¥false     ()
lift-≡pl (y => y') (y0 || y1) ()
lift-≡pl (y => y') (y0 && y1) ()
lift-≡pl (y => y') (y0 => y1) p rewrite lift-≡pl y y0 $ proj₁ $ lem-bool-∧-s (y ≡pl y0) _ p
                                      | lift-≡pl y' y1 $ proj₂ $ lem-bool-∧-s (y ≡pl y0) _ p = refl
lift-≡pl (y => y') (¥ y0)     ()
lift-≡pl (¥ y)     ¥true      ()
lift-≡pl (¥ y)     ¥false     ()
lift-≡pl (¥ y)     (y' || y0) ()
lift-≡pl (¥ y)     (y' && y0) ()
lift-≡pl (¥ y)     (y' => y0) ()
lift-≡pl (¥ y)     (¥ y') p      = cong ¥ (lift-≡ᵇ y y' p)

id-≡pl : ∀ φ → T (φ ≡pl φ)
id-≡pl ¥true     = tt
id-≡pl ¥false    = tt
id-≡pl (y || y') = lem-bool-∧-c (y ≡pl y) _ ((id-≡pl y) , (id-≡pl y'))
id-≡pl (y && y') = lem-bool-∧-c (y ≡pl y) _ (id-≡pl y , id-≡pl y')
id-≡pl (y => y') = lem-bool-∧-c (y ≡pl y) _ (id-≡pl y , id-≡pl y')
id-≡pl (¥ y)     = id-≡ᵇ y

lower-≡pl : ∀ φ ψ → φ ≡ ψ → T (φ ≡pl ψ)
lower-≡pl φ ._ refl = id-≡pl φ

_isSubFormula_ : PL-Formula → PL-Formula → Bool
_isSubFormula_ φ ψ with φ ≡pl ψ
...| true = true
φ isSubFormula ¥true     | false = false
φ isSubFormula ¥false    | false = false
φ isSubFormula (y || y') | false = φ isSubFormula y ∨ φ isSubFormula y'
φ isSubFormula (y && y') | false = φ isSubFormula y ∨ φ isSubFormula y'
φ isSubFormula (y => y') | false = φ isSubFormula y ∨ φ isSubFormula y'
φ isSubFormula ¥ y       | false = false

id-isSubFormula : ∀ φ → T (φ isSubFormula φ)
id-isSubFormula φ rewrite Tb (id-≡pl φ) = tt

envupdate : Env → ℕ → Bool → Env
envupdate ξ n b n' with n ≡ᵇ n'
...| true  = b
...| false = ξ n'

lem-envupdate : ∀ ξ n b → envupdate ξ n b n ≡ b
lem-envupdate ξ n b rewrite Tb (id-≡ᵇ n) = refl

eval-pl : Env → PL-Formula → Bool
eval-pl ξ ¥true     = true
eval-pl ξ ¥false    = false
eval-pl ξ (y || y') = eval-pl ξ y ∨ eval-pl ξ y'
eval-pl ξ (y && y') = eval-pl ξ y ∧ eval-pl ξ y'
eval-pl ξ (y => y') = not (eval-pl ξ y) ∨ eval-pl ξ y'
eval-pl ξ (¥ y)     = ξ y

mutual
  lem-eval : ∀ ξ φ → ⟦ ξ ⊧ φ ⟧pl → T (eval-pl ξ φ)
  lem-eval ξ ¥true     = id
  lem-eval ξ ¥false    = id
  lem-eval ξ (y || y') = [ ∨-introl (eval-pl ξ y) _ ∘ lem-eval ξ y ,
                           ∨-intror (eval-pl ξ y) _ ∘ lem-eval ξ y' ]′
  lem-eval ξ (y && y') = lem-bool-∧-c (eval-pl ξ y) _ ∘ Prod.map (lem-eval ξ y) (lem-eval ξ y')
  lem-eval ξ (y => y') = λ p → lem-→-elim (eval-pl ξ y) _ (lem-eval ξ y' ∘ p ∘ lem-eval' ξ y)
  lem-eval ξ (¥ y)     = id

  lem-eval' : ∀ ξ φ → T (eval-pl ξ φ) → ⟦ ξ ⊧ φ ⟧pl
  lem-eval' ξ ¥true     = id
  lem-eval' ξ ¥false    = id
  lem-eval' ξ (y || y') = ∨-elim (inj₁ ∘ lem-eval' ξ y) (inj₂ ∘ lem-eval' ξ y')
  lem-eval' ξ (y && y') = ∧-elim (curry $ Prod.map (lem-eval' ξ y) (lem-eval' ξ y'))
  lem-eval' ξ (y => y') = (λ p → lem-eval' ξ y' ∘ p ∘ lem-eval ξ y) ∘ lem-→-intro (eval-pl ξ y) _
  lem-eval' ξ (¥ y)     = id

exmid-or : {A : Set} → {B : Set} → (A ⊎ ¬ A) × (B ⊎ ¬ B) → (A ⊎ B) ⊎ ¬ (A ⊎ B)
exmid-or (inj₁ x , y)       = inj₁ (inj₁ x)
exmid-or (inj₂ y , inj₁ x)  = inj₁ (inj₂ x)
exmid-or (inj₂ y , inj₂ y') = inj₂ [ y , y' ]′

exmid-and : {A : Set} → {B : Set} → (A ⊎ ¬ A) × (B ⊎ ¬ B) → (A × B) ⊎ ¬ (A × B)
exmid-and (inj₁ x , inj₁ x') = inj₁ (x , x')
exmid-and (inj₁ x , inj₂ y)  = inj₂ (y ∘ proj₂)
exmid-and (inj₂ y , x)       = inj₂ (y ∘ proj₁)

exmid-fun : {A B : Set} → (A ⊎ ¬ A) × (B ⊎ ¬ B) → (A → B) ⊎ ¬ (A → B)
exmid-fun (a , inj₁ x) = inj₁ (const x)
exmid-fun (inj₁ x , inj₂ y)  = inj₂ (λ x' → y (x' x))
exmid-fun (inj₂ y , inj₂ y') = inj₁ (⊥-elim ∘ y)

ex-mid-pl : (ξ : Env) → (φ : PL-Formula) → ⟦ ξ ⊧ φ || ~ φ ⟧pl
ex-mid-pl ξ ¥true    = inj₁ tt
ex-mid-pl ξ ¥false   = inj₂ id
ex-mid-pl ξ (φ || ψ) = exmid-or  (ex-mid-pl ξ φ , ex-mid-pl ξ ψ)
ex-mid-pl ξ (φ && ψ) = exmid-and (ex-mid-pl ξ φ , ex-mid-pl ξ ψ)
ex-mid-pl ξ (φ => ψ) = exmid-fun (ex-mid-pl ξ φ , ex-mid-pl ξ ψ)
ex-mid-pl ξ (¥ v)    = ex-mid (ξ v)

stbl-pl : (ξ : Env) → (φ : PL-Formula) → ⟦ ξ ⊧ ~ (~ φ) ⟧pl → ⟦ ξ ⊧ φ ⟧pl
stbl-pl ξ φ p = [ id , ⊥-elim ∘ p ]′ (ex-mid-pl ξ φ)

demorg : ∀ ξ φ ψ → ⟦ ξ ⊧ ~ (φ && ψ) ⟧pl → ⟦ ξ ⊧ ~ φ || ~ ψ ⟧pl
demorg ξ φ ψ p = stbl-pl ξ (~ φ || ~ ψ) (λ x → p $ stbl-pl ξ φ (x ∘ inj₁) , stbl-pl ξ ψ (x ∘ inj₂))

material-pl : ∀ ξ φ ψ → ⟦ ξ ⊧ φ => ψ ⟧pl → ⟦ ξ ⊧ ~ φ || ψ ⟧pl
material-pl ξ φ ψ f = [ inj₂ ∘ f , inj₁ ]′ (ex-mid-pl ξ φ)

material-¬pl : ∀ ξ φ ψ → ⟦ ξ ⊧ ~ (φ => ψ) ⟧pl → ⟦ ξ ⊧ φ && (~ ψ) ⟧pl
material-¬pl ξ φ ψ p = [ ⊥-elim ∘ p ∘ const ,
                         _,_ $ [ id , ⊥-elim ∘ p ∘ (λ ~φ → ⊥-elim ∘ ~φ) ]′ (ex-mid-pl ξ φ)
                       ]′ (ex-mid-pl ξ ψ)

mkenv : List Bool → Env
mkenv []       n       = false
mkenv (x ∷ xs) 0       = x
mkenv (x ∷ xs) (suc n) = mkenv xs n

lem-mkenv-++-eq : ∀ ξ ξ' ζ n → ξ ++ ζ ≡ ξ' → T (n <ᵇ length ξ) → mkenv ξ n ≡ mkenv ξ' n
lem-mkenv-++-eq []      ξ'            ζ n       eq   n<ᵇξ = ⊥-elim n<ᵇξ
lem-mkenv-++-eq (x ∷ ξ) .(x ∷ ξ ++ ζ) ζ zero    refl n<ᵇξ = refl
lem-mkenv-++-eq (x ∷ ξ) .(x ∷ ξ ++ ζ) ζ (suc n) refl n<ᵇξ = lem-mkenv-++-eq ξ _ ζ n refl n<ᵇξ

lem-mkenv-++ : ∀ ξ ζ n → T (n <ᵇ length ξ) → T (mkenv ξ n) → T (mkenv (ξ ++ ζ) n)
lem-mkenv-++ []      ζ n       () q
lem-mkenv-++ (x ∷ ξ) ζ zero    p  q = q
lem-mkenv-++ (x ∷ ξ) ζ (suc n) p  q = lem-mkenv-++ ξ ζ n p q

lem-mkenv-++' : ∀ ξ ζ n → T (n <ᵇ length ξ) → T (mkenv (ξ ++ ζ) n) → T (mkenv ξ n)
lem-mkenv-++' []      ζ n       () q
lem-mkenv-++' (x ∷ ξ) ζ zero    p  q = q
lem-mkenv-++' (x ∷ ξ) ζ (suc n) p  q = lem-mkenv-++' ξ ζ n p q

bound : ℕ → PL-Formula → Bool
bound n ¥true     = true
bound n ¥false    = true
bound n (y || y') = bound n y ∧ bound n y'
bound n (y && y') = bound n y ∧ bound n y'
bound n (y => y') = bound n y ∧ bound n y'
bound n (¥ y)     = y <ᵇ n

injbound : ∀ φ n m → T (n <ᵇ suc m) → T (bound n φ) → T (bound m φ)
injbound ¥true     n m n<ᵇm p = tt
injbound ¥false    n m n<ᵇm p = tt
injbound (y || y') n m n<ᵇm p = f∧g {a = bound n y} (injbound y n m n<ᵇm) (injbound y' n m n<ᵇm) p
injbound (y && y') n m n<ᵇm p = f∧g {a = bound n y} (injbound y n m n<ᵇm) (injbound y' n m n<ᵇm) p
injbound (y => y') n m n<ᵇm p = f∧g {a = bound n y} (injbound y n m n<ᵇm) (injbound y' n m n<ᵇm) p
injbound (¥ y)     n m n<ᵇm p = <ᵇ-trans (suc y) n m p n<ᵇm

env-subst : ∀ ξ₁ ξ₂ φ → (∀ n → ξ₁ n ≡ ξ₂ n) → ⟦ ξ₁ ⊧ φ ⟧pl → ⟦ ξ₂ ⊧ φ ⟧pl
env-subst ξ₁ ξ₂ ¥true    ext = id
env-subst ξ₁ ξ₂ ¥false   ext = id
env-subst ξ₁ ξ₂ (φ || ψ) ext = Sum.map (env-subst ξ₁ ξ₂ φ ext) (env-subst ξ₁ ξ₂ ψ ext)
env-subst ξ₁ ξ₂ (φ && ψ) ext = Prod.map (env-subst ξ₁ ξ₂ φ ext) (env-subst ξ₁ ξ₂ ψ ext)
env-subst ξ₁ ξ₂ (φ => ψ) ext = λ x → env-subst ξ₁ ξ₂ ψ ext ∘ x ∘ env-subst ξ₂ ξ₁ φ (sym ∘ ext)
env-subst ξ₁ ξ₂ (¥ v)    ext rewrite ext v = id

env-eq-guard : ∀ ξ₁ ξ₂ φ → (∀ n → T (¥ n isSubFormula φ) → ξ₁ n ≡ ξ₂ n)
             → ⟦ ξ₁ ⊧ φ ⟧pl ≡ ⟦ ξ₂ ⊧ φ ⟧pl
env-eq-guard ξ₁ ξ₂ ¥true ext  = refl
env-eq-guard ξ₁ ξ₂ ¥false ext = refl
env-eq-guard ξ₁ ξ₂ (φ || ψ) ext
  = cong₂ _⊎_ (env-eq-guard ξ₁ ξ₂ φ (λ n x → ext n (∨-introl _ _ x)))
              (env-eq-guard ξ₁ ξ₂ ψ (λ n x → ext n (∨-intror (¥ n isSubFormula φ) _ x)))
env-eq-guard ξ₁ ξ₂ (φ && ψ) ext
  = cong₂ _×_ (env-eq-guard ξ₁ ξ₂ φ (λ n x → ext n (∨-introl _ _ x)))
              (env-eq-guard ξ₁ ξ₂ ψ (λ n x → ext n (∨-intror (¥ n isSubFormula φ) _ x)))
env-eq-guard ξ₁ ξ₂ (φ => ψ) ext
  = cong₂ (\ a b → a → b) (env-eq-guard ξ₁ ξ₂ φ (λ n x → ext n (∨-introl _ _ x)))
                          (env-eq-guard ξ₁ ξ₂ ψ (λ n x → ext n (∨-intror (¥ n isSubFormula φ) _ x)))
env-eq-guard ξ₁ ξ₂ (¥ v) ext rewrite ext v (id-isSubFormula (¥ v)) = refl

env-subst-guard : ∀ ξ₁ ξ₂ φ → (∀ n → T (¥ n isSubFormula φ) → ξ₁ n ≡ ξ₂ n)
                → ⟦ ξ₁ ⊧ φ ⟧pl → ⟦ ξ₂ ⊧ φ ⟧pl
env-subst-guard ξ₁ ξ₂ ¥true ext = id
env-subst-guard ξ₁ ξ₂ ¥false ext = id
env-subst-guard ξ₁ ξ₂ (φ || ψ) ext
  = Sum.map (env-subst-guard ξ₁ ξ₂ φ (λ n x → ext n (∨-introl _ _ x)))
            (env-subst-guard ξ₁ ξ₂ ψ (λ n x → ext n (∨-intror (¥ n isSubFormula φ) _ x)))
env-subst-guard ξ₁ ξ₂ (φ && ψ) ext
  = Prod.map (env-subst-guard ξ₁ ξ₂ φ (λ n x → ext n (∨-introl _ _ x)))
             (env-subst-guard ξ₁ ξ₂ ψ (λ n x → ext n (∨-intror (¥ n isSubFormula φ) _ x)))
env-subst-guard ξ₁ ξ₂ (φ => ψ) ext
  = λ x → env-subst-guard ξ₁ ξ₂ ψ (λ n x' → ext n (∨-intror (¥ n isSubFormula φ) _ x')) ∘
             x ∘ env-subst-guard ξ₂ ξ₁ φ (λ n x' → sym (ext n (∨-introl _ _ x')))
env-subst-guard ξ₁ ξ₂ (¥ v) ext rewrite ext v (id-isSubFormula (¥ v)) = id

subform-¥-elim : ∀ k y → T (¥ (suc k) isSubFormula ¥ (suc y)) → T (¥ k isSubFormula ¥ y)
subform-¥-elim k y p with k ≡ᵇ y
...| true = tt
...| false = p

lem-mkenv-++-pl-eq : ∀ φ ξ ζ → T (bound (length ξ) φ) → ∀ k → T (¥ k isSubFormula φ)
                   → mkenv ξ k ≡ mkenv (ξ ++ ζ) k
lem-mkenv-++-pl-eq ¥true ξ ζ b k kinφ = ⊥-elim kinφ
lem-mkenv-++-pl-eq ¥false ξ ζ b k kinφ = ⊥-elim kinφ
lem-mkenv-++-pl-eq (y || y') ξ ζ b k kinφ
  = ∨-elim (lem-mkenv-++-pl-eq y ξ ζ (∧-eliml b) k)
                   (lem-mkenv-++-pl-eq y' ξ ζ (∧-elimr (bound (length ξ) y) b) k) kinφ
lem-mkenv-++-pl-eq (y && y') ξ ζ b k kinφ
  = ∨-elim (lem-mkenv-++-pl-eq y ξ ζ (∧-eliml b) k)
                   (lem-mkenv-++-pl-eq y' ξ ζ (∧-elimr (bound (length ξ) y) b) k) kinφ
lem-mkenv-++-pl-eq (y => y') ξ ζ b k kinφ
  = ∨-elim (lem-mkenv-++-pl-eq y ξ ζ (∧-eliml b) k)
                   (lem-mkenv-++-pl-eq y' ξ ζ (∧-elimr (bound (length ξ) y) b) k) kinφ
lem-mkenv-++-pl-eq (¥ y) [] ζ b k kinφ = ⊥-elim b
lem-mkenv-++-pl-eq (¥ y) (x ∷ ξ) ζ b zero kinφ = refl
lem-mkenv-++-pl-eq (¥ zero) (x ∷ ξ) ζ b (suc k) kinφ = ⊥-elim kinφ
lem-mkenv-++-pl-eq (¥ (suc y)) (x ∷ ξ) ζ b (suc k) kinφ
  = lem-mkenv-++-pl-eq (¥ y) ξ ζ b k (subform-¥-elim k y kinφ)

lem-mkenv-++-pl-eq' : ∀ φ ξ ξ' ζ → ξ' ≡ ξ ++ ζ → T (bound (length ξ) φ) → ∀ k
                    → T (¥ k isSubFormula φ) → mkenv ξ k ≡ mkenv ξ' k
lem-mkenv-++-pl-eq' ¥true ξ ξ' ζ eq b k kinφ = ⊥-elim kinφ
lem-mkenv-++-pl-eq' ¥false ξ ξ' ζ eq b k kinφ = ⊥-elim kinφ
lem-mkenv-++-pl-eq' (y || y') ξ ξ' ζ ξ≡ξ' b k kinφ
  = ∨-elim (lem-mkenv-++-pl-eq' y ξ ξ' ζ ξ≡ξ' (∧-eliml b) k)
           (lem-mkenv-++-pl-eq' y' ξ ξ' ζ ξ≡ξ' (∧-elimr (bound (length ξ) y) b) k) kinφ
lem-mkenv-++-pl-eq' (y && y') ξ ξ' ζ ξ≡ξ' b k kinφ
  = ∨-elim (lem-mkenv-++-pl-eq' y ξ ξ' ζ ξ≡ξ' (∧-eliml b) k)
           (lem-mkenv-++-pl-eq' y' ξ ξ' ζ ξ≡ξ' (∧-elimr (bound (length ξ) y) b) k) kinφ
lem-mkenv-++-pl-eq' (y => y') ξ ξ' ζ ξ≡ξ' b k kinφ
  = ∨-elim (lem-mkenv-++-pl-eq' y ξ ξ' ζ ξ≡ξ' (∧-eliml b) k)
           (lem-mkenv-++-pl-eq' y' ξ ξ' ζ ξ≡ξ' (∧-elimr (bound (length ξ) y) b) k) kinφ
lem-mkenv-++-pl-eq' (¥ y) [] ξ' ζ ξ≡ξ' b k kinφ = ⊥-elim b
lem-mkenv-++-pl-eq' (¥ y) (x ∷ ξ) ._ ζ refl b zero kinφ = refl
lem-mkenv-++-pl-eq' (¥ zero) (x ∷ ξ) ξ' ζ ξ≡ξ' b (suc k) kinφ = ⊥-elim kinφ
lem-mkenv-++-pl-eq' (¥ (suc y)) (x ∷ ξ) ._ ζ refl b (suc k) kinφ
  = lem-mkenv-++-pl-eq' (¥ y) ξ _ ζ refl b k (subform-¥-elim k y kinφ)

lem-mkenv-++-pl : ∀ φ ξ ζ → T (bound (length ξ) φ) → ⟦ mkenv ξ ⊧ φ ⟧pl → ⟦ mkenv (ξ ++ ζ) ⊧ φ ⟧pl
lem-mkenv-++-pl φ ξ ζ b = env-subst-guard (mkenv ξ) (mkenv (ξ ++ ζ)) φ (lem-mkenv-++-pl-eq φ ξ ζ b)

lem-mkenv-++-pl' : ∀ φ ξ ζ → T (bound (length ξ) φ) → ⟦ mkenv (ξ ++ ζ) ⊧ φ ⟧pl → ⟦ mkenv ξ ⊧ φ ⟧pl
lem-mkenv-++-pl' φ ξ ζ b = env-subst-guard (mkenv (ξ ++ ζ)) (mkenv ξ) φ
                                           (λ k p → sym (lem-mkenv-++-pl-eq φ ξ ζ b k p))

lem-length : {a : Set} → (l m : List a) → length l + length m ≡ length (l ++ m)
lem-length [] m = refl
lem-length (x ∷ l) m = cong suc (lem-length l m)

lem-length² : {a : Set} → (l m n : List a) → length l + length m + length n ≡ length (l ++ m ++ n)
lem-length² [] m n = lem-length m n
lem-length² (x ∷ l) m n = cong suc (lem-length² l m n)

lem-mkenv-++-pl-eq² : ∀ φ ξ₁ ξ₂ ζ → T (bound (length ξ₁ + length ξ₂) φ) → ∀ k →
  T (¥ k isSubFormula φ) → mkenv (ξ₁ ++ ξ₂) k ≡ mkenv (ξ₁ ++ ξ₂ ++ ζ) k
lem-mkenv-++-pl-eq² φ ξ₁ ξ₂ ζ rewrite lem-length ξ₁ ξ₂
  = lem-mkenv-++-pl-eq' φ (ξ₁ ++ ξ₂) (ξ₁ ++ ξ₂ ++ ζ) ζ (sym (++-assoc ξ₁ ξ₂ ζ))

lem-mkenv-++-pl² : ∀ φ ξ₁ ξ₂ ζ → T (bound (length ξ₁ + length ξ₂) φ)
                → ⟦ mkenv (ξ₁ ++ ξ₂) ⊧ φ ⟧pl → ⟦ mkenv (ξ₁ ++ ξ₂ ++ ζ) ⊧ φ ⟧pl
lem-mkenv-++-pl² φ ξ₁ ξ₂ ζ b
  = env-subst-guard (mkenv (ξ₁ ++ ξ₂)) (mkenv (ξ₁ ++ ξ₂ ++ ζ)) φ (lem-mkenv-++-pl-eq² φ ξ₁ ξ₂ ζ b)

lem-mkenv-++-pl²' : ∀ φ ξ₁ ξ₂ ζ → T (bound (length ξ₁ + length ξ₂) φ)
                → ⟦ mkenv (ξ₁ ++ ξ₂ ++ ζ) ⊧ φ ⟧pl → ⟦ mkenv (ξ₁ ++ ξ₂) ⊧ φ ⟧pl
lem-mkenv-++-pl²' φ ξ₁ ξ₂ ζ b
  = env-subst-guard (mkenv (ξ₁ ++ ξ₂ ++ ζ)) (mkenv (ξ₁ ++ ξ₂)) φ
                    (\ k p → sym (lem-mkenv-++-pl-eq² φ ξ₁ ξ₂ ζ b k p))

lem-mkenv-++-pl-eq³ : ∀ φ ξ₁ ξ₂ ξ₃ ζ
                    → T (bound (length ξ₁ + length ξ₂ + length ξ₃) φ)
                    → (n : ℕ) → _ → mkenv (ξ₁ ++ ξ₂ ++ ξ₃) n ≡ mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ζ) n
lem-mkenv-++-pl-eq³ φ ξ₁ ξ₂ ξ₃ ζ b rewrite lem-length ξ₁ ξ₂
                                         | sym (++-assoc  ξ₁ ξ₂ ξ₃)
                                         | sym (++-assoc  ξ₁ ξ₂ (ξ₃ ++ ζ))
  = lem-mkenv-++-pl-eq² φ (ξ₁ ++ ξ₂) ξ₃ ζ b

lem-mkenv-++-pl³ : ∀ φ ξ₁ ξ₂ ξ₃ ζ → T (bound (length ξ₁ + length ξ₂ + length ξ₃) φ)
                 → ⟦ mkenv (ξ₁ ++ ξ₂ ++ ξ₃) ⊧ φ ⟧pl → ⟦ mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ζ) ⊧ φ ⟧pl
lem-mkenv-++-pl³ φ ξ₁ ξ₂ ξ₃ ζ p
  = env-subst-guard (mkenv (ξ₁ ++ ξ₂ ++ ξ₃)) (mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ζ)) φ
                    (lem-mkenv-++-pl-eq³ φ ξ₁ ξ₂ ξ₃ ζ p)

lem-mkenv-++-pl³' : ∀ φ ξ₁ ξ₂ ξ₃ ζ → T (bound (length ξ₁ + length ξ₂ + length ξ₃) φ)
                  → ⟦ mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ζ) ⊧ φ ⟧pl → ⟦ mkenv (ξ₁ ++ ξ₂ ++ ξ₃) ⊧ φ ⟧pl
lem-mkenv-++-pl³' φ ξ₁ ξ₂ ξ₃ ζ p
  = env-subst-guard (mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ζ)) (mkenv (ξ₁ ++ ξ₂ ++ ξ₃)) φ
                    (\ a b → sym (lem-mkenv-++-pl-eq³ φ ξ₁ ξ₂ ξ₃ ζ p a b))

lem-mkenv-++-pl-eq⁴ : ∀ φ ξ₁ ξ₂ ξ₃ ξ₄ ζ
                    → T (bound (length ξ₁ + length ξ₂ + length ξ₃ + length ξ₄) φ)
                    → ∀ n → _
                    → mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ξ₄) n ≡ mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ξ₄ ++ ζ) n
lem-mkenv-++-pl-eq⁴ φ ξ₁ ξ₂ ξ₃ ξ₄ ζ b rewrite lem-length ξ₁ ξ₂
                                         | sym (++-assoc ξ₁ ξ₂ (ξ₃ ++ ξ₄))
                                         | sym (++-assoc ξ₁ ξ₂ (ξ₃ ++ ξ₄ ++ ζ))
 = lem-mkenv-++-pl-eq³ φ (ξ₁ ++ ξ₂) ξ₃ ξ₄ ζ b

lem-mkenv-++-pl⁴ : ∀ φ ξ₁ ξ₂ ξ₃ ξ₄ ζ → T (bound (length ξ₁ + length ξ₂ + length ξ₃ + length ξ₄) φ)
                 → ⟦ mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ξ₄) ⊧ φ ⟧pl
                 → ⟦ mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ξ₄ ++ ζ) ⊧ φ ⟧pl
lem-mkenv-++-pl⁴ φ ξ₁ ξ₂ ξ₃ ξ₄ ζ p
  = env-subst-guard (mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ξ₄)) (mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ξ₄ ++ ζ)) φ
                    (lem-mkenv-++-pl-eq⁴ φ ξ₁ ξ₂ ξ₃ ξ₄ ζ p)

lem-mkenv-++-pl⁴' : ∀ φ ξ₁ ξ₂ ξ₃ ξ₄ ζ
                  → T (bound (length ξ₁ + length ξ₂ + length ξ₃ + length ξ₄) φ)
                  → ⟦ mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ξ₄ ++ ζ) ⊧ φ ⟧pl
                  → ⟦ mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ξ₄) ⊧ φ ⟧pl
lem-mkenv-++-pl⁴' φ ξ₁ ξ₂ ξ₃ ξ₄ ζ p
  = env-subst-guard (mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ξ₄ ++ ζ)) (mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ξ₄)) φ
                    (\ a b → sym (lem-mkenv-++-pl-eq⁴ φ ξ₁ ξ₂ ξ₃ ξ₄ ζ p a b))

extendenv : ∀ ξ ξ' ζ → (P : ℕ → Set) → length ξ ≡ length ξ' → (∀ k → P k → mkenv ξ k ≡ mkenv ξ' k)
          → ∀ j → P j → mkenv (ξ ++ ζ) j ≡ mkenv (ξ' ++ ζ) j
extendenv [] [] ζ P lp ∀k j pj = refl
extendenv [] (x' ∷ ξ') ζ P () ∀k j pj
extendenv (x ∷ ξ) [] ζ P () ∀k j pj
extendenv (x ∷ ξ) (x' ∷ ξ') ζ P lp ∀k zero pj = ∀k 0 pj
extendenv (x ∷ ξ) (x' ∷ ξ') ζ P lp ∀k (suc n) pj = extendenv ξ ξ' ζ (P ∘ suc)
                                                             (cong pred lp) (∀k ∘ suc) n pj

shiftpl : PL-Formula → ℕ → PL-Formula
shiftpl φ n = elim-pl ¥true ¥false (¥ ∘ (_+_ n)) _||_ _&&_ _=>_ φ

mutual
  lem-shift1-pl : ∀ m b φ ξ → ⟦ mkenv ξ ⊧ shiftpl φ m ⟧pl → ⟦ mkenv (b ∷ ξ) ⊧ shiftpl φ (suc m) ⟧pl
  lem-shift1-pl m b ¥true ξ     = id
  lem-shift1-pl m b ¥false ξ    = id
  lem-shift1-pl m b (y || y') ξ = Sum.map  (lem-shift1-pl m b y ξ) (lem-shift1-pl m b y' ξ)
  lem-shift1-pl m b (y && y') ξ = Prod.map (lem-shift1-pl m b y ξ) (lem-shift1-pl m b y' ξ)
  lem-shift1-pl m b (y => y') ξ = \ x → (lem-shift1-pl m b y' ξ) ∘ x ∘ (lem-shift1-pl' m b y ξ)
  lem-shift1-pl m b (¥ y) ξ     = id

  lem-shift1-pl' : ∀ m b φ ξ → ⟦ mkenv (b ∷ ξ) ⊧ shiftpl φ (suc m) ⟧pl → ⟦ mkenv ξ ⊧ shiftpl φ m ⟧pl
  lem-shift1-pl' m b ¥true ξ     = id
  lem-shift1-pl' m b ¥false ξ    = id
  lem-shift1-pl' m b (y || y') ξ = Sum.map  (lem-shift1-pl' m b y ξ) (lem-shift1-pl' m b y' ξ)
  lem-shift1-pl' m b (y && y') ξ = Prod.map (lem-shift1-pl' m b y ξ) (lem-shift1-pl' m b y' ξ)
  lem-shift1-pl' m b (y => y') ξ = \ x → (lem-shift1-pl' m b y' ξ) ∘ x ∘ (lem-shift1-pl m b y ξ)
  lem-shift1-pl' m b (¥ y) ξ     = id

id-elim-pl : ∀ φ → elim-pl ¥true ¥false ¥ _||_ _&&_ _=>_ φ ≡ φ
id-elim-pl ¥true     = refl
id-elim-pl ¥false    = refl
id-elim-pl (y || y') = cong₂ _||_ (id-elim-pl y) (id-elim-pl y')
id-elim-pl (y && y') = cong₂ _&&_ (id-elim-pl y) (id-elim-pl y')
id-elim-pl (y => y') = cong₂ _=>_ (id-elim-pl y) (id-elim-pl y')
id-elim-pl (¥ y)     = refl

lem-shift-pl : (φ : PL-Formula) → ∀ ξ ζ → ⟦ mkenv ζ ⊧ φ ⟧pl
             → ⟦ mkenv (ξ ++ ζ) ⊧ shiftpl φ (length ξ) ⟧pl
lem-shift-pl φ [] ζ p rewrite id-elim-pl φ = p
lem-shift-pl φ (x ∷ ξ) ζ p = lem-shift1-pl (length ξ) x φ (ξ ++ ζ) (lem-shift-pl φ ξ ζ p)

lem-shift-pl' : (φ : PL-Formula) → ∀ ξ ζ → ⟦ mkenv (ξ ++ ζ) ⊧ shiftpl φ (length ξ) ⟧pl
              → ⟦ mkenv ζ ⊧ φ ⟧pl
lem-shift-pl' φ [] ζ p rewrite (id-elim-pl φ) = p
lem-shift-pl' φ (x ∷ ξ) ζ p = lem-shift-pl' φ ξ ζ (lem-shift1-pl' (length ξ) x φ (ξ ++ ζ) p)

lem-shift-pl² : (φ : PL-Formula) → (ξ₁ ξ₂ ξ₃ : List Bool) → ⟦ mkenv ξ₃ ⊧ φ ⟧pl
              → ⟦ mkenv (ξ₁ ++ ξ₂ ++ ξ₃) ⊧ shiftpl φ (length ξ₁ + length ξ₂) ⟧pl
lem-shift-pl² φ [] ξ₂ ξ₃ p = lem-shift-pl φ ξ₂ ξ₃ p
lem-shift-pl² φ (x ∷ ξ₁) ξ₂ ξ₃ p = lem-shift1-pl (length ξ₁ + length ξ₂) x φ (ξ₁ ++ ξ₂ ++ ξ₃)
                                                 (lem-shift-pl² φ ξ₁ ξ₂ ξ₃ p)

lem-shift-pl²' : (φ : PL-Formula) → (ξ₁ ξ₂ ξ₃ : List Bool)
               → ⟦ mkenv (ξ₁ ++ ξ₂ ++ ξ₃) ⊧ shiftpl φ (length ξ₁ + length ξ₂) ⟧pl
               → ⟦ mkenv ξ₃ ⊧ φ ⟧pl
lem-shift-pl²' φ [] ξ₂ ξ₃ p = lem-shift-pl' φ ξ₂ ξ₃ p
lem-shift-pl²' φ (x ∷ ξ₁) ξ₂ ξ₃ p
  = lem-shift-pl²' φ ξ₁ ξ₂ ξ₃ (lem-shift1-pl' (length ξ₁ + length ξ₂) x φ (ξ₁ ++ ξ₂ ++ ξ₃) p)

lem-shift-pl³ : (φ : PL-Formula)
              → (ξ₁ ξ₂ ξ₃ ξ₄ : List Bool)
              → ⟦ mkenv ξ₄ ⊧ φ ⟧pl
              → ⟦ mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ξ₄) ⊧ shiftpl φ (length ξ₁ + length ξ₂ + length ξ₃) ⟧pl
lem-shift-pl³ φ [] ξ₂ ξ₃ ξ₄ p = lem-shift-pl² φ ξ₂ ξ₃ ξ₄ p
lem-shift-pl³ φ (x ∷ ξ₁) ξ₂ ξ₃ ξ₄ p = lem-shift1-pl (length ξ₁ + length ξ₂ + length ξ₃)
                                                    x φ (ξ₁ ++ ξ₂ ++ ξ₃ ++ ξ₄)
                                                    (lem-shift-pl³ φ ξ₁ ξ₂ ξ₃ ξ₄ p)

lem-shift-pl³' : (φ : PL-Formula) → (ξ₁ ξ₂ ξ₃ ξ₄ : List Bool)
               → ⟦ mkenv (ξ₁ ++ ξ₂ ++ ξ₃ ++ ξ₄) ⊧ shiftpl φ (length ξ₁ + length ξ₂ + length ξ₃)⟧pl
               → ⟦ mkenv ξ₄ ⊧ φ ⟧pl
lem-shift-pl³' φ [] ξ₂ ξ₃ ξ₄ p = lem-shift-pl²' φ ξ₂ ξ₃ ξ₄ p
lem-shift-pl³' φ (x ∷ ξ₁) ξ₂ ξ₃ ξ₄ p
  = lem-shift-pl³' φ ξ₁ ξ₂ ξ₃ ξ₄ (lem-shift1-pl' (length ξ₁ + length ξ₂ + length ξ₃)
                                                 x φ (ξ₁ ++ ξ₂ ++ ξ₃ ++ ξ₄) p)

lem-bound : ∀ φ n k → T (bound n φ) → T (¥ k isSubFormula φ) → T (k <ᵇ n)
lem-bound ¥true     n k bn sub = ⊥-elim sub
lem-bound ¥false    n k bn sub = ⊥-elim sub
lem-bound (y || y') n k bn sub = ∨-elim (lem-bound y n k (∧-eliml bn))
                                        (lem-bound y' n k (∧-elimr (bound n y) bn)) sub
lem-bound (y && y') n k bn sub = ∨-elim (lem-bound y n k (∧-eliml bn))
                                        (lem-bound y' n k (∧-elimr (bound n y) bn)) sub
lem-bound (y => y') n k bn sub = ∨-elim (lem-bound y n k (∧-eliml bn))
                                        (lem-bound y' n k (∧-elimr (bound n y) bn)) sub
lem-bound (¥ y)     n k bn sub with ex-mid (k ≡ᵇ y)
...| inj₁ x rewrite lift-≡ᵇ k y x = bn
...| inj₂ x rewrite ¬Tb x = ⊥-elim sub

-- another variant of subst
env-eq-bound : ∀ ξ₁ ξ₂ φ n → T (bound n φ) → (∀ m → T (m <ᵇ n) → ξ₁ m ≡ ξ₂ m)
             → ⟦ ξ₁ ⊧ φ ⟧pl ≡ ⟦ ξ₂ ⊧ φ ⟧pl
env-eq-bound ξ₁ ξ₂ ¥true     n p q = refl
env-eq-bound ξ₁ ξ₂ ¥false    n p q = refl
env-eq-bound ξ₁ ξ₂ (φ || φ₁) n p q = cong₂ _⊎_ (env-eq-bound ξ₁ ξ₂ φ n (∧-eliml p) q)
                                               (env-eq-bound ξ₁ ξ₂ φ₁ n (∧-elimr (bound n φ) p) q)
env-eq-bound ξ₁ ξ₂ (φ && φ₁) n p q = cong₂ _×_ (env-eq-bound ξ₁ ξ₂ φ n (∧-eliml p) q)
                                               (env-eq-bound ξ₁ ξ₂ φ₁ n (∧-elimr (bound n φ) p) q)
env-eq-bound ξ₁ ξ₂ (φ => φ₁) n p q = cong₂ (λ a b → a → b)
                                           (env-eq-bound ξ₁ ξ₂ φ n (∧-eliml p) q)
                                           (env-eq-bound ξ₁ ξ₂ φ₁ n (∧-elimr (bound n φ) p) q)
env-eq-bound ξ₁ ξ₂ (¥ x)     n p q = cong T (q x p)

env-eq-bound-subst : ∀ ξ₁ ξ₂ φ n → T (bound n φ) → (∀ m → T (m <ᵇ n) → ξ₁ m ≡ ξ₂ m)
                   → ⟦ ξ₁ ⊧ φ ⟧pl → ⟦ ξ₂ ⊧ φ ⟧pl
env-eq-bound-subst ξ₁ ξ₂ φ n p q r rewrite env-eq-bound ξ₁ ξ₂ φ n p q = r

injbool : Bool → PL-Formula
injbool true = ¥true
injbool false = ¥false

andpl : List PL-Formula → PL-Formula
andpl = foldr _&&_ ¥true
