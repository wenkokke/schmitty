module Kanso.Boolean.Formula.Equivalence where

open import Data.Bool as Bool using (Bool; true; false; T; _∧_; _∨_)
open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Nat as Nat using (ℕ)
open import Data.Product as Prod using (_×_; proj₁; proj₂; _,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit as Unit using (⊤; tt)
open import Function using (_∘_; id)

open import Kanso.PropIso
open import Kanso.Boolean.Formula

private
  mutual
    data PL-List* : Set where
      [_] : PL-Formula* → PL-List*
      _∷_ : PL-Formula* → PL-List* → PL-List*

    data PL-Formula* : Set where
      $true $false : PL-Formula*
      or* and* : PL-List* → PL-Formula*
      imp* : PL-Formula* → PL-Formula* → PL-Formula*
      $ : ℕ → PL-Formula*

  _++_ : PL-List* → PL-List* → PL-List*
  [ x ] ++ Δ = x ∷ Δ
  (x ∷ Γ) ++ Δ = x ∷ (Γ ++ Δ)

  ⟦_⊧_⟧pl* : (ξ : Env) → PL-Formula* → Set
  ⟦ ξ ⊧ $true ⟧pl* = ⊤
  ⟦ ξ ⊧ $false ⟧pl* = ⊥
  ⟦ ξ ⊧ and* [ x ] ⟧pl* = ⟦ ξ ⊧ x ⟧pl*
  ⟦ ξ ⊧ and* (φ ∷ φs) ⟧pl* = ⟦ ξ ⊧ φ ⟧pl* × ⟦ ξ ⊧ and* φs ⟧pl*
  ⟦ ξ ⊧ or* [ x ] ⟧pl* = ⟦ ξ ⊧ x ⟧pl*
  ⟦ ξ ⊧ or* (φ ∷ φs) ⟧pl* = ⟦ ξ ⊧ φ ⟧pl* ⊎ ⟦ ξ ⊧ or* φs ⟧pl*
  ⟦ ξ ⊧ imp* φ ψ ⟧pl* = ⟦ ξ ⊧ φ ⟧pl* → ⟦ ξ ⊧ ψ ⟧pl*
  ⟦ ξ ⊧ $ v ⟧pl* = T (ξ v)


  flatten-or' : PL-Formula* → PL-Formula* → PL-List*
  flatten-or' (or* φs) (or* ψs) = φs ++ ψs
  flatten-or' (or* φs) ψ = φs ++ [ ψ ]
  flatten-or' φ (or* ψs) = φ ∷ ψs
  flatten-or' φ ψ = φ ∷ [ ψ ]

  flatten-or : PL-Formula* → PL-Formula* → PL-Formula*
  flatten-or a b = or* (flatten-or' a b)

  flatten-and' : PL-Formula* → PL-Formula* → PL-List*
  flatten-and' (and* φs) (and* ψs) = φs ++ ψs
  flatten-and' (and* φs) ψ = φs ++ [ ψ ]
  flatten-and' φ (and* ψs) = φ ∷ ψs
  flatten-and' φ ψ = φ ∷ [ ψ ]

  flatten-and : PL-Formula* → PL-Formula* → PL-Formula*
  flatten-and a b = and* (flatten-and' a b)

flatten : PL-Formula → PL-Formula*
flatten = elim-pl $true $false $ flatten-or flatten-and imp*

private
  mutual
    _≡ᵇ_ : PL-Formula* → PL-Formula* → Bool
    $true     ≡ᵇ $true     = true
    $false    ≡ᵇ $false    = true
    or* x     ≡ᵇ or* y     = x ≡ᵇ[] y
    and* x    ≡ᵇ and* y    = x ≡ᵇ[] y
    imp* φ φ₁ ≡ᵇ imp* ψ ψ₁ = φ ≡ᵇ ψ ∧ φ₁ ≡ᵇ ψ₁
    $ x       ≡ᵇ $ y       = x Nat.≡ᵇ y
    x         ≡ᵇ y         = false

    _≡ᵇ[]_ : PL-List* → PL-List* → Bool
    [ x ] ≡ᵇ[] [ y ]       = x ≡ᵇ y
    (x ∷ xs) ≡ᵇ[] (y ∷ ys) = x ≡ᵇ y ∧ xs ≡ᵇ[] ys
    _ ≡ᵇ[] _               = false

  _∈**_ : PL-Formula* → PL-List* → Bool
  φ ∈** [ x ] = φ ≡ᵇ x
  φ ∈** (ψ ∷ ψs) = φ ≡ᵇ ψ ∨ φ ∈** ψs

  mutual
    sym-≡ᵇ' : (φ ψ : PL-Formula*) → T (φ ≡ᵇ ψ) → T (ψ ≡ᵇ φ)
    sym-≡ᵇ' $true       $true       eq = eq
    sym-≡ᵇ' $true       $false      eq = eq
    sym-≡ᵇ' $true       (or* x)     eq = eq
    sym-≡ᵇ' $true       (and* x)    eq = eq
    sym-≡ᵇ' $true       (imp* ψ ψ₁) eq = eq
    sym-≡ᵇ' $true       ($ x)       eq = eq
    sym-≡ᵇ' $false      $true       eq = eq
    sym-≡ᵇ' $false      $false      eq = eq
    sym-≡ᵇ' $false      (or* x)     eq = eq
    sym-≡ᵇ' $false      (and* x)    eq = eq
    sym-≡ᵇ' $false      (imp* ψ ψ₁) eq = eq
    sym-≡ᵇ' $false      ($ x)       eq = eq
    sym-≡ᵇ' (or* x)     $true       eq = eq
    sym-≡ᵇ' (or* x)     $false      eq = eq
    sym-≡ᵇ' (or* x)     (or* x₁)    eq = sym-≡ᵇ[] x x₁ eq
    sym-≡ᵇ' (or* x)     (and* x₁)   eq = eq
    sym-≡ᵇ' (or* x)     (imp* ψ ψ₁) eq = eq
    sym-≡ᵇ' (or* x)     ($ x₁)      eq = eq
    sym-≡ᵇ' (and* x)    $true       eq = eq
    sym-≡ᵇ' (and* x)    $false      eq = eq
    sym-≡ᵇ' (and* x)    (or* x₁)    eq = eq
    sym-≡ᵇ' (and* x)    (and* x₁)   eq = sym-≡ᵇ[] x x₁ eq
    sym-≡ᵇ' (and* x)    (imp* ψ ψ₁) eq = eq
    sym-≡ᵇ' (and* x)    ($ x₁)      eq = eq
    sym-≡ᵇ' (imp* φ φ₁) $true       eq = eq
    sym-≡ᵇ' (imp* φ φ₁) $false      eq = eq
    sym-≡ᵇ' (imp* φ φ₁) (or* x)     eq = eq
    sym-≡ᵇ' (imp* φ φ₁) (and* x)    eq = eq
    sym-≡ᵇ' (imp* φ φ₁) (imp* ψ ψ₁) eq = f∧g (sym-≡ᵇ' φ ψ) (sym-≡ᵇ' φ₁ ψ₁) eq
    sym-≡ᵇ' (imp* φ φ₁) ($ x)       eq = eq
    sym-≡ᵇ' ($ x)       $true       eq = eq
    sym-≡ᵇ' ($ x)       $false      eq = eq
    sym-≡ᵇ' ($ x)       (or* x₁)    eq = eq
    sym-≡ᵇ' ($ x)       (and* x₁)   eq = eq
    sym-≡ᵇ' ($ x)       (imp* ψ ψ₁) eq = eq
    sym-≡ᵇ' ($ x)       ($ x₁)      eq = sym-≡ᵇ x x₁ eq

    sym-≡ᵇ[] : (Γ Δ : PL-List*) → T (Γ ≡ᵇ[] Δ) → T (Δ ≡ᵇ[] Γ)
    sym-≡ᵇ[] [ x ]   [ y ]    p = sym-≡ᵇ' x y p
    sym-≡ᵇ[] [ x ]   (x' ∷ Δ) p = p
    sym-≡ᵇ[] (x ∷ Γ) [ y ]    p = p
    sym-≡ᵇ[] (γ ∷ Γ) (δ ∷ Δ)  p = f∧g (sym-≡ᵇ' γ δ) (sym-≡ᵇ[] Γ Δ) p

  mutual
     eq : PL-Formula* → PL-Formula* → Bool
     eq (and* y)    (or* x)     = alleq* x (and* y) ∨ alleq* y (or* x)
     eq (or* x)     (and* y)    = alleq* y (or* x) ∨ alleq* x (and* y)
     eq (or* x)     (or* y)     = (y ⊆pl* x ∧ x ⊆pl* y) ∨ alleq* x (or* y) ∨ alleq* y (or* x)
     eq (or* x)     ψ           = alleq* x ψ
     eq (and* x)    (and* y)    = (y ⊆pl* x ∧ x ⊆pl* y) ∨ alleq* x (and* y) ∨ alleq* y (and* x)
     eq (and* x)    ψ           = alleq* x ψ
     eq φ           (or* x)     = alleq* x φ
     eq φ           (and* x)    = alleq* x φ
     eq (imp* φ φ₁) (imp* ψ ψ₁) = eq φ ψ ∧ eq φ₁ ψ₁
     eq φ           ψ           = φ ≡ᵇ ψ

     alleq* : PL-List* → PL-Formula* → Bool
     alleq* [ x ]   φ = eq x φ
     alleq* (x ∷ l) φ = eq x φ ∧ alleq* l φ

     _⊆pl*_ : PL-List* → PL-List* → Bool
     [ x ]    ⊆pl* y  = x ∈* y
     (x ∷ xs) ⊆pl* ys = x ∈* ys ∧ xs ⊆pl* ys

     _∈*_ : PL-Formula* → PL-List* → Bool
     φ ∈* [ x ]    = eq φ x
     φ ∈* (ψ ∷ ψs) = eq φ ψ ∨ φ ∈* ψs

  sym-eq : (φ ψ : PL-Formula*) → T (eq φ ψ) → T (eq ψ φ)
  sym-eq $true $true eq = eq
  sym-eq $true $false eq = eq
  sym-eq $true (or* x) eq = eq
  sym-eq $true (and* x) eq = eq
  sym-eq $true (imp* ψ ψ₁) eq = eq
  sym-eq $true ($ x) eq = eq
  sym-eq $false $true eq = eq
  sym-eq $false $false eq = eq
  sym-eq $false (or* x) eq = eq
  sym-eq $false (and* x) eq = eq
  sym-eq $false (imp* ψ ψ₁) eq = eq
  sym-eq $false ($ x) eq = eq
  sym-eq (or* x) $true eq = eq
  sym-eq (or* x) $false eq = eq
  sym-eq (or* x) (or* x₁) eq = f∨g (∧-swap _ (x ⊆pl* x₁))
                                   (∨-swap (alleq* x (or* x₁)) _) eq
  sym-eq (or* x) (and* x₁) eq = ∨-swap (alleq* x₁ (or* x)) _ eq
  sym-eq (or* x) (imp* ψ ψ₁) eq = eq
  sym-eq (or* x) ($ x₁) eq = eq
  sym-eq (and* x) $true eq = eq
  sym-eq (and* x) $false eq = eq
  sym-eq (and* x) (or* x₁) eq = ∨-swap (alleq* x₁ (and* x)) _ eq
  sym-eq (and* x) (and* x₁) eq = f∨g (∧-swap _ (x ⊆pl* x₁))
                                     (∨-swap (alleq* x (and* x₁)) _) eq
  sym-eq (and* x) (imp* ψ ψ₁) eq = eq
  sym-eq (and* x) ($ x₁) eq = eq
  sym-eq (imp* φ φ₁) $true eq = eq
  sym-eq (imp* φ φ₁) $false eq = eq
  sym-eq (imp* φ φ₁) (or* x) eq = eq
  sym-eq (imp* φ φ₁) (and* x) eq = eq
  sym-eq (imp* φ φ₁) (imp* ψ ψ₁) eq' = f∧g (sym-eq φ ψ) (sym-eq φ₁ ψ₁) eq'
  sym-eq (imp* φ φ₁) ($ x) eq = eq
  sym-eq ($ x) $true eq = eq
  sym-eq ($ x) $false eq = eq
  sym-eq ($ x) (or* x₁) eq = eq
  sym-eq ($ x) (and* x₁) eq = eq
  sym-eq ($ x) (imp* ψ ψ₁) eq = eq
  sym-eq ($ x) ($ x₁) eq = sym-≡ᵇ x x₁ eq

  ord-⊆pl* : ∀ φ Γ Δ → T (Γ ⊆pl* Δ) → T (Γ ⊆pl* (φ ∷ Δ))
  ord-⊆pl* φ [ γ ] Δ p = ∨-intror (eq γ φ) (γ ∈* Δ) p
  ord-⊆pl* φ (γ ∷ Γ) Δ p = f∧g (∨-intror (eq γ φ) (γ ∈* Δ)) (ord-⊆pl* φ Γ Δ) p

  mutual
    id-⊆pl* : ∀ Γ → T (Γ ⊆pl* Γ)
    id-⊆pl* [ γ ] = id-eq γ
    id-⊆pl* (γ ∷ Γ) = ∧-intro _ _ (∨-introl _ _ (id-eq γ)) (ord-⊆pl* γ Γ Γ (id-⊆pl* Γ))

    id-eq : ∀ φ → T (eq φ φ)
    id-eq $true = tt
    id-eq $false = tt
    id-eq (or* y) = ∨-introl _ _ (∧-intro _ _ (id-⊆pl* y) (id-⊆pl* y))
    id-eq (and* y) = ∨-introl _ _ (∧-intro _ _ (id-⊆pl* y) (id-⊆pl* y))
    id-eq (imp* y y') = ∧-intro (eq y y) _ (id-eq y) (id-eq y')
    id-eq ($ y) = id-≡ᵇ y

    subst-eq : ∀ ξ φ ψ → T (eq φ ψ) → ⟦ ξ ⊧ φ ⟧pl* → ⟦ ξ ⊧ ψ ⟧pl*
    subst-eq ξ $true $true eqp p = p
    subst-eq ξ $true $false eqp p = ⊥-elim eqp
    subst-eq ξ $true (or* x) eqp p = subst-alleq-or ξ x $true tt eqp
    subst-eq ξ $true (and* x) eqp p = subst-alleq-and ξ x $true tt eqp
    subst-eq ξ $true (imp* ψ ψ₁) eqp p = ⊥-elim eqp
    subst-eq ξ $true ($ x) eqp p = ⊥-elim eqp
    subst-eq ξ $false ψ eqp p = ⊥-elim p
    subst-eq ξ (or* x) $true eqp p = subst-alleq-or' ξ x $true p eqp
    subst-eq ξ (or* x) $false eqp p = subst-alleq-or' ξ x $false p eqp
    subst-eq ξ (or* x) (or* x₁) eqp p =
      ∨-elim (λ k → subst-eq-or ξ x x₁ p (∧-elimr (x₁ ⊆pl* x) k))
                                (∨-elim (subst-alleq-or' ξ x (or* x₁) p)
                                        (subst-alleq-or ξ x₁ (or* x) p)) eqp
    subst-eq ξ (or* x) (and* x₁) eqp p = ∨-elim (subst-alleq-and ξ x₁ (or* x) p)
                                                (subst-alleq-or' ξ x (and* x₁) p) eqp
    subst-eq ξ (or* x) (imp* ψ ψ₁) eqp p = subst-alleq-or' ξ x (imp* ψ ψ₁) p eqp
    subst-eq ξ (or* x) ($ x₁) eqp p = subst-alleq-or' ξ x ($ x₁) p eqp
    subst-eq ξ (and* x) $true eqp p = subst-alleq-and' ξ x $true p eqp
    subst-eq ξ (and* x) $false eqp p = subst-alleq-and' ξ x $false p eqp
    subst-eq ξ (and* x) (or* x₁) eqp p = ∨-elim (subst-alleq-or ξ x₁ (and* x) p)
                                                (subst-alleq-and' ξ x (or* x₁) p) eqp
    subst-eq ξ (and* x) (and* x₁) eqp p =
      ∨-elim (λ k → subst-eq-and ξ x x₁ p (∧-eliml k))
                                 (∨-elim (subst-alleq-and' ξ x (and* x₁) p)
                                         (subst-alleq-and ξ x₁ (and* x) p)) eqp
    subst-eq ξ (and* x) (imp* ψ ψ₁) eqp p = subst-alleq-and' ξ x (imp* ψ ψ₁) p eqp
    subst-eq ξ (and* x) ($ x₁) eqp p = subst-alleq-and' ξ x ($ x₁) p eqp
    subst-eq ξ (imp* φ φ₁) $true eqp p = ⊥-elim eqp
    subst-eq ξ (imp* φ φ₁) $false eqp p = ⊥-elim eqp
    subst-eq ξ (imp* φ φ₁) (or* x) eqp p = subst-alleq-or ξ x (imp* φ φ₁) p eqp
    subst-eq ξ (imp* φ φ₁) (and* x) eqp p = subst-alleq-and ξ x (imp* φ φ₁) p eqp
    subst-eq ξ (imp* φ φ₁) (imp* ψ ψ₁) eqp p =
      subst-eq ξ φ₁ ψ₁ (∧-elimr (eq φ ψ) eqp) ∘ p ∘ subst-eq ξ ψ φ (sym-eq φ ψ (∧-eliml eqp))
    subst-eq ξ (imp* φ φ₁) ($ x) eqp p = ⊥-elim eqp
    subst-eq ξ ($ x) $true eqp p = ⊥-elim eqp
    subst-eq ξ ($ x) $false eqp p = ⊥-elim eqp
    subst-eq ξ ($ x) (or* x₁) eqp p = subst-alleq-or ξ x₁ ($ x) p eqp
    subst-eq ξ ($ x) (and* x₁) eqp p = subst-alleq-and ξ x₁ ($ x) p eqp
    subst-eq ξ ($ x) (imp* ψ ψ₁) eqp p = ⊥-elim eqp
    subst-eq ξ ($ x) ($ x₁) eqp p rewrite lift-≡ᵇ x x₁ eqp = p

    subst-alleq-and : ∀ ξ Γ φ → ⟦ ξ ⊧ φ ⟧pl* → T (alleq* Γ φ) → ⟦ ξ ⊧ and* Γ ⟧pl*
    subst-alleq-and ξ [ x ] φ [φ] aeq = subst-eq ξ φ x (sym-eq x φ aeq) [φ]
    subst-alleq-and ξ (x ∷ Γ) φ [φ] aeq = ∧-elim (λ a b → (subst-eq ξ φ x (sym-eq x φ a) [φ])
                                                          , (subst-alleq-and ξ Γ φ [φ] b)) aeq

    subst-alleq-or : ∀ ξ Γ φ → ⟦ ξ ⊧ φ ⟧pl* → T (alleq* Γ φ) → ⟦ ξ ⊧ or* Γ ⟧pl*
    subst-alleq-or ξ [ x ] φ [φ] aeq = subst-eq ξ φ x (sym-eq x φ aeq) [φ]
    subst-alleq-or ξ (x ∷ Γ) φ [φ] aeq = inj₁ (subst-eq ξ φ x (sym-eq x φ (∧-eliml aeq)) [φ])

    subst-alleq-or' : ∀ ξ Γ φ → ⟦ ξ ⊧ or* Γ ⟧pl* → T (alleq* Γ φ) → ⟦ ξ ⊧ φ ⟧pl*
    subst-alleq-or' ξ [ x ] φ [φ] aeq = subst-eq ξ x φ aeq [φ]
    subst-alleq-or' ξ (x ∷ Γ) φ (inj₁ x₁) aeq = subst-eq ξ x φ (∧-eliml aeq) x₁
    subst-alleq-or' ξ (x ∷ Γ) φ (inj₂ y) aeq = subst-alleq-or' ξ Γ φ y (∧-elimr (eq x φ) aeq)

    subst-alleq-and' : ∀ ξ Γ φ → ⟦ ξ ⊧ and* Γ ⟧pl* → T (alleq* Γ φ) → ⟦ ξ ⊧ φ ⟧pl*
    subst-alleq-and' ξ [ x ] φ [φ] aeq = subst-eq ξ x φ aeq [φ]
    subst-alleq-and' ξ (x ∷ Γ) φ [φ] aeq = subst-eq ξ x φ (∧-eliml aeq) (proj₁ [φ])

    subst-∈-and : ∀ ξ Γ φ → T (φ ∈* Γ) → ⟦ ξ ⊧ and* Γ ⟧pl* → ⟦ ξ ⊧ φ ⟧pl*
    subst-∈-and ξ [ x ] φ p q = subst-eq ξ x φ (sym-eq φ x p) q
    subst-∈-and ξ (x ∷ Γ) φ p q = ∨-elim (λ k → subst-eq ξ x φ (sym-eq φ x k) (proj₁ q))
                                         (λ k → subst-∈-and ξ Γ φ k (proj₂ q)) p

    subst-eq-and : ∀ ξ Γ Δ → ⟦ ξ ⊧ and* Γ ⟧pl* → T (Δ ⊆pl* Γ) → ⟦ ξ ⊧ and* Δ ⟧pl*
    subst-eq-and ξ Γ [ x ] p f = subst-∈-and ξ Γ x f p
    subst-eq-and ξ Γ (x ∷ Δ) p f = (subst-∈-and ξ Γ x (∧-eliml f) p)
                                   , (subst-eq-and ξ Γ Δ p (∧-elimr (x ∈* Γ) f))

    subst-∈-or : ∀ ξ Γ φ → T (φ ∈* Γ) → ⟦ ξ ⊧ φ ⟧pl* → ⟦ ξ ⊧ or* Γ ⟧pl*
    subst-∈-or ξ [ x ] φ p q = subst-eq ξ φ x p q
    subst-∈-or ξ (x ∷ Γ) φ p q = ∨-elim (λ k → inj₁ (subst-eq ξ φ x k q))
                                        (λ k → inj₂ (subst-∈-or ξ Γ φ k q)) p

    subst-eq-or : ∀ ξ Γ Δ → ⟦ ξ ⊧ or* Γ ⟧pl* → T (Γ ⊆pl* Δ) → ⟦ ξ ⊧ or* Δ ⟧pl*
    subst-eq-or ξ [ x ] Δ p q = subst-∈-or ξ Δ x q p
    subst-eq-or ξ (x ∷ Γ) Δ (inj₁ x₁) q = subst-∈-or ξ Δ x (∧-eliml q) x₁
    subst-eq-or ξ (x ∷ Γ) Δ (inj₂ y) q = subst-eq-or ξ Γ Δ y (∧-elimr (x ∈* Δ) q)

  lem-or-elim : ∀ ξ φ ψ
              → ⟦ ξ ⊧ or* (flatten-or' φ ψ) ⟧pl* → ⟦ ξ ⊧ φ ⟧pl* ⊎ ⟦ ξ ⊧ ψ ⟧pl*
  lem-or-elim ξ $true $true p = p
  lem-or-elim ξ $true $false p = p
  lem-or-elim ξ $true (or* x) p = p
  lem-or-elim ξ $true (and* x) p = p
  lem-or-elim ξ $true (imp* ψ ψ₁) p = p
  lem-or-elim ξ $true ($ x) p = p
  lem-or-elim ξ $false $true p = p
  lem-or-elim ξ $false $false p = p
  lem-or-elim ξ $false (or* x) p = p
  lem-or-elim ξ $false (and* x) p = p
  lem-or-elim ξ $false (imp* ψ ψ₁) p = p
  lem-or-elim ξ $false ($ x) p = p
  lem-or-elim ξ (or* [ x ]) $true p = p
  lem-or-elim ξ (or* [ x ]) $false p = p
  lem-or-elim ξ (or* [ x ]) (or* x₁) p = p
  lem-or-elim ξ (or* [ x ]) (and* x₁) p = p
  lem-or-elim ξ (or* [ x ]) (imp* ψ ψ₁) p = p
  lem-or-elim ξ (or* [ x ]) ($ x₁) p = p
  lem-or-elim ξ (or* (x ∷ xs)) $true p =
    [ inj₁ ∘ inj₁ , (λ x' → Sum.map inj₂ id (lem-or-elim ξ (or* xs) $true x')) ]′ p
  lem-or-elim ξ (or* (x ∷ xs)) $false p =
    [ inj₁ ∘ inj₁ , (λ x' → Sum.map inj₂ id (lem-or-elim ξ (or* xs) $false x')) ]′ p
  lem-or-elim ξ (or* (x ∷ xs)) (or* x₁) p =
    [ inj₁ ∘ inj₁ , (λ x' → Sum.map inj₂ id (lem-or-elim ξ (or* xs) (or* x₁) x')) ]′ p
  lem-or-elim ξ (or* (x ∷ xs)) (and* x₁) p =
    [ inj₁ ∘ inj₁ , (λ x' → Sum.map inj₂ id (lem-or-elim ξ (or* xs) (and* x₁) x')) ]′ p
  lem-or-elim ξ (or* (x ∷ xs)) (imp* ψ ψ₁) p =
    [ inj₁ ∘ inj₁ , (λ x' → Sum.map inj₂ id (lem-or-elim ξ (or* xs) (imp* ψ ψ₁) x')) ]′ p
  lem-or-elim ξ (or* (x ∷ xs)) ($ x₁) p =
    [ inj₁ ∘ inj₁ , (λ x' → Sum.map inj₂ id (lem-or-elim ξ (or* xs) ($ x₁) x')) ]′ p
  lem-or-elim ξ (and* x) $true p = p
  lem-or-elim ξ (and* x) $false p = p
  lem-or-elim ξ (and* x) (or* x₁) p = p
  lem-or-elim ξ (and* x) (and* x₁) p = p
  lem-or-elim ξ (and* x) (imp* ψ ψ₁) p = p
  lem-or-elim ξ (and* x) ($ x₁) p = p
  lem-or-elim ξ (imp* φ φ₁) $true p = p
  lem-or-elim ξ (imp* φ φ₁) $false p = p
  lem-or-elim ξ (imp* φ φ₁) (or* x) p = p
  lem-or-elim ξ (imp* φ φ₁) (and* x) p = p
  lem-or-elim ξ (imp* φ φ₁) (imp* ψ ψ₁) p = p
  lem-or-elim ξ (imp* φ φ₁) ($ x) p = p
  lem-or-elim ξ ($ x) $true p = p
  lem-or-elim ξ ($ x) $false p = p
  lem-or-elim ξ ($ x) (or* x₁) p = p
  lem-or-elim ξ ($ x) (and* x₁) p = p
  lem-or-elim ξ ($ x) (imp* ψ ψ₁) p = p
  lem-or-elim ξ ($ x) ($ x₁) p = p

  lem-or-elim' : ∀ ξ φ ψ
               → ⟦ ξ ⊧ φ ⟧pl* ⊎ ⟦ ξ ⊧ ψ ⟧pl* → ⟦ ξ ⊧ or* (flatten-or' φ ψ) ⟧pl*
  lem-or-elim' ξ $true $true p = p
  lem-or-elim' ξ $true $false p = p
  lem-or-elim' ξ $true (or* x) p = p
  lem-or-elim' ξ $true (and* x) p = p
  lem-or-elim' ξ $true (imp* ψ ψ₁) p = p
  lem-or-elim' ξ $true ($ x) p = p
  lem-or-elim' ξ $false $true p = p
  lem-or-elim' ξ $false $false p = p
  lem-or-elim' ξ $false (or* x) p = p
  lem-or-elim' ξ $false (and* x) p = p
  lem-or-elim' ξ $false (imp* ψ ψ₁) p = p
  lem-or-elim' ξ $false ($ x) p = p
  lem-or-elim' ξ (or* [ x ]) $true p = p
  lem-or-elim' ξ (or* [ x ]) $false p = p
  lem-or-elim' ξ (or* [ x ]) (or* x₁) p = p
  lem-or-elim' ξ (or* [ x ]) (and* x₁) p = p
  lem-or-elim' ξ (or* [ x ]) (imp* ψ ψ₁) p = p
  lem-or-elim' ξ (or* [ x ]) ($ x₁) p = p
  lem-or-elim' ξ (or* (x ∷ x₁)) $true p = Sum.map id (lem-or-elim' ξ (or* x₁) $true) (lem-⊎ p)
  lem-or-elim' ξ (or* (x ∷ x₁)) $false p = Sum.map id (lem-or-elim' ξ (or* x₁) $false) (lem-⊎ p)
  lem-or-elim' ξ (or* (x ∷ x₁)) (or* x₂) p = Sum.map id (lem-or-elim' ξ (or* x₁) (or* x₂))
                                                                      (lem-⊎ p)
  lem-or-elim' ξ (or* (x ∷ x₁)) (and* x₂) p = Sum.map id (lem-or-elim' ξ (or* x₁) (and* x₂))
                                                                       (lem-⊎ p)
  lem-or-elim' ξ (or* (x ∷ x₁)) (imp* ψ ψ₁) p = Sum.map id (lem-or-elim' ξ (or* x₁) (imp* ψ ψ₁))
                                                                         (lem-⊎ p)
  lem-or-elim' ξ (or* (x ∷ x₁)) ($ x₂) p = Sum.map id (lem-or-elim' ξ (or* x₁) ($ x₂)) (lem-⊎ p)
  lem-or-elim' ξ (and* x) $true p = p
  lem-or-elim' ξ (and* x) $false p = p
  lem-or-elim' ξ (and* x) (or* x₁) p = p
  lem-or-elim' ξ (and* x) (and* x₁) p = p
  lem-or-elim' ξ (and* x) (imp* ψ ψ₁) p = p
  lem-or-elim' ξ (and* x) ($ x₁) p = p
  lem-or-elim' ξ (imp* φ φ₁) $true p = p
  lem-or-elim' ξ (imp* φ φ₁) $false p = p
  lem-or-elim' ξ (imp* φ φ₁) (or* x) p = p
  lem-or-elim' ξ (imp* φ φ₁) (and* x) p = p
  lem-or-elim' ξ (imp* φ φ₁) (imp* ψ ψ₁) p = p
  lem-or-elim' ξ (imp* φ φ₁) ($ x) p = p
  lem-or-elim' ξ ($ x) $true p = p
  lem-or-elim' ξ ($ x) $false p = p
  lem-or-elim' ξ ($ x) (or* x₁) p = p
  lem-or-elim' ξ ($ x) (and* x₁) p = p
  lem-or-elim' ξ ($ x) (imp* ψ ψ₁) p = p
  lem-or-elim' ξ ($ x) ($ x₁) p = p

  lem-and-elim : ∀ ξ φ ψ
               → ⟦ ξ ⊧ and* (flatten-and' φ ψ) ⟧pl* → ⟦ ξ ⊧ φ ⟧pl* × ⟦ ξ ⊧ ψ ⟧pl*
  lem-and-elim ξ $true $true p = p
  lem-and-elim ξ $true $false p = p
  lem-and-elim ξ $true (or* x) p = p
  lem-and-elim ξ $true (and* x) p = p
  lem-and-elim ξ $true (imp* ψ ψ₁) p = p
  lem-and-elim ξ $true ($ x) p = p
  lem-and-elim ξ $false $true p = p
  lem-and-elim ξ $false $false p = p
  lem-and-elim ξ $false (or* x) p = p
  lem-and-elim ξ $false (and* x) p = p
  lem-and-elim ξ $false (imp* ψ ψ₁) p = p
  lem-and-elim ξ $false ($ x) p = p
  lem-and-elim ξ (or* x) $true p = p
  lem-and-elim ξ (or* x) $false p = p
  lem-and-elim ξ (or* x) (or* x₁) p = p
  lem-and-elim ξ (or* x) (and* x₁) p = p
  lem-and-elim ξ (or* x) (imp* ψ ψ₁) p = p
  lem-and-elim ξ (or* x) ($ x₁) p = p
  lem-and-elim ξ (and* [ x ]) $true p = p
  lem-and-elim ξ (and* [ x ]) $false p = p
  lem-and-elim ξ (and* [ x ]) (or* x₁) p = p
  lem-and-elim ξ (and* [ x ]) (and* x₁) p = p
  lem-and-elim ξ (and* [ x ]) (imp* ψ ψ₁) p = p
  lem-and-elim ξ (and* [ x ]) ($ x₁) p = p
  lem-and-elim ξ (and* (x ∷ xs)) $true p =
    Prod.map (_,_ (proj₁ p)) id (lem-and-elim ξ (and* xs) $true (proj₂ p))
  lem-and-elim ξ (and* (x ∷ xs)) $false p =
    Prod.map (_,_ (proj₁ p)) id (lem-and-elim ξ (and* xs) $false (proj₂ p))
  lem-and-elim ξ (and* (x ∷ xs)) (or* x₁) p =
    Prod.map (_,_ (proj₁ p)) id (lem-and-elim ξ (and* xs) (or* x₁) (proj₂ p))
  lem-and-elim ξ (and* (x ∷ xs)) (and* x₁) p =
    Prod.map (_,_ (proj₁ p)) id (lem-and-elim ξ (and* xs) (and* x₁) (proj₂ p))
  lem-and-elim ξ (and* (x ∷ xs)) (imp* ψ ψ₁) p =
    Prod.map (_,_ (proj₁ p)) id (lem-and-elim ξ (and* xs) (imp* ψ ψ₁) (proj₂ p))
  lem-and-elim ξ (and* (x ∷ xs)) ($ x₁) p =
    Prod.map (_,_ (proj₁ p)) id (lem-and-elim ξ (and* xs) ($ x₁) (proj₂ p))
  lem-and-elim ξ (imp* φ φ₁) $true p = p
  lem-and-elim ξ (imp* φ φ₁) $false p = p
  lem-and-elim ξ (imp* φ φ₁) (or* x) p = p
  lem-and-elim ξ (imp* φ φ₁) (and* x) p = p
  lem-and-elim ξ (imp* φ φ₁) (imp* ψ ψ₁) p = p
  lem-and-elim ξ (imp* φ φ₁) ($ x) p = p
  lem-and-elim ξ ($ x) $true p = p
  lem-and-elim ξ ($ x) $false p = p
  lem-and-elim ξ ($ x) (or* x₁) p = p
  lem-and-elim ξ ($ x) (and* x₁) p = p
  lem-and-elim ξ ($ x) (imp* ψ ψ₁) p = p
  lem-and-elim ξ ($ x) ($ x₁) p = p

  lem-and-elim' : ∀ ξ φ ψ
                → ⟦ ξ ⊧ φ ⟧pl* × ⟦ ξ ⊧ ψ ⟧pl* → ⟦ ξ ⊧ and* (flatten-and' φ ψ) ⟧pl*
  lem-and-elim' ξ $true $true p = p
  lem-and-elim' ξ $true $false p = p
  lem-and-elim' ξ $true (or* x) p = p
  lem-and-elim' ξ $true (and* x) p = p
  lem-and-elim' ξ $true (imp* ψ ψ₁) p = p
  lem-and-elim' ξ $true ($ x) p = p
  lem-and-elim' ξ $false $true p = p
  lem-and-elim' ξ $false $false p = p
  lem-and-elim' ξ $false (or* x) p = p
  lem-and-elim' ξ $false (and* x) p = p
  lem-and-elim' ξ $false (imp* ψ ψ₁) p = p
  lem-and-elim' ξ $false ($ x) p = p
  lem-and-elim' ξ (or* x) $true p = p
  lem-and-elim' ξ (or* x) $false p = p
  lem-and-elim' ξ (or* x) (or* x₁) p = p
  lem-and-elim' ξ (or* x) (and* x₁) p = p
  lem-and-elim' ξ (or* x) (imp* ψ ψ₁) p = p
  lem-and-elim' ξ (or* x) ($ x₁) p = p
  lem-and-elim' ξ (and* [ x ]) $true p = p
  lem-and-elim' ξ (and* [ x ]) $false p = p
  lem-and-elim' ξ (and* [ x ]) (or* x₁) p = p
  lem-and-elim' ξ (and* [ x ]) (and* x₁) p = p
  lem-and-elim' ξ (and* [ x ]) (imp* ψ ψ₁) p = p
  lem-and-elim' ξ (and* [ x ]) ($ x₁) p = p
  lem-and-elim' ξ (and* (x ∷ x₁)) $true p =
    Prod.map id (λ k → lem-and-elim' ξ (and* x₁) $true (k , proj₂ p)) (proj₁ p)
  lem-and-elim' ξ (and* (x ∷ x₁)) $false p =
    Prod.map id (λ k → lem-and-elim' ξ (and* x₁) $false (k , proj₂ p)) (proj₁ p)
  lem-and-elim' ξ (and* (x ∷ x₁)) (or* x₂) p =
    Prod.map id (λ k → lem-and-elim' ξ (and* x₁) (or* x₂) (k , proj₂ p)) (proj₁ p)
  lem-and-elim' ξ (and* (x ∷ x₁)) (and* x₂) p =
    Prod.map id (λ k → lem-and-elim' ξ (and* x₁) (and* x₂) (k , proj₂ p)) (proj₁ p)
  lem-and-elim' ξ (and* (x ∷ x₁)) (imp* ψ ψ₁) p =
    Prod.map id (λ k → lem-and-elim' ξ (and* x₁) (imp* ψ ψ₁) (k , proj₂ p)) (proj₁ p)
  lem-and-elim' ξ (and* (x ∷ x₁)) ($ x₂) p =
    Prod.map id (λ k → lem-and-elim' ξ (and* x₁) ($ x₂) (k , proj₂ p)) (proj₁ p)
  lem-and-elim' ξ (imp* φ φ₁) $true p = p
  lem-and-elim' ξ (imp* φ φ₁) $false p = p
  lem-and-elim' ξ (imp* φ φ₁) (or* x) p = p
  lem-and-elim' ξ (imp* φ φ₁) (and* x) p = p
  lem-and-elim' ξ (imp* φ φ₁) (imp* ψ ψ₁) p = p
  lem-and-elim' ξ (imp* φ φ₁) ($ x) p = p
  lem-and-elim' ξ ($ x) $true p = p
  lem-and-elim' ξ ($ x) $false p = p
  lem-and-elim' ξ ($ x) (or* x₁) p = p
  lem-and-elim' ξ ($ x) (and* x₁) p = p
  lem-and-elim' ξ ($ x) (imp* ψ ψ₁) p = p
  lem-and-elim' ξ ($ x) ($ x₁) p = p

  mutual
    lem-flatten : ∀ ξ φ → ⟦ ξ ⊧ flatten φ ⟧pl* → ⟦ ξ ⊧ φ ⟧pl
    lem-flatten ξ ¥true p = tt
    lem-flatten ξ ¥false p = p
    lem-flatten ξ (y || y') p = Sum.map (lem-flatten ξ y) (lem-flatten ξ y')
                                        (lem-or-elim ξ (flatten y) (flatten y') p)
    lem-flatten ξ (y && y') p = Prod.map (lem-flatten ξ y) (lem-flatten ξ y')
                                         (lem-and-elim ξ (flatten y) (flatten y') p)
    lem-flatten ξ (y => y') p = \ x → lem-flatten ξ y' (p (lem-flatten' ξ y x))
    lem-flatten ξ (¥ y) p = p

    lem-flatten' : ∀ ξ φ → ⟦ ξ ⊧ φ ⟧pl → ⟦ ξ ⊧ flatten φ ⟧pl*
    lem-flatten' ξ ¥true p = tt
    lem-flatten' ξ ¥false p = p
    lem-flatten' ξ (y || y') p = lem-or-elim' ξ (flatten y) (flatten y')
                                              (Sum.map (lem-flatten' ξ y)
                                                       (lem-flatten' ξ y') p)
    lem-flatten' ξ (y && y') p = lem-and-elim' ξ (flatten y) (flatten y')
                                               (Prod.map (lem-flatten' ξ y)
                                                         (lem-flatten' ξ y') p)
    lem-flatten' ξ (y => y') p = λ x → lem-flatten' ξ y' (p (lem-flatten ξ y x))
    lem-flatten' ξ (¥ y) p = p

_≡ᵇpl_ : (φ ψ : PL-Formula) → Bool
φ ≡ᵇpl ψ = eq (flatten φ) (flatten ψ)

private
  lift-flatten : ∀ φ ψ → T (φ ≡ᵇpl ψ) → ∀ ξ → ⟦ ξ ⊧ φ ⟧pl → ⟦ ξ ⊧ ψ ⟧pl
  lift-flatten φ ψ φ=ψ ξ [φ] = lem-flatten ξ ψ (subst-eq ξ (flatten φ) (flatten ψ)
                                                         φ=ψ (lem-flatten' ξ φ [φ]))

lift-≡ᵇpl : ∀ φ ψ → T (φ ≡ᵇpl ψ)
          → ∀ ξ → ((⟦ ξ ⊧ φ ⟧pl → ⟦ ξ ⊧ ψ ⟧pl) × (⟦ ξ ⊧ ψ ⟧pl → ⟦ ξ ⊧ φ ⟧pl))
lift-≡ᵇpl φ ψ φ=ψ ξ = (lift-flatten φ ψ φ=ψ ξ)
                    , (lift-flatten ψ φ (sym-eq (flatten φ) (flatten ψ) φ=ψ) ξ)

lift-≡ᵇpl→ : ∀ φ ψ → T (φ ≡ᵇpl ψ) → ∀ ξ → ⟦ ξ ⊧ φ ⟧pl → ⟦ ξ ⊧ ψ ⟧pl
lift-≡ᵇpl→ φ ψ p ξ = proj₁ (lift-≡ᵇpl φ ψ p ξ)

lift-≡ᵇpl← : ∀ φ ψ → T (φ ≡ᵇpl ψ) → ∀ ξ → ⟦ ξ ⊧ ψ ⟧pl → ⟦ ξ ⊧ φ ⟧pl
lift-≡ᵇpl← φ ψ p ξ = proj₂ (lift-≡ᵇpl φ ψ p ξ)
