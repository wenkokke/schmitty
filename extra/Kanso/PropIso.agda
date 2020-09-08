module Kanso.PropIso where

import Algebra.Structures as Alg
open import Data.Bool using (Bool; true; false; T; not) renaming (_∧_ to _∧ᵇ_; _∨_ to _∨ᵇ_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_; _+_; pred)
open import Data.Nat.Properties using (+-*-isCommutativeSemiring)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; ∃; -,_; _×_; _,_; proj₁; proj₂; uncurry′)
open import Relation.Nullary public using (¬_)
open import Function using (id ; _∘_ ; _$_ ; const)
open import Data.Nat.Properties using (isCommutativeSemiring)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst)
open Alg.IsCommutativeSemiring using (+-isCommutativeMonoid)
open Alg.IsCommutativeMonoid using (comm)

{- Propositional logic isomorphisim -}

lem-bool-neg-c : (b : Bool) → ¬ T b → T (not b)
lem-bool-neg-c true p  = p tt
lem-bool-neg-c false p = tt

lem-bool-neg-s : (b : Bool) → T (not b) → ¬ T b
lem-bool-neg-s true  ()
lem-bool-neg-s false p = λ x → x

lem-bool-∧-s : (b c : Bool) → T (b ∧ᵇ c) → T b × T c
lem-bool-∧-s true  _ x = tt , x
lem-bool-∧-s false _ ()

lem-bool-∧-c : (b c : Bool) → T b × T c → T (b ∧ᵇ c)
lem-bool-∧-c true  _ (_ , x') = x'
lem-bool-∧-c false _ (() , _)


lem-bool-∨-s : (b c : Bool) → T (b ∨ᵇ c) → T b ⊎ T c
lem-bool-∨-s true  _ _ = inj₁ tt
lem-bool-∨-s false _ x = inj₂ x

lem-bool-∨-c : (b c : Bool) → T b ⊎ T c → T (b ∨ᵇ c)
lem-bool-∨-c true  _  _         = tt
lem-bool-∨-c false b' (inj₁ ())
lem-bool-∨-c false b' (inj₂ y)  = y

{- Propositional logic introduction / elimination rules -}

∨-introl : (a b : Bool) → T a → T (a ∨ᵇ b)
∨-introl true  _ p = p
∨-introl false _ ()

∨-intror : (a b : Bool) → T b → T (a ∨ᵇ b)
∨-intror true  true  p = p
∨-intror false true  p = p
∨-intror _     false ()

∨-elim : ∀ {C : Set} → {a b : Bool} → (T a → C) → (T b → C) → T (a ∨ᵇ b) → C
∨-elim {_} {a} {b} f g p = [ f , g ]′ (lem-bool-∨-s a b p)

∧-elim : {C : Set} → {a b : Bool} → (T a → T b → C) → T (a ∧ᵇ b) → C
∧-elim {C} {a} {b} f p = uncurry′ f (lem-bool-∧-s a b p)

∧-swap : ∀ a b → T (a ∧ᵇ b) → T (b ∧ᵇ a)
∧-swap true  true  = id
∧-swap true  false = id
∧-swap false true  = id
∧-swap false false = id

∨-swap : ∀ a b → T (a ∨ᵇ b) → T (b ∨ᵇ a)
∨-swap true  true  = id
∨-swap true  false = id
∨-swap false true  = id
∨-swap false false = id

f∨g : {a b c d : Bool} → (T a → T c) → (T b → T d) → T (a ∨ᵇ b) → T (c ∨ᵇ d)
f∨g {a} {b} {c} {d} f g = ∨-elim (λ p → ∨-introl c d (f p)) (λ p → ∨-intror c d (g p))

∧-intro : (a b : Bool) → T a → T b → T (a ∧ᵇ b)
∧-intro true  true  c  d = tt
∧-intro true  false c  ()
∧-intro false b     () d

∧-eliml : {a b : Bool} → T (a ∧ᵇ b) → T a
∧-eliml {true}  p = tt
∧-eliml {false} ()

∧-elimr : (a : Bool) → {b : Bool} → T (a ∧ᵇ b) → T b
∧-elimr a     {true}  p = tt
∧-elimr true  {false} ()
∧-elimr false {false} ()

f∧g : {a b c d : Bool} → (T a → T c) → (T b → T d) → T (a ∧ᵇ b) → T (c ∧ᵇ d)
f∧g {a} {b} {c} {d} f g p = ∧-intro c d (f (∧-eliml p)) (g (∧-elimr a p))

¬[p∧¬p] : (b : Bool) → ¬ (T b × T (not b))
¬[p∧¬p] true  = proj₂
¬[p∧¬p] false = proj₁

ex-mid : (a : Bool) → T a ⊎ ¬ T a
ex-mid true  = inj₁ tt
ex-mid false = inj₂ id

_⟶_ : Bool → Bool → Bool
true  ⟶ b = b
false ⟶ b = true

lem-⟶-s : (a b : Bool) → T (a ⟶ b) → T a → T b
lem-⟶-s true  b p pa = p
lem-⟶-s false b p pa = ⊥-elim pa

lem-⟶-c : (a b : Bool) → (T a → T b) → T (a ⟶ b)
lem-⟶-c true  b p = p tt
lem-⟶-c false b p = tt

lem-→-intro : (a b : Bool) → T (not a ∨ᵇ b) → T a → T b
lem-→-intro a b p ta = ∨-elim (\ x → ⊥-elim (¬[p∧¬p] a (ta , x))) id p

lem-→-elim : (a b : Bool) → (T a → T b) → T (not a ∨ᵇ b)
lem-→-elim true  b f = f tt
lem-→-elim false b f = tt

lem-→ : {A B : Set} → ¬ A ⊎ B → A → B
lem-→ = [ (λ x x' → ⊥-elim (x x')) , (λ z _ → z) ]′

lem-⊎ : {A : Set} {B : Set} {C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
lem-⊎ (inj₁ (inj₁ x)) = inj₁ x
lem-⊎ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
lem-⊎ (inj₂ y)        = inj₂ (inj₂ y)

demorg1 : ∀ a b → T (not (a ∨ᵇ b)) → T ((not a) ∧ᵇ (not b))
demorg1 true  b p = p
demorg1 false b p = p

demorg2 : ∀ a b → T ((not a) ∧ᵇ (not b)) → T (not (a ∨ᵇ b))
demorg2 true  b ¬ab = ¬ab
demorg2 false b ¬ab = ¬ab

¬∃ : ∀ {A : Set} → (P : A → Set) → ¬ ∃ P → ∀ x → ¬ P x
¬∃ P ¬ep x px = ¬ep (-, px)

Tb : ∀ {b} → T b → b ≡ true
Tb {true}  tt = refl
Tb {false} ()

¬Tb : ∀ {b} → ¬ T b → b ≡ false
¬Tb {true}  x = ⊥-elim (x tt)
¬Tb {false} x = refl

trans-≡ᵇ : ∀ k l m → T (k ≡ᵇ l) → T (l ≡ᵇ m) → T (k ≡ᵇ m)
trans-≡ᵇ zero    l        zero     k=l l=m = tt
trans-≡ᵇ zero    zero     (suc n)  k=l l=m = l=m
trans-≡ᵇ zero    (suc n)  (suc n') k=l l=m = k=l
trans-≡ᵇ (suc n) zero     zero     k=l l=m = k=l
trans-≡ᵇ (suc n) (suc n') zero     k=l l=m = l=m
trans-≡ᵇ (suc n) zero     (suc n') k=l l=m = ⊥-elim l=m
trans-≡ᵇ (suc n) (suc n') (suc n0) k=l l=m = trans-≡ᵇ n n' n0 k=l l=m

sym-≡ᵇ : ∀ k l → T (k ≡ᵇ l) → T (l ≡ᵇ k)
sym-≡ᵇ zero    zero    = id
sym-≡ᵇ zero    (suc l) = id
sym-≡ᵇ (suc k) zero    = id
sym-≡ᵇ (suc k) (suc l) = sym-≡ᵇ k l

lift-≡ᵇ : ∀ n m → T (n ≡ᵇ m) → n ≡ m
lift-≡ᵇ zero    zero    p = refl
lift-≡ᵇ (suc n) (suc m) p = cong suc (lift-≡ᵇ n m p)
lift-≡ᵇ zero    (suc m) ()
lift-≡ᵇ (suc n) zero    ()

id-≡ᵇ : ∀ n → T (n ≡ᵇ n)
id-≡ᵇ zero    = tt
id-≡ᵇ (suc n) = id-≡ᵇ n

+r-≡ᵇ : ∀ n m → ¬ T (n ≡ᵇ (n + (suc m)))
+r-≡ᵇ zero    m = id
+r-≡ᵇ (suc n) m = +r-≡ᵇ n m

+-comm : ∀ n m → n + m ≡ m + n
+-comm n m = comm (+-isCommutativeMonoid +-*-isCommutativeSemiring) n m

+l-≡ᵇ : ∀ n m → ¬ T (n ≡ᵇ ((suc m) + n))
+l-≡ᵇ zero    m = id
+l-≡ᵇ (suc n) m rewrite +-comm m (suc n)
                      | +-comm n m
  = +l-≡ᵇ n m

<ᵇ-ord : ∀ n → T (n <ᵇ suc n)
<ᵇ-ord zero    = tt
<ᵇ-ord (suc n) = <ᵇ-ord n

<ᵇ-trans : ∀ k l m → T (k <ᵇ suc l) → T (l <ᵇ suc m) → T (k <ᵇ suc m)
<ᵇ-trans zero    l        m        k<ᵇl l<ᵇm = tt
<ᵇ-trans (suc n) zero     zero     k<ᵇl l<ᵇm = ⊥-elim k<ᵇl
<ᵇ-trans (suc n) (suc n') zero     k<ᵇl l<ᵇm = ⊥-elim l<ᵇm
<ᵇ-trans (suc n) zero     (suc n') k<ᵇl l<ᵇm = ⊥-elim k<ᵇl
<ᵇ-trans (suc n) (suc n') (suc n0) k<ᵇl l<ᵇm = <ᵇ-trans n n' n0 k<ᵇl l<ᵇm

<ᵇ-lsuc : ∀ n m → T (suc n <ᵇ m) → T (n <ᵇ m)
<ᵇ-lsuc zero    zero     p = ⊥-elim p
<ᵇ-lsuc zero    (suc n)  p = tt
<ᵇ-lsuc (suc n) zero     p = ⊥-elim p
<ᵇ-lsuc (suc n) (suc n') p = <ᵇ-lsuc n n' p

<ᵇ-rsuc : ∀ n m → T (n <ᵇ m) → T (n <ᵇ suc m)
<ᵇ-rsuc zero    zero     p = ⊥-elim p
<ᵇ-rsuc zero    (suc n)  p = tt
<ᵇ-rsuc (suc n) zero     p = ⊥-elim p
<ᵇ-rsuc (suc n) (suc n') p = <ᵇ-rsuc n n' p

<ᵇ-trans' : ∀ k l m → T (k <ᵇ l) → T (l <ᵇ m) → T (suc k <ᵇ m)
<ᵇ-trans' k       l       zero          p q = ⊥-elim q
<ᵇ-trans' k       zero    (suc m)       p q = ⊥-elim p
<ᵇ-trans' zero    (suc l) (suc zero)    p q = q
<ᵇ-trans' zero    (suc l) (suc (suc m)) p q = tt
<ᵇ-trans' (suc k) (suc l) (suc m)       p q = <ᵇ-trans' k l m p q

<ᵇ-¬ : ∀ n m → ¬ T (n <ᵇ m) → T (m <ᵇ suc n)
<ᵇ-¬ zero    zero     p = tt
<ᵇ-¬ zero    (suc n)  p = p tt
<ᵇ-¬ (suc n) zero     p = tt
<ᵇ-¬ (suc n) (suc n') p = <ᵇ-¬ n n' p

<ᵇ-¬' : ∀ n m → T (n <ᵇ m) → ¬ T (m <ᵇ suc n)
<ᵇ-¬' n       zero    p = const p
<ᵇ-¬' zero    (suc m) p = id
<ᵇ-¬' (suc n) (suc m) p = <ᵇ-¬' n m p

<ᵇ→≠ : ∀ n m → T (n <ᵇ m) → ¬ T (n ≡ᵇ m)
<ᵇ→≠ n       zero    p = const p
<ᵇ→≠ zero    (suc m) p = λ ()
<ᵇ→≠ (suc n) (suc m) p = <ᵇ→≠ n m p

<ᵇ→≢ : ∀ n m → T (n <ᵇ m) → n ≢ m
<ᵇ→≢ n zero p = const p
<ᵇ→≢ zero (suc m) p = λ ()
<ᵇ→≢ (suc n) (suc m) p = <ᵇ→≢ n m p ∘ (cong pred)

<ᵇ-weaken : ∀ n m l → T (n <ᵇ m) → T (n <ᵇ (m + l))
<ᵇ-weaken n       zero    l = ⊥-elim
<ᵇ-weaken zero    (suc m) l = id
<ᵇ-weaken (suc n) (suc m) l = <ᵇ-weaken n m l

<ᵇ-¬refl : ∀ n → ¬ T (n <ᵇ n)
<ᵇ-¬refl zero    ()
<ᵇ-¬refl (suc n) p = <ᵇ-¬refl n p

<ᵇ¬-weaken : ∀ n m k → ¬ T (n <ᵇ m) → ¬ T ((n + k) <ᵇ m)
<ᵇ¬-weaken n       zero    k ¬n<ᵇm n+k<ᵇm = n+k<ᵇm
<ᵇ¬-weaken zero    (suc m) k ¬n<ᵇm n+k<ᵇm = ¬n<ᵇm tt
<ᵇ¬-weaken (suc n) (suc m) k ¬n<ᵇm n+k<ᵇm = <ᵇ¬-weaken n m k ¬n<ᵇm n+k<ᵇm


<ᵇ-+-rsuc : ∀ n m l → T ((n + suc m) <ᵇ suc l) → T ((n + m) <ᵇ l)
<ᵇ-+-rsuc zero    m l       p = p
<ᵇ-+-rsuc (suc n) m zero    p = p
<ᵇ-+-rsuc (suc n) m (suc l) p = <ᵇ-+-rsuc n m l p

max : ℕ → ℕ → ℕ
max n m with n <ᵇ m
...| true = m
...| false = n

elim-max : ∀ n m → (P : ℕ → Set) → (fn : ¬ T (n <ᵇ m) → P n) → (fm : T (n <ᵇ m) → P m) →  P (max n m)
elim-max n m P fn fm with n <ᵇ m
...| true = fm tt
...| false = fn id

cong' : ∀ {k m l} {A : Set k} (B : A → Set l) {C : Set m}
      → (F : (a : A) → B a → C)
      → {a a' : A}
      → (eq : a ≡ a')
      → (b : B a)
      → F a b ≡ F a' (subst B eq b)
cong' B F refl b = refl

assembleℕ : (f g : ℕ → Set) → (f 0 → g 0) → ({n : ℕ} → f (suc n) → g (suc n)) → {m : ℕ} → f m → g m
assembleℕ f g bc ih {zero}  = bc
assembleℕ f g bc ih {suc m} = ih
