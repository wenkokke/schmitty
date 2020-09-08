module Kanso.Boolean.Formula.RemoveConstants where

open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Product as Prod using (_×_; proj₁; proj₂; _,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit as Unit using (⊤; tt)
open import Function using (id; const; _∘_)

open import Kanso.Boolean.Formula
open import Kanso.PropIso

map-or : PL-Formula → PL-Formula → PL-Formula
map-or ¥true  b      = ¥true
map-or ¥false b      = b
map-or a      ¥true  = ¥true
map-or a      ¥false = a
map-or a      b      = a || b

map-and : PL-Formula → PL-Formula → PL-Formula
map-and ¥true  b      = b
map-and ¥false b      = ¥false
map-and a      ¥true  = a
map-and a      ¥false = ¥false
map-and a      b      = a && b

map-iff : PL-Formula → PL-Formula → PL-Formula
map-iff ¥true  b      = b
map-iff ¥false b      = ¥true
map-iff a      ¥true  = ¥true
map-iff a      ¥false = ~ a
map-iff a      b      = a => b

const-removal : PL-Formula → PL-Formula
const-removal = elim-pl ¥true ¥false ¥ map-or map-and map-iff

lem-map-or : ∀ ξ φ ψ → ⟦ ξ ⊧ φ || ψ ⟧pl → ⟦ ξ ⊧ map-or φ ψ ⟧pl
lem-map-or ξ ¥true = λ _ _ → tt
lem-map-or ξ ¥false = λ _ → [ (λ ()) , id ]′
lem-map-or ξ (φ || ψ) = λ {¥true → const tt; ¥false → [ id , (λ ()) ]′; (ψ' || ψ'') → id;
                             (ψ' && ψ'') → id ; (ψ' => ψ'') → id ; (¥ x) → id }
lem-map-or ξ (φ && ψ) = λ {¥true → const tt; ¥false → [ id , (λ ()) ]′; (ψ' || ψ'') → id;
                             (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}
lem-map-or ξ (φ => ψ) = λ {¥true → const tt; ¥false → [ id , (λ ()) ]′; (ψ' || ψ'') → id;
                             (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}
lem-map-or ξ (¥ x) = λ {¥true → const tt; ¥false → [ id , (λ ()) ]′; (ψ' || ψ'') → id;
                          (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}

lem-map-or' : ∀ ξ φ ψ → ⟦ ξ ⊧ map-or φ ψ ⟧pl → ⟦ ξ ⊧ φ || ψ ⟧pl
lem-map-or' ξ ¥true = λ _ → inj₁
lem-map-or' ξ ¥false = λ _ → inj₂
lem-map-or' ξ (φ || φ₁) = λ {¥true → inj₂; ¥false → inj₁; (ψ' || ψ'') → id; (ψ' && ψ'') → id;
                               (ψ' => ψ'') → id; (¥ x) → id}
lem-map-or' ξ (φ && φ₁) = λ {¥true → inj₂; ¥false → inj₁; (ψ' || ψ'') → id; (ψ' && ψ'') → id;
                               (ψ' => ψ'') → id; (¥ x) → id}
lem-map-or' ξ (φ => φ₁) = λ {¥true → inj₂; ¥false → inj₁; (ψ' || ψ'') → id; (ψ' && ψ'') → id;
                               (ψ' => ψ'') → id; (¥ x) → id}
lem-map-or' ξ (¥ x) = λ {¥true → inj₂; ¥false → inj₁; (ψ' || ψ'') → id; (ψ' && ψ'') → id;
                           (ψ' => ψ'') → id; (¥ x) → id}

lem-map-and : ∀ ξ φ ψ → ⟦ ξ ⊧ φ && ψ ⟧pl → ⟦ ξ ⊧ map-and φ ψ ⟧pl
lem-map-and ξ ¥true = λ _ → proj₂
lem-map-and ξ ¥false = λ _ → proj₁
lem-map-and ξ (φ || φ₁) = λ {¥true → proj₁; ¥false → proj₂; (ψ' || ψ'') → id;
                               (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}
lem-map-and ξ (φ && φ₁) = λ {¥true → proj₁; ¥false → proj₂; (ψ' || ψ'') → id;
                               (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}
lem-map-and ξ (φ => φ₁) = λ {¥true → proj₁; ¥false → proj₂; (ψ' || ψ'') → id;
                               (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}
lem-map-and ξ (¥ x) = λ {¥true → proj₁; ¥false → proj₂; (ψ' || ψ'') → id;
                           (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}

lem-map-and' : ∀ ξ φ ψ → ⟦ ξ ⊧ map-and φ ψ ⟧pl → ⟦ ξ ⊧ φ && ψ ⟧pl
lem-map-and' ξ ¥true = λ _ x → _ , x
lem-map-and' ξ ¥false = λ _ → λ ()
lem-map-and' ξ (φ || φ₁) = λ {¥true → λ x → x , _; ¥false → λ (); (ψ' || ψ'') → id;
                                (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}
lem-map-and' ξ (φ && φ₁) = λ {¥true → λ x → x , _; ¥false → λ (); (ψ' || ψ'') → id;
                                (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}
lem-map-and' ξ (φ => φ₁) = λ {¥true → λ x → x , _; ¥false → λ (); (ψ' || ψ'') → id;
                                (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}
lem-map-and' ξ (¥ x) = λ {¥true → λ x₁ → x₁ , _; ¥false → λ (); (ψ' || ψ'') → id;
                            (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}

lem-map-iff : ∀ ξ φ ψ → ⟦ ξ ⊧ φ => ψ ⟧pl → ⟦ ξ ⊧ map-iff φ ψ ⟧pl
lem-map-iff ξ ¥true = λ _ x → x tt
lem-map-iff ξ ¥false = λ _ _ → tt
lem-map-iff ξ (φ || φ₁) = λ {¥true → λ _ → tt; ¥false → id; (ψ' || ψ'') → id;
                               (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}
lem-map-iff ξ (φ && φ₁) = λ {¥true → λ _ → tt; ¥false → id; (ψ' || ψ'') → id;
                               (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}
lem-map-iff ξ (φ => φ₁) = λ {¥true → λ _ → tt; ¥false → id; (ψ' || ψ'') → id;
                               (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}
lem-map-iff ξ (¥ x) = λ {¥true → λ _ → tt; ¥false → id; (ψ' || ψ'') → id;
                           (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}

lem-map-iff' : ∀ ξ φ ψ → ⟦ ξ ⊧ map-iff φ ψ ⟧pl → ⟦ ξ ⊧ φ => ψ ⟧pl
lem-map-iff' ξ ¥true = λ _ x _ → x
lem-map-iff' ξ ¥false = λ _ _ → λ ()
lem-map-iff' ξ (φ || φ₁) = λ {¥true → λ x _ → x; ¥false → id; (ψ' || ψ'') → id;
                                (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}
lem-map-iff' ξ (φ && φ₁) = λ {¥true → λ x _ → x; ¥false → id; (ψ' || ψ'') → id;
                                (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}
lem-map-iff' ξ (φ => φ₁) = λ {¥true → λ x _ → x; ¥false → id; (ψ' || ψ'') → id;
                                (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}
lem-map-iff' ξ (¥ x) = λ {¥true → λ x₁ _ → x₁; ¥false → id; (ψ' || ψ'') → id;
                            (ψ' && ψ'') → id; (ψ' => ψ'') → id; (¥ x) → id}

mutual
  lem-no-const : ∀ ξ φ → ⟦ ξ ⊧ φ ⟧pl → ⟦ ξ ⊧ const-removal φ ⟧pl
  lem-no-const ξ ¥true p = p
  lem-no-const ξ ¥false p = p
  lem-no-const ξ (φ || ψ) p = lem-map-or ξ (const-removal φ) _ (Sum.map (lem-no-const ξ φ)
                                                                        (lem-no-const ξ ψ) p)
  lem-no-const ξ (φ && ψ) p = lem-map-and ξ (const-removal φ) _ (Prod.map (lem-no-const ξ φ)
                                                                          (lem-no-const ξ ψ) p)
  lem-no-const ξ (φ => ψ) p = lem-map-iff ξ (const-removal φ) _ (lem-no-const ξ ψ ∘ p ∘
                                                                         lem-no-const' ξ φ)
  lem-no-const ξ (¥ v) p = p

  lem-no-const' : ∀ ξ φ → ⟦ ξ ⊧ const-removal φ ⟧pl → ⟦ ξ ⊧ φ ⟧pl
  lem-no-const' ξ ¥true p = p
  lem-no-const' ξ ¥false p = p
  lem-no-const' ξ (φ || ψ) p = Sum.map (lem-no-const' ξ φ) (lem-no-const' ξ ψ)
                                       (lem-map-or' ξ (const-removal φ) _ p)
  lem-no-const' ξ (φ && ψ) p = Prod.map (lem-no-const' ξ φ) (lem-no-const' ξ ψ)
                                        (lem-map-and' ξ (const-removal φ) _ p)
  lem-no-const' ξ (φ => ψ) p = lem-no-const' ξ ψ ∘ lem-map-iff' ξ (const-removal φ) _ p ∘
                                    lem-no-const ξ φ
  lem-no-const' ξ (¥ v) p = p
