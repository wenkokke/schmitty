module Kanso.Boolean.Formula.Distribute where

open import Kanso.Boolean.Formula

open import Data.Product as Prod using (_×_; proj₁; proj₂; _,_; uncurry)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (_∘_)

-- dist-clause-∨ : CLAUSE → CNF → CNF
dist-clause-∨ : PL-Formula → PL-Formula → PL-Formula
dist-clause-∨ cl (φ && ψ) = dist-clause-∨ cl φ && dist-clause-∨ cl ψ
dist-clause-∨ cl φ = cl || φ

-- dist-∨ : CNF → CNF → CNF
dist-∨ : PL-Formula → PL-Formula → PL-Formula
dist-∨ (φ && φ') ψ = dist-∨ φ ψ && dist-∨ φ' ψ
dist-∨ cl ψ = dist-clause-∨ cl ψ

mkdist : PL-Formula → PL-Formula
mkdist (φ || ψ) = dist-∨ (mkdist φ) (mkdist ψ)
mkdist (φ && ψ) = mkdist φ && mkdist ψ
mkdist φ = φ

lem-dist-clause-∨ : ∀ ξ cl φ → ⟦ ξ ⊧ cl || φ ⟧pl → ⟦ ξ ⊧ dist-clause-∨ cl φ ⟧pl
lem-dist-clause-∨ ξ cl ¥true p = p
lem-dist-clause-∨ ξ cl ¥false p = p
lem-dist-clause-∨ ξ cl (y || y') p = p
lem-dist-clause-∨ ξ cl (y && y') p
  = [ (λ x → (lem-dist-clause-∨ ξ cl y (inj₁ x)) , (lem-dist-clause-∨ ξ cl y' (inj₁ x)))
    , (λ x → lem-dist-clause-∨ ξ cl y (inj₂ (proj₁ x))
             , lem-dist-clause-∨ ξ cl y' (inj₂ (proj₂ x))) ]′ p
lem-dist-clause-∨ ξ cl (y => y') p = p
lem-dist-clause-∨ ξ cl (¥ y) p = p

lem-dist-clause-∨' : ∀ ξ cl φ → ⟦ ξ ⊧ dist-clause-∨ cl φ ⟧pl → ⟦ ξ ⊧ cl || φ ⟧pl
lem-dist-clause-∨' ξ cl ¥true p = p
lem-dist-clause-∨' ξ cl ¥false p = p
lem-dist-clause-∨' ξ cl (y || y') p = p
lem-dist-clause-∨' ξ cl (y && y') p
  = uncurry (λ [y] [y'] → [ inj₁ , (λ [y]' → [ inj₁ , (λ [y']' → inj₂ ([y]' , [y']'))
                                             ]′ (lem-dist-clause-∨' ξ cl y' [y']))
                          ]′ (lem-dist-clause-∨' ξ cl y [y])) p
lem-dist-clause-∨' ξ cl (y => y') p = p
lem-dist-clause-∨' ξ cl (¥ y) p = p

lem-dist-∨ : ∀ ξ φ ψ → ⟦ ξ ⊧ φ || ψ ⟧pl → ⟦ ξ ⊧ dist-∨ φ ψ ⟧pl
lem-dist-∨ ξ ¥true = lem-dist-clause-∨ ξ ¥true
lem-dist-∨ ξ ¥false = lem-dist-clause-∨ ξ ¥false
lem-dist-∨ ξ (y || y') = lem-dist-clause-∨ ξ (y || y')
lem-dist-∨ ξ (y && y') =
  λ ψ → [ Prod.map (lem-dist-∨ ξ y ψ ∘ inj₁) (lem-dist-∨ ξ y' ψ ∘ inj₁) ,
          (λ x → (lem-dist-∨ ξ y ψ (inj₂ x)) , (lem-dist-∨ ξ y' ψ (inj₂ x))) ]′
lem-dist-∨ ξ (y => y') = lem-dist-clause-∨ ξ (y => y')
lem-dist-∨ ξ (¥ y) = lem-dist-clause-∨ ξ (¥ y)

lem-dist-∨' : ∀ ξ φ ψ → ⟦ ξ ⊧ dist-∨ φ ψ ⟧pl → ⟦ ξ ⊧ φ || ψ ⟧pl
lem-dist-∨' ξ ¥true = lem-dist-clause-∨' ξ ¥true
lem-dist-∨' ξ ¥false = lem-dist-clause-∨' ξ ¥false
lem-dist-∨' ξ (y || y') = lem-dist-clause-∨' ξ (y || y')
lem-dist-∨' ξ (y && y')
  = λ ψ → uncurry (λ [y]' [y']' → [ (\ [y] → [ (λ [y'] → inj₁ ([y] , [y'])) , inj₂
                                             ]′ (lem-dist-∨' ξ y' ψ [y']')) , inj₂
                                  ]′ (lem-dist-∨' ξ y ψ [y]'))
lem-dist-∨' ξ (y => y') = lem-dist-clause-∨' ξ (y => y')
lem-dist-∨' ξ (¥ y) = lem-dist-clause-∨' ξ (¥ y)

lem-mkdist : ∀ ξ φ → ⟦ ξ ⊧ φ ⟧pl → ⟦ ξ ⊧ mkdist φ ⟧pl
lem-mkdist ξ ¥true p = p
lem-mkdist ξ ¥false p = p
lem-mkdist ξ (y || y') p = lem-dist-∨ ξ (mkdist y) (mkdist y')
                                        (Sum.map (lem-mkdist ξ y) (lem-mkdist ξ y') p)
lem-mkdist ξ (y && y') p = Prod.map (lem-mkdist ξ y) (lem-mkdist ξ y') p
lem-mkdist ξ (y => y') p = p
lem-mkdist ξ (¥ y) p = p

lem-mkdist' : ∀ ξ φ → ⟦ ξ ⊧ mkdist φ ⟧pl → ⟦ ξ ⊧ φ ⟧pl
lem-mkdist' ξ ¥true p = p
lem-mkdist' ξ ¥false p = p
lem-mkdist' ξ (y || y') p = Sum.map (lem-mkdist' ξ y) (lem-mkdist' ξ y')
                                    (lem-dist-∨' ξ (mkdist y) (mkdist y') p)
lem-mkdist' ξ (y && y') p = Prod.map (lem-mkdist' ξ y) (lem-mkdist' ξ y') p
lem-mkdist' ξ (y => y') p = p
lem-mkdist' ξ (¥ y) p = p
