module SMT.Term.Example where

open import Data.Empty using (⊥)
open import Data.Fin using (suc; zero)
open import Data.List using (List; _∷_; [])
open import Data.String using (String)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Sort : Set
Sort = ⊤

pattern Bool = tt

data Literal : Sort → Set where
  true  : Literal Bool
  false : Literal Bool

data Identifier : List Sort → Sort → Set where
  not     : Identifier (Bool ∷ [])        Bool
  and     : Identifier (Bool ∷ Bool ∷ []) Bool
  or      : Identifier (Bool ∷ Bool ∷ []) Bool
  xor     : Identifier (Bool ∷ Bool ∷ []) Bool
  implies : Identifier (Bool ∷ Bool ∷ []) Bool

showSort : Sort → String
showSort Bool = "Bool"

showLiteral : ∀ {σ} (l : Literal σ) → String
showLiteral true  = "true"
showLiteral false = "false"

showIdentifier : ∀ {Σ} {σ} (x : Identifier Σ σ) → String
showIdentifier not     = "not"
showIdentifier and     = "and"
showIdentifier or      = "or"
showIdentifier xor     = "xor"
showIdentifier implies = "=>"

open import SMT.Term Sort Bool Literal Identifier
open import SMT.Term.Show Sort Bool Literal Identifier showSort showLiteral showIdentifier

=> : ∀ {Γ} → Term Γ Bool → Term Γ Bool → Term Γ Bool
=> x y = app implies (x ∷ y ∷ [])

example₁ : Term [] Bool
example₁ = (forAll (forAll ((=> (=> (=> P Q) P) P))))
  where
    P = var (suc zero , refl)
    Q = var (    zero , refl)


test_example₁ : showTerm x′es example₁
              ≡ "(forall (x0 Bool) (forall (x1 Bool) (=> (=> (=> x0 x1) x0) x0)))"
test_example₁ = refl
