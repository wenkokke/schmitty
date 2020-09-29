
module Reflection.Annotated.Free where

open import Data.Bool using (if_then_else_)
open import Data.Nat
open import Data.List
open import Data.List.Relation.Unary.All as All using (All; _∷_; [])
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit
open import Function
open import Reflection
open import Reflection.Argument.Visibility

open import Reflection.Universe
open import Reflection.Annotated

private
  variable
    k : Univ

-- Free variable annotations --

FVs : Set
FVs = List ℕ -- ordered, no duplicates

FV : ∀ {k} → ⟦ k ⟧ → Set
FV _ = FVs

private

  infixr 3 _∪_

  _∪_ : FVs → FVs → FVs
  []     ∪ ys = ys
  xs     ∪ [] = xs
  x ∷ xs ∪ y ∷ ys with compare x y | x ∷ xs ∪ ys
  ... | less    x _ | _   = x ∷ (xs ∪ y ∷ ys)
  ... | equal   x   | _   = x ∷ (xs ∪ ys)
  ... | greater y _ | rec = y ∷ rec

  insert : ℕ → FVs → FVs
  insert x []       = x ∷ []
  insert x (y ∷ xs) with compare x y
  ... | less    x k = x ∷ y ∷ xs
  ... | equal   x   = y ∷ xs
  ... | greater y k = y ∷ insert x xs

  close : ℕ → FVs → FVs
  close k = concatMap λ x → if x <ᵇ k then [] else [ x ∸ k ]

freeVars : AnnotationFun FV
freeVars ⟨term⟩    (var x (⟨ fv ⟩ _))                                      = insert x fv
freeVars ⟨pat⟩     (var x)                                                 = x ∷ []
freeVars ⟨clause⟩  (clause {tel = Γ} (⟨ fvΓ ⟩ _) (⟨ fvps ⟩ _) (⟨ fvt ⟩ _)) = fvΓ ∪ close (length Γ) (fvps ∪ fvt)
freeVars ⟨clause⟩  (absurd-clause {tel = Γ} (⟨ fvΓ ⟩ _) (⟨ fvps ⟩ _))      = fvΓ ∪ close (length Γ) fvps
freeVars (⟨list⟩ (⟨named⟩ _)) (⟨ fv ⟩ _ ∷ xs)                               = fv ∪ close 1 (freeVars _ xs) -- telescope case
freeVars k t = defaultAnn [] _∪_ k t
