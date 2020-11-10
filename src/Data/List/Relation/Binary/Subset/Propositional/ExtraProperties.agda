
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Level
open import Data.List.Relation.Binary.Permutation.Propositional
import Data.List.Relation.Binary.Permutation.Propositional.Properties as Perm

module Data.List.Relation.Binary.Subset.Propositional.ExtraProperties where

private
  variable
    a : Level
    A : Set a
    x y : A
    xs ys ws zs : List A

xs⊆xs++ys : xs ⊆ xs ++ ys
xs⊆xs++ys = ∈-++⁺ˡ

xs⊆ys++xs : xs ⊆ ys ++ xs
xs⊆ys++xs = ∈-++⁺ʳ _

++⁺ʳ : ∀ zs → xs ⊆ ys → zs ++ xs ⊆ zs ++ ys
++⁺ʳ zs xs⊆ys = ⊆-refl {x = zs} ++-mono xs⊆ys

++⁺ˡ : ∀ zs → xs ⊆ ys → xs ++ zs ⊆ ys ++ zs
++⁺ˡ zs xs⊆ys = xs⊆ys ++-mono ⊆-refl {x = zs}

++↭ʳ++ : ∀ (xs ys : List A) → xs ++ ys ↭ xs ʳ++ ys
++↭ʳ++ []       ys = ↭-refl
++↭ʳ++ (x ∷ xs) ys = ↭-trans (↭-sym (Perm.shift x xs ys)) (++↭ʳ++ xs (x ∷ ys))

↭⇒⊆ : xs ↭ ys → xs ⊆ ys
↭⇒⊆ xs↭ys = Perm.Any-resp-↭ xs↭ys
