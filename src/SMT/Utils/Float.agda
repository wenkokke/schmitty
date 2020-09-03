module SMT.Utils.Float where

open import Data.Bool as Bool using (Bool; false; true; T; not; _∧_)
open import Data.Float as Float using (Float; isNaN; _≤ᵇ_; _<ᵇ_)
open import Data.Product as Prod using (_×_)
open import Function using (flip)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel)

IsNaN : Float → Set
IsNaN x = T (isNaN x)

_≤_ : Rel Float _
x ≤ y = ¬ (IsNaN x) × ¬ (IsNaN x) × T (x ≤ᵇ y)

_<_ : Rel Float _
x < y = ¬ (IsNaN x) × ¬ (IsNaN x) × T (x <ᵇ y)

_≥_ : Rel Float _
_≥_ = flip _≤_

_>_ : Rel Float _
_>_ = flip _<_
