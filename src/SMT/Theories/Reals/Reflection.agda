module SMT.Theories.Reals.Reflection where

open import Data.Bool.Base as Bool using (Bool; false; true; if_then_else_)
open import Data.Integer as Int using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Float as Float using (Float)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat as Nat using (ℕ)
import Data.Nat.Show as Nat using (show)
open import Data.List as List using (List; []; _∷_)
open import Data.Product as Prod using (Σ-syntax; _×_; _,_)
open import Data.String as String using (String)
open import Function.Equivalence using (equivalence)
open import Relation.Nullary using (Dec; yes; no)
import Reflection as Rfl
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong)
open import SMT.Theory
open import SMT.Theory.Reflection
open import SMT.Theories.Core as Core hiding (BOOL)
open import SMT.Theories.Core.Extensions
open import SMT.Theories.Reals.Base as Reals
open import SMT.Script.Base Reals.baseTheory
import SMT.Utils.Float as Float


-----------
-- Sorts --
-----------

sorts : List Sort
sorts = REAL ∷ List.map CORE coreSorts


checkSort : Rfl.Term → Maybe Sort
checkSort (Rfl.def (quote Float) []) = just REAL
checkSort t                          = Maybe.map CORE (checkCoreSort t)


--------------
-- Literals --
--------------

private
  pattern `float  f = Rfl.float f

checkLiteral : (σ : Sort) → Rfl.Literal → Maybe (Literal σ)
checkLiteral (CORE φ) x          = Maybe.map core (checkCoreLiteral φ x)
checkLiteral REAL     (`float f) = just (float f)
checkLiteral REAL     _          = nothing


-----------------
-- Identifiers --
-----------------

private
  pattern `eq  = quote Eq._≡_
  pattern `neq = quote Eq._≢_
  -- NOTE: We're interpreting BOOL to be Set. Unfortunately, that means that `ite`
  --       cannot really be given a sensible interpretation. (Unless, perhaps, we
  --       involve Dec.)
  --
  -- pattern `ite = ?
  pattern `neg = quote Float.-_
  pattern `sub = quote Float._-_
  pattern `add = quote Float._+_
  pattern `mul = quote Float._*_
  pattern `div = quote Float._÷_
  -- NOTE: Float modulo is currently not defined in the standard library, so we
  --       don't map them here.
  --
  -- pattern `mod = ?
  --
  -- NOTE: Float relations are currently not defined in the standard library, so
  --       provide quick and dirty definitions in SMT.Utils.Float, which are
  --       mapped below. These should be replaced once proper orderings on Float
  --       become available in the standard library.
  pattern `leq = quote Float._≤_
  pattern `lt  = quote Float._<_
  pattern `geq = quote Float._≥_
  pattern `gt  = quote Float._>_

checkIdentifier : (σ : Sort) → Rfl.Name → Maybe (Σ[ Σ ∈ Signature σ ] Macro Σ)
checkIdentifier BOOL     `eq  = just (Rel REAL , app eq)
checkIdentifier BOOL     `neq = just (Rel REAL , app neq)
checkIdentifier REAL     `neg = just (Op₁ REAL , app neg)
checkIdentifier REAL     `sub = just (Op₂ REAL , app sub)
checkIdentifier REAL     `add = just (Op₂ REAL , app add)
checkIdentifier REAL     `mul = just (Op₂ REAL , app mul)
checkIdentifier REAL     `div = just (Op₂ REAL , app div)
checkIdentifier BOOL     `leq = just (Rel REAL , app leq)
checkIdentifier BOOL     `lt  = just (Rel REAL , app lt)
checkIdentifier BOOL     `geq = just (Rel REAL , app geq)
checkIdentifier BOOL     `gt  = just (Rel REAL , app gt)
checkIdentifier REAL      _   = nothing
checkIdentifier (CORE φ)  x   =
  Maybe.map (Prod.map liftCoreSignature (λ i → app (core i))) (checkCoreIdentifier′ φ x)


---------------
-- Instances --
---------------

reflectable : Reflectable theory
Reflectable.sorts           reflectable = sorts
Reflectable.checkSort       reflectable = checkSort
Reflectable.checkLiteral    reflectable = checkLiteral
Reflectable.checkIdentifier reflectable = checkIdentifier
