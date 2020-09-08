module SMT.Theories.Ints.Reflection where


open import Data.Integer as Int using (ℤ; +_; -[1+_]) renaming (show to showℤ)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat.Base as Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List as List using (List; _∷_; [])
open import Data.Product as Prod using (Σ-syntax; _,_)
import Reflection as Rfl
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)
open import SMT.Theory
open import SMT.Theory.Reflection
open import SMT.Theories.Core as Core hiding (BOOL)
open import SMT.Theories.Core.Extensions
open import SMT.Theories.Ints.Base as Ints
open import SMT.Script.Base Ints.baseTheory


-----------
-- Sorts --
-----------

sorts : List Sort
sorts = INT ∷ List.map CORE coreSorts


--------------
-- Literals --
--------------

private
  pattern `nat    n = Rfl.lit (Rfl.nat n)
  pattern `+_     n = Rfl.con (quote +_) (Rfl.vArg (`nat n) ∷ [])
  pattern `-[1+_] n = Rfl.con (quote -[1+_]) (Rfl.vArg (`nat n) ∷ [])

checkLiteral : (σ : Sort) → Rfl.Term → Maybe (Literal σ)
checkLiteral (CORE φ) x         = Maybe.map core (checkCoreLiteral φ x)
checkLiteral INT      (`nat n)  = just (nat n)
checkLiteral INT      (`+ n)    = just (int (+ n))
checkLiteral INT      `-[1+ n ] = just (int -[1+ n ])
checkLiteral INT      _         = nothing


-----------------
-- Identifiers --
-----------------

private
  pattern `eq  = quote PropEq._≡_
  pattern `neq = quote PropEq._≢_
  -- NOTE: We're interpreting BOOL to be Set. Unfortunately, that means that `ite`
  --       cannot really be given a sensible interpretation. (Unless, perhaps, we
  --       involve Dec.)
  --
  -- pattern `ite = ?
  pattern `neg = quote Int.-_
  pattern `sub = quote Int._-_
  pattern `add = quote Int._+_
  pattern `mul = quote Int._*_
  -- NOTE: Integer division and modulo are currently not defined in the standard
  --       library, so we don't map them here. Note that division by zero is
  --       allowed in SMT-LIB, so care should be taken.
  --
  -- pattern `div = ?
  -- pattern `mod = ?
  pattern `abs = quote Int.∣_∣
  pattern `leq = quote Int._≤_
  pattern `lt  = quote Int._<_
  pattern `geq = quote Int._≥_
  pattern `gt  = quote Int._>_

checkIdentifier : (σ : Sort) → Rfl.Name → Maybe (Σ[ Σ ∈ Signature σ ] Macro Σ)
checkIdentifier BOOL     `eq  = just (Rel INT , app eq)
checkIdentifier BOOL     `neq = just (Rel INT , app neq)
checkIdentifier INT      `neg = just (Op₁ INT , app neg)
checkIdentifier INT      `sub = just (Op₂ INT , app sub)
checkIdentifier INT      `add = just (Op₂ INT , app add)
checkIdentifier INT      `mul = just (Op₂ INT , app mul)
checkIdentifier INT      `abs = just (Op₁ INT , app abs)
checkIdentifier BOOL     `leq = just (Rel INT , app leq)
checkIdentifier BOOL     `lt  = just (Rel INT , app lt)
checkIdentifier BOOL     `geq = just (Rel INT , app geq)
checkIdentifier BOOL     `gt  = just (Rel INT , app gt)
checkIdentifier INT       _   = nothing
checkIdentifier (CORE φ)  x   =
  Maybe.map (Prod.map liftCoreSignature (λ i → app (core i))) (checkCoreIdentifier′ φ x)


---------------
-- Instances --
---------------

reflectable : Reflectable theory
Reflectable.sorts           reflectable = sorts
Reflectable.checkLiteral    reflectable = checkLiteral
Reflectable.checkIdentifier reflectable = checkIdentifier
