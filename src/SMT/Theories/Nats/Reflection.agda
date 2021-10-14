{-# OPTIONS --guardedness #-}

--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Defines the `Reflectable` instance for the theory of natural numbers, called
-- `reflectable`.
--------------------------------------------------------------------------------

module SMT.Theories.Nats.Reflection where

open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat as Nat using (ℕ; _≤_; _<_; _≥_; _>_; _≟_; _≤?_; _<?_)
open import Data.List as List using (List; _∷_; [])
open import Data.List.Relation.Unary.All as All using (All; _∷_; [])
open import Data.Product as Prod using (Σ-syntax; _,_)
open import Function using (id)
import Reflection as Rfl
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import SMT.Theory
open import SMT.Theories.Core as Core hiding (BOOL; theory)
open import SMT.Theories.Core.Extensions
open import SMT.Theories.Nats.Base as Nats
open import SMT.Script.Base Nats.theory


-----------
-- Sorts --
-----------

sorts : List Sort
sorts = NAT ∷ List.map CORE coreSorts


checkSort : Rfl.Term → Maybe Sort
checkSort (Rfl.def (quote ℕ) []) = just NAT
checkSort t                      = Maybe.map CORE (checkCoreSort t)


--------------
-- Literals --
--------------

private
  pattern `nat    n = Rfl.nat n

checkLiteral : (σ : Sort) → Rfl.Literal → Maybe (Literal σ)
checkLiteral (CORE φ) x         = Maybe.map core (checkCoreLiteral φ x)
checkLiteral NAT      (`nat n)  = just (nat n)
checkLiteral NAT      _         = nothing


-----------------
-- Identifiers --
-----------------

private
  pattern `eq     = quote PropEq._≡_
  pattern `neq    = quote PropEq._≢_
  -- NOTE: We're interpreting BOOL to be Set. Unfortunately, that means that `ite`
  --       cannot really be given a sensible interpretation. (Unless, perhaps, we
  --       involve Dec.)
  --
  -- pattern `ite = ?
  pattern `sub    = quote Nat._∸_
  pattern `add    = quote Nat._+_
  pattern `mul    = quote Nat._*_
  -- pattern `div = ?
  -- pattern `mod = ?
  pattern `leq    = quote Nat._≤_
  pattern `lt     = quote Nat._<_
  pattern `geq    = quote Nat._≥_
  pattern `gt     = quote Nat._>_

  pattern `zero   = quote Nat.zero
  pattern `suc    = quote Nat.suc

  `zero! : Macro (Op₀ NAT)
  `zero! [] = `lit (nat 0)

  `suc! : Macro (Op₁ NAT)
  `suc! (`lit (nat x) ∷ []) = `lit (nat (Nat.suc x))
  `suc! (x ∷ [])           = `app₂ add (`lit (nat 1)) x

checkIdentifier : (σ : Sort) → Rfl.Name → Maybe (Σ[ Σ ∈ Signature σ ] Macro Σ)
checkIdentifier NAT      `zero   = just (Op₀ NAT , `zero!)
checkIdentifier NAT      `suc    = just (Op₁ NAT , `suc!)
checkIdentifier BOOL     `eq     = just (Rel NAT , `app eq)
checkIdentifier BOOL     `neq    = just (Rel NAT , `app neq)
checkIdentifier NAT      `sub    = just (Op₂ NAT , `app mon)
checkIdentifier NAT      `add    = just (Op₂ NAT , `app add)
checkIdentifier NAT      `mul    = just (Op₂ NAT , `app mul)
checkIdentifier BOOL     `leq    = just (Rel NAT , `app leq)
checkIdentifier BOOL     `lt     = just (Rel NAT , `app lt)
checkIdentifier BOOL     `geq    = just (Rel NAT , `app geq)
checkIdentifier BOOL     `gt     = just (Rel NAT , `app gt)
checkIdentifier NAT       _      = nothing
checkIdentifier (CORE φ)  x      =
  Maybe.map (Prod.map liftCoreSignature (λ i → `app (core i))) (checkCoreIdentifier′ φ x)


-----------------------
-- Proof computation --
-----------------------

private
  compute≡ : {x y : ℕ} → x ≡ y → x ≡ y
  compute≡ {x} {y} fallback with x ≟ y
  ... | yes p = p
  ... | no  _ = fallback

  compute≢ : {x y : ℕ} → x ≢ y → x ≢ y
  compute≢ {x} {y} fallback with x ≟ y
  ... | yes _ = fallback
  ... | no  p = p

  compute≤ : {x y : ℕ} → x ≤ y → x ≤ y
  compute≤ {x} {y} fallback with x ≤? y
  ... | yes p = p
  ... | no  _ = fallback

  compute≥ : {x y : ℕ} → x ≥ y → x ≥ y
  compute≥ p = compute≤ p

  compute< : {x y : ℕ} → x < y → x < y
  compute< {x} {y} fallback with x <? y
  ... | yes p = p
  ... | no  _ = fallback

  compute> : {x y : ℕ} → x > y → x > y
  compute> p = compute< p

  proofComputation′ : ∀ {Γ} → Term Γ BOOL → Rfl.Name
  proofComputation′ (`app eq _)  = quote compute≡
  proofComputation′ (`app neq _) = quote compute≢
  proofComputation′ (`app ite _) = quote id
  proofComputation′ (`app leq _) = quote compute≤
  proofComputation′ (`app lt _)  = quote compute<
  proofComputation′ (`app geq _) = quote compute≥
  proofComputation′ (`app gt _)  = quote compute>
  proofComputation′ _            = quote id

proofComputation : ∀ {Γ} → Term Γ BOOL → Rfl.Name
proofComputation (`app (core not) (t ∷ [])) = proofComputation′ t
proofComputation _ = quote id


---------------
-- Instances --
---------------

instance
  reflectable : Reflectable theory
  Reflectable.sorts            reflectable = sorts
  Reflectable.checkSort        reflectable = checkSort
  Reflectable.checkLiteral     reflectable = checkLiteral
  Reflectable.checkIdentifier  reflectable = checkIdentifier
  Reflectable.proofComputation reflectable = proofComputation
