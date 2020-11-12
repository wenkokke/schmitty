module SMT.Theories.Ints.Reflection where


open import Data.Integer as Int using (ℤ; +_; -[1+_]; _≤_; _≥_; _<_; _>_; _≟_; _≤?_; _<?_)
                                renaming (show to showℤ)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat.Base as Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List as List using (List; _∷_; [])
open import Data.List.Relation.Unary.All as All using (All; _∷_; [])
open import Data.Product as Prod using (Σ-syntax; _,_)
open import Function using (id)
import Reflection as Rfl
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import SMT.Theory
open import SMT.Theories.Core as Core hiding (BOOL)
open import SMT.Theories.Core.Extensions
open import SMT.Theories.Ints.Base as Ints
open import SMT.Script.Base Ints.baseTheory


-----------
-- Sorts --
-----------

sorts : List Sort
sorts = INT ∷ List.map CORE coreSorts


checkSort : Rfl.Term → Maybe Sort
checkSort (Rfl.def (quote ℤ) []) = just INT
checkSort t                      = Maybe.map CORE (checkCoreSort t)


--------------
-- Literals --
--------------

private
  pattern `nat    n = Rfl.nat n

checkLiteral : (σ : Sort) → Rfl.Literal → Maybe (Literal σ)
checkLiteral (CORE φ) x         = Maybe.map core (checkCoreLiteral φ x)
checkLiteral INT      (`nat n)  = just (nat n)
checkLiteral INT      _         = nothing


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
  pattern `neg    = quote Int.-_
  pattern `sub    = quote Int._-_
  pattern `add    = quote Int._+_
  pattern `mul    = quote Int._*_
  -- NOTE: Integer division and modulo are currently not defined in the standard
  --       library, so we don't map them here. Note that division by zero is
  --       allowed in SMT-LIB, so care should be taken.
  --
  -- pattern `div = ?
  -- pattern `mod = ?
  pattern `abs    = quote Int.∣_∣
  pattern `leq    = quote Int._≤_
  pattern `lt     = quote Int._<_
  pattern `geq    = quote Int._≥_
  pattern `gt     = quote Int._>_

  pattern `zero   = quote Nat.zero
  pattern `suc    = quote Nat.suc

  -- NOTE: These should eventually use NAT sort, once we implement NAT sort.
  `zero! : Macro (Op₀ INT)
  `zero! [] = `lit (nat 0)

  `suc! : Macro (Op₁ INT)
  `suc! (`lit (nat x) ∷ []) = `lit (nat (Nat.suc x))
  `suc! (x ∷ [])           = `app₂ add (`lit (nat 1)) x

  pattern `+_     = quote Int.+_
  pattern `-[1+_] = quote Int.-[1+_]

  `+!_ : Macro (Op₁ INT)
  `+! (x ∷ []) = x

  `-[1+_]! : Macro (Op₁ INT)
  `-[1+ `lit (nat x) ∷ [] ]! = `lit (int -[1+ x ])
  `-[1+ `lit (int x) ∷ [] ]! = `lit (int (Int.- (Int.1ℤ Int.+ x)))
  `-[1+ x ∷ [] ]!            = `app₁ neg (`app₂ add (`lit (nat 1)) x)

checkIdentifier : (σ : Sort) → Rfl.Name → Maybe (Σ[ Σ ∈ Signature σ ] Macro Σ)
checkIdentifier INT      `zero   = just (Op₀ INT , `zero!)
checkIdentifier INT      `suc    = just (Op₁ INT , `suc!)
checkIdentifier INT      `+_     = just (Op₁ INT , `+!_)
checkIdentifier INT      `-[1+_] = just (Op₁ INT , `-[1+_]!)
checkIdentifier BOOL     `eq     = just (Rel INT , `app eq)
checkIdentifier BOOL     `neq    = just (Rel INT , `app neq)
checkIdentifier INT      `neg    = just (Op₁ INT , `app neg)
checkIdentifier INT      `sub    = just (Op₂ INT , `app sub)
checkIdentifier INT      `add    = just (Op₂ INT , `app add)
checkIdentifier INT      `mul    = just (Op₂ INT , `app mul)
checkIdentifier INT      `abs    = just (Op₁ INT , `app abs)
checkIdentifier BOOL     `leq    = just (Rel INT , `app leq)
checkIdentifier BOOL     `lt     = just (Rel INT , `app lt)
checkIdentifier BOOL     `geq    = just (Rel INT , `app geq)
checkIdentifier BOOL     `gt     = just (Rel INT , `app gt)
checkIdentifier INT       _      = nothing
checkIdentifier (CORE φ)  x      =
  Maybe.map (Prod.map liftCoreSignature (λ i → `app (core i))) (checkCoreIdentifier′ φ x)


-----------------------
-- Proof computation --
-----------------------

private
  compute≡ : {x y : ℤ} → x ≡ y → x ≡ y
  compute≡ {x} {y} fallback with x ≟ y
  ... | yes p = p
  ... | no  _ = fallback

  compute≢ : {x y : ℤ} → x ≢ y → x ≢ y
  compute≢ {x} {y} fallback with x ≟ y
  ... | yes _ = fallback
  ... | no  p = p

  compute≤ : {x y : ℤ} → x ≤ y → x ≤ y
  compute≤ {x} {y} fallback with x ≤? y
  ... | yes p = p
  ... | no  _ = fallback

  compute≥ : {x y : ℤ} → x ≥ y → x ≥ y
  compute≥ p = compute≤ p

  compute< : {x y : ℤ} → x < y → x < y
  compute< {x} {y} fallback with x <? y
  ... | yes p = p
  ... | no  _ = fallback

  compute> : {x y : ℤ} → x > y → x > y
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

reflectable : Reflectable theory
Reflectable.sorts            reflectable = sorts
Reflectable.checkSort        reflectable = checkSort
Reflectable.checkLiteral     reflectable = checkLiteral
Reflectable.checkIdentifier  reflectable = checkIdentifier
Reflectable.proofComputation reflectable = proofComputation
