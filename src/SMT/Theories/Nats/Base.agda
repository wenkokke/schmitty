{-# OPTIONS --guardedness #-}

--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Defines the `Theory` instance for the theory of natural numbers, called
-- "theory".
--------------------------------------------------------------------------------

module SMT.Theories.Nats.Base where

open import Data.Bool.Base as Bool using (Bool; false; true)
open import Data.Integer as Int using (ℤ; +_; -[1+_])
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.Nat.Base as Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List as List using (List; _∷_; [])
open import Data.String as String using (String)
open import Function.Equivalence using (equivalence)
import Reflection as Rfl
open import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)
open import SMT.Theory
open import SMT.Theories.Core as Core hiding (BOOL; theory)
open import SMT.Theories.Core.Extensions
open import Text.Parser.String


-----------
-- Sorts --
-----------

data Sort : Set where
   CORE : (φ : CoreSort) → Sort
   NAT  : Sort

pattern `CORE φ = Rfl.con (quote CORE) (Rfl.vArg φ ∷ [])
pattern `NAT    = Rfl.con (quote NAT) []

open Sorts Sort CORE public hiding (BOOL)

pattern BOOL = CORE Core.BOOL

private
  variable
    σ σ′ : Sort
    Σ Σ′ : Signature σ
    φ φ′ : CoreSort
    Φ Φ′ : Signature φ

CORE-injective : CORE φ ≡ CORE φ′ → φ ≡ φ′
CORE-injective refl = refl

_≟-Sort_ : (σ σ′ : Sort) → Dec (σ ≡ σ′)
CORE φ ≟-Sort CORE φ′ = Dec.map (equivalence (PropEq.cong CORE) CORE-injective) (φ ≟-CoreSort φ′)
CORE φ ≟-Sort NAT     = no (λ ())
NAT    ≟-Sort CORE φ  = no (λ ())
NAT    ≟-Sort NAT     = yes refl

quoteSort : Sort → Rfl.Term
quoteSort (CORE φ) = `CORE (quoteCoreSort φ)
quoteSort NAT      = `NAT


------------
-- Values --
------------

Value : Sort → Set
Value (CORE φ) = CoreValue φ
Value NAT      = ℕ

quoteNat : ℕ → Rfl.Term
quoteNat n = Rfl.lit (Rfl.nat n)

quoteValue : (σ : Sort) → Value σ → Rfl.Term
quoteValue (CORE φ) = quoteCoreValue φ
quoteValue NAT      = quoteNat


--------------
-- Literals --
--------------

data Literal : Sort → Set where
  core : CoreLiteral φ → Literal (CORE φ)
  nat  : ℕ → Literal NAT

private
  variable
    l : Literal σ


-----------------
-- Identifiers --
-----------------

data Identifier : (Σ : Signature σ) → Set where
  -- Core theory
  core : CoreIdentifier Φ → Identifier (map CORE Φ)
  eq   : Identifier (Rel NAT)
  neq  : Identifier (Rel NAT)
  ite  : Identifier (ITE σ)
  -- Nats theory
  add  : Identifier (Op₂ NAT)
  mon  : Identifier (Op₂ NAT)
  mul  : Identifier (Op₂ NAT)
  div  : Identifier (Op₂ NAT)
  mod  : Identifier (Op₂ NAT)
  leq  : Identifier (Rel NAT)
  lt   : Identifier (Rel NAT)
  geq  : Identifier (Rel NAT)
  gt   : Identifier (Rel NAT)

private
  variable
    i : Identifier Σ


---------------
-- Instances --
---------------

theory : Theory
Theory.Sort          theory = Sort
Theory._≟-Sort_      theory = _≟-Sort_
Theory.BOOL          theory = BOOL
Theory.Value         theory = Value
Theory.Literal       theory = Literal
Theory.Identifier    theory = Identifier
Theory.quoteSort     theory = quoteSort
Theory.quoteValue    theory = quoteValue
Theory.interpValue   theory = interpCoreValue
