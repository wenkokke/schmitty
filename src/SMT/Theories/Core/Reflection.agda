{-# OPTIONS --guardedness #-}

--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Defines the `Reflectable` instance for core theory, called `coreReflectable`.
--------------------------------------------------------------------------------

module SMT.Theories.Core.Reflection where

open import Data.Empty as Empty using (⊥)
open import Data.Bool.Base as Bool using (Bool; false; true)
open import Data.List.Base as List using (List; _∷_; [])
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Product as Prod using (Σ-syntax; _,_; _×_)
open import Data.Sum as Sum using (_⊎_)
open import Data.Unit as Unit using (⊤)
open import Function using (Morphism)
import Reflection as Rfl
open import Relation.Nullary using (¬_)
open import SMT.Theory
open import SMT.Theories.Core.Base as Core
open import SMT.Script.Base Core.theory renaming ( Macro to CoreMacro )


-----------
-- Sorts --
-----------

coreSorts : List CoreSort
coreSorts = BOOL ∷ []


checkCoreSort : Rfl.Term → Maybe CoreSort
checkCoreSort (Rfl.agda-sort _) = just BOOL
checkCoreSort _                 = nothing


--------------
-- Literals --
--------------

checkCoreLiteral : (φ : CoreSort) → Rfl.Literal → Maybe (CoreLiteral φ)
checkCoreLiteral _ _ = nothing


-----------------
-- Identifiers --
-----------------

-- NOTE: There is no builtin type corresponding to XOR, so we don't map anything
--       to XOR. The bulltin Π-type has no name, so in the Reflection to Raw
--       code we must take care to map non-dependent Π-types to "Morphism" from
--       the module Function.Core.
--
private
  pattern `false   = quote ⊥
  pattern `true    = quote ⊤
  pattern `not     = quote ¬_
  pattern `implies = quote Morphism
  pattern `and     = quote _×_
  pattern `or      = quote _⊎_


-- NOTE: The core theory is not allowed to use macros, because this gets us in
--       trouble while extending theories: we cannot lift CoreMacros into
--       arbitrary Macros, since that would require us to *lower* arbitrary
--       Terms to CoreTerms. With great power comes very little extensibility.
checkCoreIdentifier′ : (φ : CoreSort) → Rfl.Name → Maybe (Σ[ Φ ∈ Signature φ ] CoreIdentifier Φ)
checkCoreIdentifier′ BOOL `false   = just (Op₀ BOOL , false)
checkCoreIdentifier′ BOOL `true    = just (Op₀ BOOL , true)
checkCoreIdentifier′ BOOL `not     = just (Op₁ BOOL , not)
checkCoreIdentifier′ BOOL `implies = just (Op₂ BOOL , implies)
checkCoreIdentifier′ BOOL `and     = just (Op₂ BOOL , and)
checkCoreIdentifier′ BOOL `or      = just (Op₂ BOOL , or)
checkCoreIdentifier′ BOOL  _       = nothing

checkCoreIdentifier : (φ : CoreSort) → Rfl.Name → Maybe (Σ[ Φ ∈ Signature φ ] CoreMacro Φ)
checkCoreIdentifier φ n = Maybe.map (Prod.map₂ λ {Φ} f args → `app f args) (checkCoreIdentifier′ φ n)


-----------------------
-- Proof computation --
-----------------------

-- There are no interesting proof computations for the core theory.
coreProofComputation : ∀ {Γ} → Term Γ BOOL → Rfl.Name
coreProofComputation _ = quote Function.id


---------------
-- Instances --
---------------

instance
  coreReflectable : Reflectable theory
  Reflectable.sorts            coreReflectable = coreSorts
  Reflectable.checkSort        coreReflectable = checkCoreSort
  Reflectable.checkLiteral     coreReflectable = checkCoreLiteral
  Reflectable.checkIdentifier  coreReflectable = checkCoreIdentifier
  Reflectable.proofComputation coreReflectable = coreProofComputation
