module SMT.Theories.Core.Reflection where

open import Data.Empty as Empty using (⊥)
open import Data.Bool.Base as Bool using (Bool; false; true)
open import Data.List.Base as List using (List; _∷_; [])
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Product as Prod using (Σ-syntax; -,_; _×_)
open import Data.Sum as Sum using (_⊎_)
open import Data.Unit as Unit using (⊤)
open import Function using (Morphism)
import Reflection as Rfl
open import Relation.Nullary using (¬_)
open import SMT.Theory
open import SMT.Theories.Raw as Raw
open import SMT.Theories.Core.Base as Core
open import SMT.Script.Base Core.coreBaseTheory


-----------
-- Sorts --
-----------

coreSorts : List CoreSort
coreSorts = BOOL ∷ []


--------------
-- Literals --
--------------

private
  pattern `⊥ = Rfl.con (quote ⊥) []
  pattern `⊤ = Rfl.con (quote ⊤) []

checkCoreLiteral : (φ : CoreSort) → Rfl.Term → Maybe (CoreLiteral φ)
checkCoreLiteral BOOL `⊥ = just (bool false)
checkCoreLiteral BOOL `⊤ = just (bool true)
checkCoreLiteral _     _ = nothing


-----------------
-- Identifiers --
-----------------

-- NOTE: There is no builtin type corresponding to XOR, so we don't map anything
--       to XOR. The bulltin Π-type has no name, so in the Reflection to Raw
--       code we must take care to map non-dependent Π-types to "Morphism" from
--       the module Function.Core.
--
private
  pattern `not     = quote ¬_
  pattern `implies = quote Morphism
  pattern `and     = quote _×_
  pattern `or      = quote _⊎_

checkCoreIdentifier : (φ : CoreSort) → Rfl.Name → Maybe (Σ[ Φ ∈ Signature φ ] CoreIdentifier Φ)
checkCoreIdentifier BOOL `not     = just (-, not)
checkCoreIdentifier BOOL `implies = just (-, implies)
checkCoreIdentifier BOOL `and     = just (-, and)
checkCoreIdentifier BOOL `or      = just (-, or)
checkCoreIdentifier BOOL  _       = nothing


---------------
-- Instances --
---------------

coreReflectable : Reflectable coreTheory
Reflectable.sorts           coreReflectable = coreSorts
Reflectable.checkLiteral    coreReflectable = checkCoreLiteral
Reflectable.checkIdentifier coreReflectable = checkCoreIdentifier
