--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Defines the `Reflectable` class, which is used to provide integration with
-- Agda reflection. To implement the `Reflectable` class, you need to provide
-- conversions from the raw theory to the intended theory.
--
-- Optionally, you may implement the `proofComputation` function, which is used
-- to generate proof objects which compute on closed terms. For an example, see
-- `SMT.Theories.Ints.Reflectable`.
--------------------------------------------------------------------------------

open import SMT.Theory.Base

module SMT.Theory.Class.Reflectable (theory : Theory) where

open Theory theory

open import Data.List as List using (List)
open import Data.Maybe as Maybe using (Maybe)
open import Data.Product as Prod using (Σ-syntax)
import Reflection as Rfl
open import SMT.Script.Base theory


record Reflectable : Set where
  field
    sorts           : List Sort
    checkSort       : Rfl.Term → Maybe Sort
    checkLiteral    : (σ : Sort) → Rfl.Literal → Maybe (Literal σ)
    checkIdentifier : (σ : Sort) → Rfl.Name → Maybe (Σ[ Σ ∈ Signature σ ] Macro Σ)

    -- |Return the name of a function `f : ∀ {..} → Goal → Goal` which will be called
    --  with `because "solver" Goal` as the argument. Can be used to produce proof objects
    --  that compute on closed terms.
    proofComputation : ∀ {Γ} → Term Γ BOOL → Rfl.Name
