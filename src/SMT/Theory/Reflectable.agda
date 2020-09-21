open import SMT.Theory.Base

module SMT.Theory.Reflectable (theory : Theory) where


open Theory theory

import Level
open import Data.List as List using (List)
open import Data.Maybe as Maybe using (Maybe)
open import Data.Product as Prod using (Σ-syntax)
import Reflection as Rfl
open import SMT.Script.Base baseTheory


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
