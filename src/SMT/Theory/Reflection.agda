open import SMT.Theory

module SMT.Theory.Reflection (theory : Theory) where


open Theory theory
open import Level
open import Data.List as List using (List; _∷_; [])
open import Data.Maybe as Maybe using (Maybe)
open import Data.Product as Prod using (Σ-syntax)
import Reflection as Rfl
open import SMT.Script.Base baseTheory


record Reflectable : Set where
  field
    sorts           : List Sort
    checkLiteral    : (σ : Sort) → Rfl.Term → Maybe (Literal σ)
    checkIdentifier : (σ : Sort) → Rfl.Name → Maybe (Σ[ Σ ∈ Signature σ ] Macro Σ)
