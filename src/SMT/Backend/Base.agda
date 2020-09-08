module SMT.Backend.Base where

open import Data.List as List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String as String using (String)
open import Data.Unit using (⊤)
open import Function using (case_of_; const; _$_; _∘_)
open import Reflection as Rfl using (return; _>>=_; _>>_)
open import SMT.Theory
open import SMT.Theory.Reflection

postulate
  because : (solver : String) (A : Set) → A

`because : (solver : String) (A : Rfl.Type) → Rfl.Term
`because solver A = Rfl.def (quote because) (Rfl.vArg (Rfl.lit (Rfl.string solver)) ∷ Rfl.vArg A ∷ [])

module Solver (theory : Theory) (reflectable : Reflectable theory) where

  open import SMT.Script theory reflectable
  open Theory theory
  open Reflectable reflectable

  private
    variable
      Γ : Ctxt
      Ξ : OutputCtxt

  private
    counterExample : VarNames Γ → Model Γ → List Rfl.ErrorPart → List Rfl.ErrorPart
    counterExample []       []      acc = acc
    counterExample (x ∷ xs) (v ∷ m) acc =
      counterExample xs m (Rfl.strErr "  " ∷ Rfl.strErr x ∷ Rfl.strErr " = " ∷ Rfl.termErr (quoteValue _ v) ∷ nl acc)
      where
        nl : List Rfl.ErrorPart → List Rfl.ErrorPart
        nl []  = []
        nl err = Rfl.strErr "\n" ∷ err

  typeErrorCounterExample : Script [] Γ Ξ → Model Γ → Rfl.TC ⊤
  typeErrorCounterExample {Γ} scr m =
    Rfl.typeErrorFmt "Found counter-example:\n%e" (counterExample (scriptVarNames scr) m [])

  solve : String → (∀ {Γ ξ Ξ} → Script [] Γ (ξ ∷ Ξ) → Rfl.TC (Outputs (ξ ∷ Ξ))) → Rfl.Term → Rfl.TC ⊤
  solve name solver hole = do
    goal ← Rfl.inferType hole
    Γ , scr ← reflectToScript goal
    let scr′ = scr ◆ get-model ∷ []
    qm ∷ [] ← solver scr′
    case qm of λ where
      (sat     , m) → typeErrorCounterExample scr′ m
      (unsat   , _) → Rfl.unify hole (`because name goal)
      (unknown , _) → Rfl.typeErrorFmt "Solver returned 'unknown'"
