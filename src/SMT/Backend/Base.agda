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
  because : ∀ {a} (solver : String) (A : Set a) → A

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

    piApply′ : Rfl.Term → List Rfl.Term → Rfl.Term
    piApply′ t [] = t
    piApply′ (Rfl.pi (Rfl.arg _ a) (Rfl.abs x b)) (v ∷ args) =
      Rfl.def (quote Function._$′_)
              ( Rfl.hArg Rfl.unknown
              ∷ Rfl.hArg a
              ∷ Rfl.hArg Rfl.unknown
              ∷ Rfl.hArg Rfl.unknown
              ∷ Rfl.vArg (Rfl.lam Rfl.visible (Rfl.abs x (piApply′ b args)))
              ∷ Rfl.vArg v
              ∷ [])
    piApply′ t _ = t -- impossible?

    modelToQuotedList : Model Γ → List Rfl.Term → List Rfl.Term
    modelToQuotedList [] acc = acc
    modelToQuotedList (v ∷ m) acc = modelToQuotedList m (quoteValue _ v ∷ acc)

    -- Assume all declare-consts are up front (this is what we parse in reflectToRawScript).
    piApply : Rfl.Term → Model Γ → Rfl.Term
    piApply goal m = piApply′ goal (modelToQuotedList m [])

  private
    counterExample : VarNames Γ → Model Γ → List Rfl.ErrorPart → List Rfl.ErrorPart
    counterExample []       []      acc = acc
    counterExample (x ∷ xs) (v ∷ m) acc =
      counterExample xs m (Rfl.strErr "  " ∷ Rfl.strErr x ∷ Rfl.strErr " = " ∷ Rfl.termErr (quoteValue _ v) ∷ Rfl.strErr "\n" ∷ acc)

  typeErrorCounterExample : Rfl.Term → Script [] Γ Ξ → Model Γ → Rfl.TC ⊤
  typeErrorCounterExample {Γ} goal scr m = do
    inst-goal ← Rfl.normalise (piApply goal m)
    Rfl.typeErrorFmt "Found counter-example:\n%erefuting %t" (counterExample (scriptVarNames scr) m []) inst-goal

  solve : String → (∀ {Γ ξ Ξ} → Script [] Γ (ξ ∷ Ξ) → Rfl.TC (Outputs (ξ ∷ Ξ))) → Rfl.Term → Rfl.TC ⊤
  solve name solver hole = do
    goal ← Rfl.inferType hole
    Γ , scr ← reflectToScript goal
    let scr′ = scr ◆ get-model ∷ []
    qm ∷ [] ← solver scr′
    case qm of λ where
      (sat     , m) → typeErrorCounterExample goal scr′ m
      (unsat   , _) → Rfl.unify hole (`because name goal)
      (unknown , _) → Rfl.typeErrorFmt "Solver returned 'unknown'"
