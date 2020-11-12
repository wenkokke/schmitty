--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Defines various helper functions used in all backends.
--------------------------------------------------------------------------------

module SMT.Backend.Base where

open import Data.List as List using (List; _∷_; [])
open import Data.List.Relation.Unary.All as All using (All; _∷_; [])
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String as String using (String)
open import Data.Unit using (⊤)
open import Function using (case_of_; const; _$_; _∘_; flip)
open import Reflection as Rfl using (return; _>>=_; _>>_)
open import Reflection.Normalise using (normaliseClosed)
open import SMT.Theory


postulate
  because : ∀ {a} (solver : String) (A : Set a) → A

`because : (solver : String) (A : Rfl.Type) → Rfl.Term
`because solver A = Rfl.def (quote because) (Rfl.vArg (Rfl.lit (Rfl.string solver)) ∷ Rfl.vArg A ∷ [])


module Solver {theory : Theory} (reflectable : Reflectable theory) where

  open Theory theory
  open Reflectable reflectable
  open import SMT.Script reflectable

  private
    variable
      Γ Γ′ : Ctxt
      Ξ : OutputCtxt

    -- Instantiate the arguments to a Π-type with the values in a Model.
    --
    -- NOTE: We assume all declare-consts are up front, which is what we return
    --       from reflectToRawScript. Possibly, the output of quoteInterpValues
    --       needs to be reversed.
    --
    piApply : Rfl.Term → List Rfl.Term → Rfl.Term
    piApply goal vs = piApply′ goal vs
      where
        piApply′ : Rfl.Term → List Rfl.Term → Rfl.Term
        piApply′ t [] = t
        piApply′ (Rfl.pi (Rfl.arg _ a) (Rfl.abs x b)) (v ∷ args) =
          Rfl.def (quote Function._$′_)
                  $ Rfl.hArg Rfl.unknown
                  ∷ Rfl.hArg a
                  ∷ Rfl.hArg Rfl.unknown
                  ∷ Rfl.hArg Rfl.unknown
                  ∷ Rfl.vArg (Rfl.lam Rfl.visible (Rfl.abs x (piApply b args)))
                  ∷ Rfl.vArg v
                  ∷ []
        piApply′ t _ = t -- impossible?

    counterExampleFmt : VarNames Γ → ValueInterps Γ → List Rfl.ErrorPart → List Rfl.ErrorPart
    counterExampleFmt []       []      acc = acc
    counterExampleFmt (x ∷ xs) (v ∷ m) acc =
      counterExampleFmt xs m $
        Rfl.strErr "  " ∷ Rfl.strErr x ∷ Rfl.strErr " = " ∷ Rfl.termErr v ∷ Rfl.strErr "\n" ∷ acc

  typeErrorCounterExample : Rfl.Term → Script [] Γ Ξ → Model Γ → Rfl.TC ⊤
  typeErrorCounterExample goal scr vs = do
    let `vs = quoteInterpValues vs
    instGoal₀ ← Rfl.reduce (piApply goal (List.reverse ∘ List.map proj₂ ∘ All.toList $ `vs))
    instGoal ← normaliseClosed instGoal₀
    Rfl.typeErrorFmt "Found counter-example:\n%erefuting %t"
      (counterExampleFmt (scriptVarNames scr) `vs []) instGoal

  buildProof′ : String → Script Γ Γ′ Ξ → Rfl.Term
  buildProof′ name (`assert t ∷ []) = Rfl.def (proofComputation t) (Rfl.vArg (`because name Rfl.unknown) ∷ [])
  buildProof′ name (_ ∷ scr)        = buildProof′ name scr
  buildProof′ name []               = `because name Rfl.unknown

  buildProof : String → Script [] Γ [] → Rfl.Term → Rfl.Term
  buildProof name scr (Rfl.pi (Rfl.arg (Rfl.arg-info h _) a) (Rfl.abs x b)) =
    let x′ = case x of λ where "_" → "H"; _   → x
    in Rfl.lam h $ Rfl.abs x′ $ buildProof name scr b
  buildProof name scr goal = buildProof′ name scr

  solve : String → (∀ {Γ ξ Ξ} → Script [] Γ (ξ ∷ Ξ) → Rfl.TC (Outputs (ξ ∷ Ξ))) → Rfl.Term → Rfl.TC ⊤
  solve name solver hole = do
    goal ← Rfl.inferType hole
    Γ , scr ← reflectToScript goal
    let scr′ = scr ◆ `get-model ∷ []
    qm ∷ [] ← solver scr′
    case qm of λ where
      (sat     , m) → typeErrorCounterExample goal scr′ m
      (unsat   , _) → Rfl.unify hole (buildProof name scr goal)
      (unknown , _) → Rfl.typeErrorFmt "Solver returned 'unknown'"
