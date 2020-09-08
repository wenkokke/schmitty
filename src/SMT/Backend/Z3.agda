{-# OPTIONS --allow-exec #-}

open import SMT.Theory

module SMT.Backend.Z3 (theory : Theory) (reflectable : Reflectable theory) where

open Theory theory
open Reflectable reflectable

open import Data.List as List using (List; _∷_; _∷ʳ_; [])
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String as String using (String; _++_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit as Unit using (⊤)
open import Data.List.Relation.Unary.All
open import Function using (case_of_; const; _$_; _∘_)
open import Reflection as Rfl using (return; _>>=_; _>>_)
open import Reflection.External
open import Text.Parser.String using (runParser)
open import SMT.Script theory reflectable
open import SMT.Backend.Base

private
  variable
    Γ Γ′ : Ctxt
    ξ : OutputType
    Ξ : OutputCtxt


z3TC : Script [] Γ (ξ ∷ Ξ) → Rfl.TC (Outputs (ξ ∷ Ξ))
z3TC {Γ} {ξ} {Ξ} scr = do

  -- Print the SMT-LIB script and build the output parser.
  let (scr , parseOutputs) = showScript scr

  -- Construct the command specification.
  let z3Cmd = record
              { name  = "z3"
              ; args  = "-smt2" ∷ "-in" ∷ "-v:0" ∷ []
              ; input = scr
              }

  -- Run the Z3 command and parse the output.
  (result exitCode stdout stderr) ← unsafeRunCmdTC z3Cmd
  case runParser parseOutputs stdout of λ where
    (inj₁ parserr) → parseError stdout parserr
    (inj₂ outputs) → return outputs


macro
  z3 : Script [] Γ (ξ ∷ Ξ) → Rfl.Term → Rfl.TC ⊤
  z3 scr hole = z3TC scr >>= Rfl.unify hole ∘ quoteOutputs

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

macro
  solveZ3 : Rfl.Term → Rfl.TC ⊤
  solveZ3 hole = do
    goal ← Rfl.inferType hole
    Γ , scr ← reflectToScript goal
    let scr′ = scr ◆ get-model ∷ []
    qm ∷ [] ← z3TC scr′
    case qm of λ where
      (sat     , m) → typeErrorCounterExample scr′ m
      (unsat   , _) → Rfl.unify hole (`because "z3" goal)
      (unknown , _) → Rfl.typeErrorFmt "Solver returned 'unknown'"
