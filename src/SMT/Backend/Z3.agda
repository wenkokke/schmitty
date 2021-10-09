{-# OPTIONS --allow-exec #-}
{-# OPTIONS --guardedness #-}

--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Defines the `z3` tactic, which runs an SMT-LIB script using Z3, as well as
-- the `solveZ3` tactic, which translates the goal term to an SMT-LIB script and
-- solves it using Z3.
--------------------------------------------------------------------------------

open import SMT.Theory

module SMT.Backend.Z3 (theory : Theory) {{solvable : Solvable theory}} where

open Solvable solvable

open import Data.List as List using (List; _∷_; _∷ʳ_; [])
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String as String using (String; _++_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit as Unit using (⊤)
open import Function using (case_of_; const; _$_; _∘_)
open import Reflection as Rfl using (return; _>>=_; _>>_)
open import Reflection.External
open import SMT.Backend.Base
open import SMT.Script.Base theory public

private
  variable
    Γ Γ′ : Ctxt
    ξ : OutputType
    Ξ : OutputCtxt


z3TC : Script [] Γ (ξ ∷ Ξ) → Rfl.TC (Outputs (ξ ∷ Ξ))
z3TC {Γ} {ξ} {Ξ} scr = do

  -- Print the SMT-LIB script and build the output parser.
  let (scr , parseOutputs) = toSMTLIBWithOutputParser scr

  -- Construct the command specification.
  let z3Cmd = record
              { name  = "z3"
              ; args  = "-smt2" ∷ "-in" ∷ "-v:0" ∷ []
              ; input = scr
              }

  -- Run the Z3 command and parse the output.
  (result exitCode stdout stderr) ← unsafeRunCmdTC z3Cmd
  case parseOutputs stdout of λ where
    (inj₁ smterr)  → displayError stdout smterr (showCmdSpec z3Cmd) scr
    (inj₂ outputs) → return outputs


macro
  z3 : Script [] Γ (ξ ∷ Ξ) → Rfl.Term → Rfl.TC ⊤
  z3 scr hole = z3TC scr >>= Rfl.unify hole ∘ quoteOutputs


macro
  solveZ3 : {{Reflectable theory}} → Rfl.Term → Rfl.TC ⊤
  solveZ3 = solve "z3" z3TC
    where
      open Solver theory using (solve)
