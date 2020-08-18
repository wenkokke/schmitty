{-# OPTIONS --allow-exec #-}

open import Data.List using (List)
open import Data.String using (String)

module SMT.Backend.Z3
  {s i l}
  (Sort : Set s)
  (Bool : Sort)
  (Literal : Sort → Set l)
  (Identifier : List Sort → Sort → Set i)
  (showSort : Sort → String)
  (showLiteral : ∀ {σ} → Literal σ → String)
  (showIdentifier : ∀ {Σ : List Sort} {σ} → Identifier Σ σ → String)
  where

open import Data.List
open import Reflection.External
open import SMT.Script Sort Bool Literal Identifier
open import SMT.Script.Show Sort Bool Literal Identifier showSort showLiteral showIdentifier

private
  variable
    Γ : Ctxt
    Ξ : ResultCtxt

z3Cmd : Script [] Γ Ξ → CmdSpec
CmdSpec.name  (z3Cmd _)    = "z3"
CmdSpec.args  (z3Cmd _)    = "-smt2" ∷ "-in" ∷ "-v:0" ∷ []
CmdSpec.input (z3Cmd cmds) = showScript x′es cmds
