{-# OPTIONS --allow-exec #-}

open import SMT.Theory

module SMT.Backend.Z3 {s i l} (showableTheory : ShowableTheory s i l) where

open ShowableTheory showableTheory
open import SMT.Script theory
open import SMT.Script.Show showableTheory
open import Data.List
open import Reflection.External

private
  variable
    Γ : Ctxt
    Ξ : OutputCtxt

z3Cmd : Script [] Γ Ξ → CmdSpec
CmdSpec.name  (z3Cmd _)    = "z3"
CmdSpec.args  (z3Cmd _)    = "-smt2" ∷ "-in" ∷ "-v:0" ∷ []
CmdSpec.input (z3Cmd cmds) = showScript x′es cmds
