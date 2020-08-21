{-# OPTIONS --allow-exec #-}

open import SMT.Theory

module SMT.Backend.Z3 {theory : Theory} (printable : Printable theory) where

open Theory theory
open Printable printable

open import SMT.Script theory
open Interaction printable
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
