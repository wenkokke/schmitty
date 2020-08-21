{-# OPTIONS --allow-exec #-}

open import SMT.Theory

module SMT.Backend.Z3
  {theory : Theory}
  (printable : Printable theory)
  (parsable : Parsable theory)
  where

open Theory theory
open Printable printable

open import SMT.Script theory as Script using (Script; Results; Ctxt; OutputCtxt; OutputType)
open Script.Interaction printable parsable using (showScript; x′es; parseResults; quoteResults)
open import Data.List as List using (List; _∷_; [])
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.String as String using (String; _++_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit as Unit using (⊤)
open import Function using (case_of_; const; _$_; _∘_)
open import Reflection
open import Reflection.External
open import Text.Parser.String

private
  variable
    Γ : Ctxt
    ξ : OutputType
    Ξ : OutputCtxt

mkZ3Cmd : Script [] Γ Ξ → CmdSpec
CmdSpec.name  (mkZ3Cmd _)    = "z3"
CmdSpec.args  (mkZ3Cmd _)    = "-smt2" ∷ "-in" ∷ "-v:0" ∷ []
CmdSpec.input (mkZ3Cmd cmds) = showScript x′es cmds

parseError : String → ErrorMsg →  TC ⊤
parseError str no-parse
  = userError $ "Failed to parse Z3 output:\n" ++ str
parseError str ambiguous-parse
  = userError $ "Ambiguous parse:\n" ++ str

macro
  runZ3 : Script [] Γ (ξ ∷ Ξ) → Term → TC ⊤
  runZ3 {Γ} {ξ} {Ξ} scr hole =
    runCmdTC (mkZ3Cmd scr) >>=
      [ userError
      , (λ str → [ parseError str , unify hole ∘ quoteResults ] $ runParser (parseResults ξ Ξ) str) ]
