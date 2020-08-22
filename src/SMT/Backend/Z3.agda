{-# OPTIONS --allow-exec #-}

open import SMT.Theory

module SMT.Backend.Z3
  {theory : Theory}
  (printable : Printable theory)
  (parsable : Parsable theory)
  where

open Theory theory
open Printable printable
open Parsable parsable

open import SMT.Script.Base theory hiding (Term)
open import SMT.Script printable parsable
open import Data.List as List using (List; _∷_; [])
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String as String using (String; _<+>_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit as Unit using (⊤)
open import Function using (case_of_; const; _$_; _∘_)
open import Reflection
open import Reflection.External
open import Text.Parser.String using (parseError; runParser)

private
  variable
    Γ : Ctxt
    ξ : OutputType
    Ξ : OutputCtxt

mkZ3Cmd : Script [] Γ Ξ → CmdSpec
CmdSpec.name  (mkZ3Cmd _)   = "z3"
CmdSpec.args  (mkZ3Cmd _)   = "-smt2" ∷ "-in" ∷ "-v:0" ∷ []
CmdSpec.input (mkZ3Cmd scr) = proj₁ (showScript scr)

runZ3TC : Script [] Γ (ξ ∷ Ξ) → TC (StdErr ⊎ Term)
runZ3TC {Γ} {ξ} {Ξ} scr = do

  -- Print the SMT-LIB script and build the output parser.
  let (scr , parseOutputs) = showScript scr

  -- Construct the command specification.
  let z3Cmd = record
              { name  = "z3"
              ; args  = "-smt2" ∷ "-in" ∷ "-v:0" ∷ []
              ; input = scr
              }

  -- Run the Z3 command and parse the output.
  r ← runCmdTC z3Cmd
  case r of λ where
    (inj₁ stderr) → return ∘ inj₁ $ stderr
    (inj₂ stdout) →
      case runParser parseOutputs stdout of λ where
        (inj₁ parserr) → return ∘ inj₁ $ parseError stdout parserr
        (inj₂ outputs) → return ∘ inj₂ $ quoteOutputs outputs

macro
  runZ3 : Script [] Γ (ξ ∷ Ξ) → Term → TC ⊤
  runZ3 scr hole = runZ3TC scr >>= [ userError , unify hole ]
