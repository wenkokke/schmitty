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

open import Data.List as List using (List; _∷_; [])
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String as String using (String; _++_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit as Unit using (⊤)
open import Function using (case_of_; const; _$_; _∘_)
open import Reflection hiding (Term)
open import Reflection.External
open import Text.Parser.String using (ParseErrorMsg; no-parse; ambiguous-parse; runParser)
open import SMT.Script printable parsable public

private
  variable
    Γ : Ctxt
    ξ : OutputType
    Ξ : OutputCtxt

parseErrorMsg : (input : String) → ParseErrorMsg →  String
parseErrorMsg input no-parse        = "Failed to parse '" ++ input ++ "'"
parseErrorMsg input ambiguous-parse = "Ambiguous parse '" ++ input ++ "'"

parseError : ∀ {a} {A : Set a} (input : String) (errMsg : ParseErrorMsg) → TC A
parseError input errMsg = typeError (strErr (parseErrorMsg input errMsg) ∷ [])

z3TC : Script [] Γ (ξ ∷ Ξ) → TC Reflection.Term
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
  stdout ← runCmdTC z3Cmd
  case runParser parseOutputs stdout of λ where
    (inj₁ parserr) → parseError stdout parserr
    (inj₂ outputs) → return $ quoteOutputs outputs

macro
  z3 : Script [] Γ (ξ ∷ Ξ) → Reflection.Term → TC ⊤
  z3 scr hole = z3TC scr >>= unify hole
