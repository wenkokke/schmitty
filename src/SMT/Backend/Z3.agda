{-# OPTIONS --allow-exec #-}

open import SMT.Theory

module SMT.Backend.Z3 (theory : Theory) where

open Theory theory

open import Data.List as List using (List; _∷_; [])
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String as String using (String; _++_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit as Unit using (⊤)
open import Function using (case_of_; const; _$_; _∘_)
open import Reflection as Rfl using (return; _>>=_; _>>_)
open import Reflection.External
open import Text.Parser.String using (runParser)
open import SMT.Script theory

private
  variable
    Γ : Ctxt
    ξ : OutputType
    Ξ : OutputCtxt

z3TC : Script [] Γ (ξ ∷ Ξ) → Rfl.TC Rfl.Term
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
  z3 : Script [] Γ (ξ ∷ Ξ) → Rfl.Term → Rfl.TC ⊤
  z3 scr hole = z3TC scr >>= Rfl.unify hole
