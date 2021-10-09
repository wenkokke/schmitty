{-# OPTIONS --guardedness #-}

--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- TODO
--------------------------------------------------------------------------------

module SMT.Theory.Class.Solvable where

open import Data.Product as Prod using (_×_; _,_; map₂)
open import Data.List as List using (List; _∷_; [])
open import Data.String using (String)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; subst)
import SMT.Script.Base
import SMT.Script.Show
open import SMT.Theory.Base
open import SMT.Theory.Class.Parsable
open import SMT.Theory.Class.Printable
open import Text.Parser.String using (IUniversal; Parser; runParser; Position)


InterpError : Set
InterpError = String

data SMTError : Set where
  parseError  : Position → SMTError
  interpError : InterpError → SMTError


record Solvable (theory : Theory) : Set where
  open SMT.Script.Base theory
  field
    -- rename to toSMTLIBWithOutputParser
    toSMTLIBWithOutputParser : ∀ {Γ} {Ξ}
             → Script [] Γ Ξ → String × (String → SMTError ⊎ Outputs Ξ)


makeSolvable : (theory : Theory) → {{Printable theory}} → {{Parsable theory}} → Solvable theory
makeSolvable theory = record {
    toSMTLIBWithOutputParser = Prod.map₂ (λ p s → Sum.map₁ parseError (p s)) ∘ showScript
  }
  where
    open SMT.Script.Show theory


record SortTranslation (virtual : Theory) (concrete : Theory) : Set₁ where
  private
    module VT = Theory virtual
    module VS = SMT.Script.Base virtual
    module CT = Theory concrete
    module CS = SMT.Script.Base concrete

  field
    compileSort       : VT.Sort → CT.Sort
    interpSort        : CT.Sort → VT.Sort
    interpCompileSort : ∀ σ → interpSort (compileSort σ) ≡ σ

  compileCtxt : VS.Ctxt → CS.Ctxt
  compileCtxt = List.map compileSort

  compileOutputType : VS.OutputType → CS.OutputType
  compileOutputType VS.SAT       = CS.SAT
  compileOutputType (VS.MODEL Γ) = CS.MODEL (compileCtxt Γ)

  compileOutputCtxt : VS.OutputCtxt → CS.OutputCtxt
  compileOutputCtxt = List.map compileOutputType

  interpCtxt : CS.Ctxt → VS.Ctxt
  interpCtxt = List.map interpSort

  interpOutputType : CS.OutputType → VS.OutputType
  interpOutputType CS.SAT       = VS.SAT
  interpOutputType (CS.MODEL Γ) = VS.MODEL (interpCtxt Γ)

  interpOutputCtxt : CS.OutputCtxt → VS.OutputCtxt
  interpOutputCtxt = List.map interpOutputType

  interpCompileCtxt : ∀ Γ → interpCtxt (compileCtxt Γ) ≡ Γ
  interpCompileCtxt [] = refl
  interpCompileCtxt (σ ∷ Γ) rewrite interpCompileSort σ | interpCompileCtxt Γ = refl

  interpCompileOutputType : ∀ ξ → interpOutputType (compileOutputType ξ) ≡ ξ
  interpCompileOutputType VS.SAT = refl
  interpCompileOutputType (VS.MODEL Γ) rewrite interpCompileCtxt Γ = refl

  interpCompileOutputCtxt : ∀ Ξ → interpOutputCtxt (compileOutputCtxt Ξ) ≡ Ξ
  interpCompileOutputCtxt [] = refl
  interpCompileOutputCtxt (ξ ∷ Ξ) rewrite interpCompileOutputType ξ | interpCompileOutputCtxt Ξ = refl


record Translation (virtual : Theory) (concrete : Theory) : Set₁ where
  private
    module VT = Theory virtual
    module VS = SMT.Script.Base virtual
    module CT = Theory concrete
    module CS = SMT.Script.Base concrete

  field
    sortTranslation : SortTranslation virtual concrete

  open SortTranslation sortTranslation public

  field
    compileScript     : ∀ {Γ Γ′ Ξ} → VS.Script Γ Γ′ Ξ → CS.Script (compileCtxt Γ) (compileCtxt Γ′) (compileOutputCtxt Ξ)
    interpOutputs     : ∀ {Ξ} → CS.Outputs Ξ → InterpError ⊎ VS.Outputs (interpOutputCtxt Ξ)


makeVirtualSolvable : (virtual : Theory) → (concrete : Theory) → {{Solvable concrete}} → Translation virtual concrete → Solvable virtual
makeVirtualSolvable virtual concrete translation = record {
    toSMTLIBWithOutputParser = Prod.map₂ (λ p s → [ inj₁ , Sum.map interpError ((subst VS.Outputs (interpCompileOutputCtxt _))) ∘ interpOutputs ]′ (p s) ) ∘ toSMTLIBWithOutputParser ∘ compileScript
  }
  where
    open Solvable {{...}}
    open Translation translation
    module VS = SMT.Script.Base virtual
