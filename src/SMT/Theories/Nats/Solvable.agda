{-# OPTIONS --guardedness #-}

--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- TODO
--------------------------------------------------------------------------------

module SMT.Theories.Nats.Solvable where

open import Data.Integer using (+_; -[1+_])
open import Data.List as List using (List; []; _∷_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_$_; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theory
open import SMT.Script.Base
import SMT.Theories.Core as Core
import SMT.Theories.Ints as Ints
import SMT.Theories.Nats.Base as Nats


sortTranslation : SortTranslation Nats.theory Ints.theory
sortTranslation = record
  { compileSort       = compileSort
  ; interpSort        = interpSort
  ; interpCompileSort = interpCompileSort
  }
  where
    compileSort : Nats.Sort → Ints.Sort
    compileSort (Nats.CORE φ) = Ints.CORE φ
    compileSort Nats.NAT      = Ints.INT

    interpSort : Ints.Sort → Nats.Sort
    interpSort (Ints.CORE φ) = Nats.CORE φ
    interpSort Ints.INT      = Nats.NAT

    interpCompileSort : ∀ σ → interpSort (compileSort σ) ≡ σ
    interpCompileSort (Nats.CORE φ) = refl
    interpCompileSort Nats.NAT      = refl

open SortTranslation sortTranslation


translation : Translation Nats.theory Ints.theory
translation = record
  { sortTranslation = sortTranslation
  ; compileScript   = compileScript
  ; interpOutputs   = interpOutputs
  }
  where
    compileLiteral : ∀ {σ} → Nats.Literal σ → Ints.Literal (compileSort σ)
    compileLiteral (Nats.nat x) = Ints.nat x

    compileIdentifier : ∀ {σ} {Σ : Signature σ} → Nats.Identifier Σ → Ints.Identifier (map compileSort Σ)
    compileIdentifier (Nats.core Core.false)   = Ints.core Core.false
    compileIdentifier (Nats.core Core.true)    = Ints.core Core.true
    compileIdentifier (Nats.core Core.not)     = Ints.core Core.not
    compileIdentifier (Nats.core Core.implies) = Ints.core Core.implies
    compileIdentifier (Nats.core Core.and)     = Ints.core Core.and
    compileIdentifier (Nats.core Core.or)      = Ints.core Core.or
    compileIdentifier (Nats.core Core.xor)     = Ints.core Core.xor
    compileIdentifier Nats.eq                  = Ints.eq
    compileIdentifier Nats.neq                 = Ints.eq
    compileIdentifier Nats.ite                 = Ints.ite
    compileIdentifier Nats.mon                 = Ints.sub
    compileIdentifier Nats.add                 = Ints.add
    compileIdentifier Nats.mul                 = Ints.mul
    compileIdentifier Nats.div                 = Ints.div
    compileIdentifier Nats.mod                 = Ints.mod
    compileIdentifier Nats.leq                 = Ints.leq
    compileIdentifier Nats.lt                  = Ints.lt
    compileIdentifier Nats.geq                 = Ints.geq
    compileIdentifier Nats.gt                  = Ints.gt

    -- consider exporting Script from the top-level module, so we don't have to do the following
    private
      module VS = SMT.Script.Base Nats.theory
      module CS = SMT.Script.Base Ints.theory

    last≥0 : ∀ {Γ} → CS.Term (Ints.INT ∷ Γ) Ints.BOOL
    last≥0 = `app₂ Ints.geq (`var (here refl)) (CS.`lit (Ints.int (+ zero)))

    mutual
      compileTerm : ∀ {Γ σ} → VS.Term Γ σ → CS.Term (compileCtxt Γ) (compileSort σ)
      compileTerm (`var x)               = `var (∈-map⁺ compileSort x)
      compileTerm (`lit l)               = `lit (compileLiteral l)
      compileTerm (`app x xs)            = `app (compileIdentifier x) (compileArgs xs)
      compileTerm (`forall n Nats.NAT t) = `forall n Ints.INT (`app₂ (Ints.core Core.and) last≥0 (compileTerm t))
      compileTerm (`forall n σ t)        = `forall n (compileSort σ) (compileTerm t)
      compileTerm (`exists n Nats.NAT t) = `exists n Ints.INT (`app₂ (Ints.core Core.and) last≥0 (compileTerm t))
      compileTerm (`exists n σ t)        = `exists n (compileSort σ) (compileTerm t)
      compileTerm (`let n σ t′ t)        = `let n (compileSort σ) (compileTerm t′) (compileTerm t)

      compileArgs : ∀ {Γ Δ} → VS.Args Γ Δ → CS.Args (compileCtxt Γ) (compileCtxt Δ)
      compileArgs []       = []
      compileArgs (x ∷ xs) = compileTerm x ∷ compileArgs xs

    compileScript : ∀ {Γ Γ′ Ξ} → VS.Script Γ Γ′ Ξ → CS.Script (compileCtxt Γ) (compileCtxt Γ′) (compileOutputCtxt Ξ)
    compileScript []                              = []
    compileScript (`set-logic l scr)              = `set-logic l $ compileScript scr
    compileScript (`declare-const n Nats.NAT scr) = `declare-const n Ints.INT
                                                  $ `assert last≥0
                                                  $ compileScript scr
    compileScript (`declare-const n σ scr)        = `declare-const n (compileSort σ) $ compileScript scr
    compileScript (`assert t scr)                 = `assert (compileTerm t) $ compileScript scr
    compileScript (`check-sat scr)                = `check-sat $ compileScript scr
    compileScript (`get-model scr)                = `get-model $ compileScript scr

    module _ where
      open import Level
      open import Data.Sum.Categorical.Left InterpError Level.zero using (monad)
      open import Category.Monad

      open RawMonad monad

      interpSat : CS.Sat → VS.Sat
      interpSat sat     = sat
      interpSat unsat   = unsat
      interpSat unknown = unknown

      interpValue : ∀ {σ} → Ints.Value σ → InterpError ⊎ Nats.Value (interpSort σ)
      interpValue {Ints.CORE φ} x       = return x
      interpValue {Ints.INT} (+_ n)     = return n
      interpValue {Ints.INT} (-[1+ n ]) = inj₁ "interpValue error" -- TODO: better error message

      interpModel : ∀ {Γ} → CS.Model Γ → InterpError ⊎ VS.Model (interpCtxt Γ)
      interpModel {[]}    []       = return []
      interpModel {σ ∷ Γ} (x ∷ xs) = do
        x′ ← interpValue {σ} x
        xs′ ← interpModel xs
        return (x′ ∷ xs′ )

      interpQualifiedModel : ∀ {Γ} → CS.QualifiedModel Γ → InterpError ⊎ VS.QualifiedModel (interpCtxt Γ)
      interpQualifiedModel (sat     , model) = do model′ ← interpModel model
                                                  return (sat , model′)
      interpQualifiedModel (unsat   , ⊤)     = return (unsat , tt)
      interpQualifiedModel (unknown , ⊤)     = return (unknown , tt)

      interpOutputs : ∀ {Ξ} → CS.Outputs Ξ → InterpError ⊎ VS.Outputs (interpOutputCtxt Ξ)
      interpOutputs {[]}          []       = return []
      interpOutputs {SAT ∷ Ξ}     (x ∷ xs) = do r ← interpOutputs xs
                                                return (interpSat x ∷ r)
      interpOutputs {MODEL Γ ∷ Ξ} (x ∷ xs) = do r ← interpOutputs xs
                                                m ← interpQualifiedModel x
                                                return (m ∷ r)


instance
  solvable : Solvable Nats.theory
  solvable = makeVirtualSolvable Nats.theory Ints.theory translation
