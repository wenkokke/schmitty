{-# OPTIONS --guardedness #-}

--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Defines `reflectToScript`, which uses an instance of the `Reflectable` class
-- to convert reflected Agda syntax to an SMT-LIB script.
--------------------------------------------------------------------------------

open import SMT.Theory

module SMT.Script.Reflection (theory : Theory) {{reflectable : Reflectable theory}} where

open Theory theory
open Reflectable reflectable

open import Category.Monad
open import Data.Environment as Env using (Env; _∷_; [])
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.List as List using (List; _∷_; []; _++_; length)
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.List.Relation.Unary.Any as Any using (here; there)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
import Data.Maybe.Categorical as MaybeCat
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Product as Prod using (∃; ∃-syntax; -,_; _×_; _,_; proj₁; proj₂)
open import Data.String as String using (String)
open import Data.Unit as Unit using (⊤)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Function using (_$_; case_of_; _∘_; const; flip; id)
import Function.Identity.Categorical as Identity
import Level
import Reflection as Rfl
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import SMT.Script.Base theory

private
  variable
    σ σ′    : Sort
    Γ Γ′ δΓ : Ctxt
    Δ Δ′    : Ctxt
    Σ       : Signature σ
    Σ′      : Signature σ′
    ξ ξ′    : OutputType
    Ξ Ξ′ δΞ : OutputCtxt

-- * Reflection hooks

-- TODO: The checkRawTerm and checkRawCommand functions should be rewritten to
--       infer their argument sort, as opposed to just trying all sorts.
--       Premature optimisation and all that, but the current approach is
--       exponential.
module _ where

  open import SMT.Theory.Raw.Reflection

  private
    monadPlusMaybe = MaybeCat.monadPlus {Level.zero}

  open RawMonadPlus monadPlusMaybe renaming (_⊛_ to _<*>_)


  private
    variable
      σᵣ         : RawSort
      Γᵣ Γᵣ′ δΓᵣ : RawCtxt
      Ξᵣ Ξᵣ′ δΞᵣ : RawOutputCtxt
      Δᵣ Δᵣ′     : RawCtxt

  checkRawSort : RawSort → Maybe Sort
  checkRawSort ⋆        = just BOOL
  checkRawSort (TERM x) = checkSort x

  checkRawVar : (Γ : Ctxt) (σ : Sort) (n : ℕ) → Maybe (Γ ∋ σ)
  checkRawVar []       σ n       = nothing
  checkRawVar (σ′ ∷ Γ) σ zero    = ⦇ (here ∘ sym) (Maybe.decToMaybe (σ′ ≟-Sort σ)) ⦈
  checkRawVar (σ′ ∷ Γ) σ (suc n) = ⦇ extendVar (checkRawVar Γ σ n) ⦈

  mutual
    checkRawTerm : (Γ : Ctxt) (σ : Sort) {σᵣ : RawSort} → RawTerm Γᵣ σᵣ → Maybe (Term Γ σ)
    checkRawTerm Γ σ (`appᵣ (quote rawVar) (`varᵣ n ∷ [])) = do
      x ← checkRawVar Γ σ (Fin.toℕ (Any.index n))
      return $ `var x
    checkRawTerm Γ σ (`varᵣ n) = nothing -- should be no naked variables
    checkRawTerm Γ σ (`litᵣ l) = do
      l ← checkLiteral σ l
      return $ `lit l
    checkRawTerm Γ σ (`appᵣ f args) = do
      (Σ , f) ← checkIdentifier σ f
      args ← checkRawArgs Γ (ArgSorts Σ) args
      return $ f args
    checkRawTerm Γ σ (`forallᵣ n σᵣ x) = do
      refl ← Maybe.decToMaybe (σ ≟-Sort BOOL)
      σ′   ← checkRawSort σᵣ
      x    ← checkRawTerm (σ′ ∷ Γ) BOOL x
      return $ `forall n σ′ x
    checkRawTerm Γ σ (`existsᵣ n σᵣ x) = do
      refl ← Maybe.decToMaybe (σ ≟-Sort BOOL)
      σ′   ← checkRawSort σᵣ
      x    ← checkRawTerm (σ′ ∷ Γ) BOOL x
      return $ `exists n σ′ x
    checkRawTerm Γ σ (`letᵣ n σᵣ x y) = do
      σ′ ← checkRawSort σᵣ
      x  ← checkRawTerm Γ σ′ x
      y  ← checkRawTerm (σ′ ∷ Γ) σ y
      return $ (`let n σ′ x y)

    checkRawArgs : (Γ Δ : Ctxt) → RawArgs Γᵣ Δᵣ → Maybe (Args Γ Δ)
    checkRawArgs Γ []      []           = ⦇ [] ⦈
    checkRawArgs Γ (σ ∷ Δ) (arg ∷ args) = ⦇ (checkRawTerm Γ σ arg) ∷ (checkRawArgs Γ Δ args) ⦈
    checkRawArgs _ _       _            = nothing

  Script[_↦_,_↦_,_↦_] :
    (Γᵣ  : RawCtxt)       (Γ  : Vec Sort (length Γᵣ))
    (Γᵣ′ : RawCtxt)       (Γ′ : Vec Sort (length Γᵣ′))
    (Ξᵣ  : RawOutputCtxt) (Ξ  : Vec OutputType (length Ξᵣ)) → Set
  Script[ _ ↦ Γ , _ ↦ Γ′ , _ ↦ Ξ ] = Script (Vec.toList Γ) (Vec.toList Γ′) (Vec.toList Ξ)

  checkRawScript : {Γᵣ Γᵣ′ : RawCtxt} {Ξᵣ : RawOutputCtxt}
    → (Γ : Vec Sort (length Γᵣ))
    → RawScript Γᵣ Γᵣ′ Ξᵣ
    → Maybe (∃[ Γ′ ] ∃[ Ξ ] Script[ Γᵣ ↦ Γ , Γᵣ′ ↦ Γ′ , Ξᵣ ↦ Ξ ])
  checkRawScript {Γᵣ} {.Γᵣ} {.[]} Γ []ᵣ =
    return $ Γ , [] , []
  checkRawScript Γ (`set-logicᵣ l scr) = do
    (Γ′ , Ξ , scr) ← checkRawScript Γ scr
    return $ Γ′ , Ξ , (`set-logic l scr)
  checkRawScript Γ (`declare-constᵣ _ ⋆ _) = nothing -- we never declare constants of type ⋆
  checkRawScript Γ (`declare-constᵣ n (TERM σᵣ) scr) = do
    σ ← checkSort σᵣ
    Γ′ , Ξ , scr ← checkRawScript (σ ∷ Γ) scr
    return $ Γ′ , Ξ , (`declare-const n σ scr)
  checkRawScript Γ (`assertᵣ x scr) = do
    x ← (checkRawTerm (Vec.toList Γ) BOOL x)
    (Γ′ , Ξ , scr) ← (checkRawScript Γ scr)
    return $ Γ′ , Ξ , (`assert x scr)
  checkRawScript Γ (`check-satᵣ scr) = do
    (Γ′ , Ξ , scr) ← checkRawScript Γ scr
    return $ Γ′ , SAT ∷ Ξ , (`check-sat scr)
  checkRawScript Γ (`get-modelᵣ scr) = do
    (Γ′ , Ξ , scr) ← checkRawScript Γ scr
    return $ Γ′ , MODEL (Vec.toList Γ) ∷ Ξ , (`get-model scr)

module _ where

  open import SMT.Theory.Raw.Reflection
  import Reflection.TypeChecking.Monad.Categorical as TC

  private
    open module TCMonad {ℓ} = Category.Monad.RawMonad {ℓ} TC.monad renaming (_⊛_ to _<*>_)

  reflectToScript : Rfl.Term → Rfl.TC (∃[ Γ ] Script [] Γ [])
  reflectToScript t = do
    (Γᵣ , scrᵣ) ← reflectToRawScript t
    case checkRawScript [] scrᵣ of λ where
      nothing → Rfl.typeErrorFmt "Ill-typed script:\n%s" (showRawScript scrᵣ)
      (just (Γ , [] , scr)) → return (Vec.toList Γ , scr)
