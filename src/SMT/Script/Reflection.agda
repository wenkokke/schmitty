open import SMT.Theory
open import SMT.Theory.Reflection

module SMT.Script.Reflection (theory : Theory) (reflectable : Reflectable theory) where

open import Category.Monad
open import Data.Environment as Env using (Env; _∷_; [])
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.List as List using (List; _∷_; []; _++_; length)
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Logics
open Theory theory
open Reflectable reflectable
open import SMT.Script.Base baseTheory
open import SMT.Script.Show theory
open import SMT.Theories.Raw as Raw using (showRawScript)

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

  open import SMT.Theories.Raw

  private
    monadPlusMaybe = MaybeCat.monadPlus {Level.zero}

  open RawMonadPlus monadPlusMaybe renaming (_⊛_ to _<*>_)


  private
    variable
      Γᵣ Γᵣ′ δΓᵣ : RawCtxt
      Ξᵣ Ξᵣ′ δΞᵣ : RawOutputCtxt
      Δᵣ Δᵣ′ : RawCtxt

  checkRawVar : (Γ : Ctxt) (σ : Sort) (n : ℕ) → Maybe (Γ ∋ σ)
  checkRawVar []       σ n       = nothing
  checkRawVar (σ′ ∷ Γ) σ zero    = ⦇ (zero ,_) (Maybe.decToMaybe (σ′ ≟-Sort σ)) ⦈
  checkRawVar (σ′ ∷ Γ) σ (suc n) = ⦇ extendVar (checkRawVar Γ σ n) ⦈

  mutual
    checkRawTerm : (Γ : Ctxt) (σ : Sort) → RawTerm Γᵣ ⋆ → Maybe (Term Γ σ)
    checkRawTerm Γ σ (varᵣ n) = do
      x ← checkRawVar Γ σ (Fin.toℕ (proj₁ n))
      return $ var x
    checkRawTerm Γ σ (litᵣ l) = do
      l ← checkLiteral σ l
      return $ lit l
    checkRawTerm Γ σ (appᵣ f args) = do
      (Σ , f) ← checkIdentifier σ f
      args ← checkRawArgs Γ (ArgSorts Σ) args
      return $ f args
    checkRawTerm Γ σ (forAllᵣ ⋆ x) = do
      refl ← Maybe.decToMaybe (σ ≟-Sort BOOL)
      checkRawQ forAll Γ x
    checkRawTerm Γ σ (existsᵣ ⋆ x) = do
      refl ← Maybe.decToMaybe (σ ≟-Sort BOOL)
      checkRawQ exists Γ x

    checkRawQ : (q : ∀ {Γ} σ → Term (σ ∷ Γ) BOOL → Term Γ BOOL) (Γ : Ctxt) → RawTerm Γᵣ ⋆ → Maybe (Term Γ BOOL)
    checkRawQ q Γ x
      = List.foldr Maybe._<∣>_ nothing
      $ List.map (λ σ′ → ⦇ (q σ′) (checkRawTerm (σ′ ∷ Γ) BOOL x) ⦈ ) sorts

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
  checkRawScript Γ (set-logicᵣ l ∷ᵣ scr) = do
    (Γ′ , Ξ , scr) ← checkRawScript Γ scr
    return $ Γ′ , Ξ , (set-logic l ∷ scr)
  checkRawScript Γ (declare-constᵣ x ⋆ ∷ᵣ scr)
    = List.foldr Maybe._<∣>_ nothing
    $ flip List.map sorts $ λ σ → do
      (Γ′ , Ξ , scr) ← checkRawScript (σ ∷ Γ) scr
      return $ Γ′ , Ξ , (declare-const x σ ∷ scr)
  checkRawScript Γ (assertᵣ x ∷ᵣ scr) = do
    x ← (checkRawTerm (Vec.toList Γ) BOOL x)
    (Γ′ , Ξ , scr) ← (checkRawScript Γ scr)
    return $ Γ′ , Ξ , (assert x ∷ scr)
  checkRawScript Γ (check-satᵣ ∷ᵣ scr) = do
    (Γ′ , Ξ , scr) ← checkRawScript Γ scr
    return $ Γ′ , SAT ∷ Ξ , (check-sat ∷ scr)
  checkRawScript Γ (get-modelᵣ ∷ᵣ scr) = do
    (Γ′ , Ξ , scr) ← checkRawScript Γ scr
    return $ Γ′ , MODEL (Vec.toList Γ) ∷ Ξ , (get-model ∷ scr)

module _ where

  open import SMT.Theories.Raw.Reflection
  import Reflection.TypeChecking.Monad.Categorical as TC

  private
    open module TCMonad {ℓ} = Category.Monad.RawMonad {ℓ} TC.monad renaming (_⊛_ to _<*>_)

  reflectToScript : Rfl.Term → Rfl.TC (∃[ Γ ] Script [] Γ [])
  reflectToScript t = do
    (Γᵣ , scrᵣ) ← reflectToRawScript t
    case checkRawScript [] scrᵣ of λ where
      nothing → Rfl.typeErrorFmt "Ill-typed script:\n%s" (showRawScript scrᵣ)
      (just (Γ , [] , scr)) → return (Vec.toList Γ , scr)
