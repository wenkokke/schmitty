
module Reflection.DeBruijn where

open import Level using () renaming (zero to ℓ₀)
open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<?_; _≡ᵇ_)
open import Data.List
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Reflection hiding (_≟_)
open import Reflection.Argument.Visibility
import Reflection.Traversal as Traverse
open import Function.Identity.Categorical as Identity using (Identity)
open import Category.Applicative

---------------
-- Weakening --
---------------

module _ (n : ℕ) (k : ℕ) where

  open Traverse Identity.applicative

  private

    wkVar : Cxt → ℕ → ℕ
    wkVar (n , _) i = if isYes (i <? n) then i else i + k

    wkActions : Actions
    wkActions = record defaultActions { onVar = wkVar }

  weakenUnder : Term → Term
  weakenUnder = traverseTerm wkActions (n , []) -- not using the context part

  weakenUnderArgs : Args Term → Args Term
  weakenUnderArgs = traverseArgs wkActions (n , [])

  weakenUnderClauses : Clauses → Clauses
  weakenUnderClauses = traverseClauses wkActions (n , [])

weaken : ℕ → Term → Term
weaken = weakenUnder 0

weakenArgs : ℕ → Args Term → Args Term
weakenArgs = weakenUnderArgs 0

weakenClauses : ℕ → Clauses → Clauses
weakenClauses = weakenUnderClauses 0

private
  η : Visibility → (Args Term → Term) → Args Term → Term
  η h f args = lam h (abs "x" (f (weakenArgs 1 args ++ arg (arg-info h relevant) (var 0 []) ∷ [])))

η-expand : Visibility → Term → Term
η-expand h (var x      args) = η h (var (suc x)) args
η-expand h (con c      args) = η h (con c) args
η-expand h (def f      args) = η h (def f) args
η-expand h (pat-lam cs args) = η h (pat-lam (weakenClauses 1 cs)) args
η-expand h (meta x     args) = η h (meta x) args
η-expand h t@(lam _ _)       = t
η-expand h t@(pi _ _)        = t
η-expand h t@(agda-sort _)   = t
η-expand h t@(lit _)         = t
η-expand h t@unknown         = t

--------------------
-- Free variables --
--------------------

module _ (i : ℕ) where

  private
    anyApplicative : RawApplicative (λ _ → Bool)
    anyApplicative .RawApplicative.pure _ = false
    anyApplicative .RawApplicative._⊛_    = _∨_

  open Traverse anyApplicative

  private
    fvVar : Cxt → ℕ → Bool
    fvVar (n , _) x = i + n ≡ᵇ x

    actions = record defaultActions { onVar = fvVar }

  _∈FV_ : Term → Bool
  _∈FV_ = traverseTerm actions (0 , [])
