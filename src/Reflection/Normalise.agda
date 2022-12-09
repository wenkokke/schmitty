
module Reflection.Normalise where

open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; nothing; just; _<∣>_)
open import Data.List
open import Data.List.Relation.Unary.All as All using (All; _∷_; [])
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit
open import Function

open import Reflection
open import Reflection.TCM.Effectful using (applicative)

open import Reflection.AST.Universe
open import Reflection.AnnotatedAST
open import Reflection.AnnotatedAST.Free

private
  Ann : ∀ {k} → ⟦ k ⟧ → Set
  Ann _ = Maybe Meta × Bool × List ℕ

private
  normalise? : Univ → Maybe Meta × Bool × List ℕ → Bool
  normalise? _      (just _ , _ , _) = true -- this will block
  normalise? ⟨term⟩ (_ , false , []) = true
  normalise? _      _                = false

  action : ∀ {k} {t : ⟦ k ⟧} → Annotated Ann t → TC ⟦ k ⟧
  action (⟨ just m , _ , _ ⟩ _) = blockOnMeta m
  action {⟨term⟩} {t = t} _     = normalise t
  action {t = t} _              = return t

  hasBinder : AnnotationFun (λ _ → Bool)
  hasBinder (⟨abs⟩ _) _ = true
  hasBinder = defaultAnn false _∨_

  hasMeta : AnnotationFun (λ _ → Maybe Meta)
  hasMeta ⟨term⟩ (meta x _) = just x
  hasMeta = defaultAnn nothing _<∣>_

open Traverse applicative

blockOnAnyMeta : Term → TC Term
blockOnAnyMeta t = traverse (λ { nothing → false; (just _) → true })
                            (λ { {t = t} (⟨ nothing ⟩ _) → return t; (⟨ just m ⟩ _) → blockOnMeta m })
                            (annotate hasMeta t)

-- Normalise closed subterms with no binders of a term
normaliseClosed : Term → TC Term
normaliseClosed t = traverse (λ {k} → normalise? k) action (annotate (hasMeta ⊗ hasBinder ⊗ freeVars) t)
