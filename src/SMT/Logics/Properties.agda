{-# OPTIONS --without-K --safe #-}

module SMT.Logics.Properties where

open import Data.Nat as Nat using (ℕ)
import Data.Nat.Induction as WfNat
open import Data.Product using (∃-syntax; _×_; _,_)
open import Function using (_on_)
open import Induction.WellFounded as WF using (WellFounded)
open import Relation.Nullary.Decidable as Dec using (True; toWitness)
open import Relation.Binary using (Irreflexive; Asymmetric)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Logics

private
  variable
    l l₁ l₂ l₃ : Logic

-- |The ⇾-relation is irreflexive.
⇾-irreflexive : Irreflexive _≡_ _⇾_
⇾-irreflexive refl ()

-- |The ⇾-relation is asymmetric.
⇾-asymmetric : Asymmetric _⇾_
⇾-asymmetric QF-IDL⇾QF-LIA ()
⇾-asymmetric QF-LIA⇾QF-NIA ()
⇾-asymmetric NIA⇾UFNIA ()
⇾-asymmetric UFNIA⇾AUFNIRA ()
⇾-asymmetric QF-LIA⇾LIA ()
⇾-asymmetric LIA⇾AUFLIRA ()
⇾-asymmetric AUFLIRA⇾AUFNIRA ()
⇾-asymmetric LIA⇾ALIA ()
⇾-asymmetric ALIA⇾AUFLIA ()
⇾-asymmetric QF-LIA⇾QF-ALIA ()
⇾-asymmetric QF-ALIA⇾QF-AUFLIA ()
⇾-asymmetric QF-AUFLIA⇾AUFLIA ()
⇾-asymmetric QF-LIA⇾QF-UFLIA ()
⇾-asymmetric QF-UFLIA⇾QF-AUFLIA ()
⇾-asymmetric QF-UFLIA⇾QF-UFNIA ()
⇾-asymmetric QF-UFNIA⇾UFNIA ()
⇾-asymmetric QF-IDL⇾QF-UFIDL ()
⇾-asymmetric QF-UFIDL⇾QF-UFLIA ()
⇾-asymmetric QF-UF⇾QF-UFIDL ()
⇾-asymmetric QF-UF⇾QF-UFLRA ()
⇾-asymmetric QF-UFLRA⇾UFLRA ()
⇾-asymmetric UFLRA⇾AUFLIRA ()
⇾-asymmetric QF-UFLRA⇾QF-UFNRA ()
⇾-asymmetric QF-UFNRA⇾AUFNIRA ()
⇾-asymmetric QF-UF⇾QF-UFBV ()
⇾-asymmetric QF-UFBV⇾QF-AUFBV ()
⇾-asymmetric QF-BV⇾QF-UFBV ()
⇾-asymmetric QF-BV⇾QF-ABV ()
⇾-asymmetric QF-ABV⇾QF-AUFBV ()
⇾-asymmetric QF-RDL⇾QF-LRA ()
⇾-asymmetric QF-LRA⇾QF-UFNRA ()
⇾-asymmetric QF-LRA⇾LRA ()
⇾-asymmetric LRA⇾UFLRA ()
⇾-asymmetric LRA⇾NRA ()
⇾-asymmetric NRA⇾AUFNIRA ()
⇾-asymmetric QF-LRA⇾QF-NRA ()
⇾-asymmetric QF-NRA⇾NRA ()

-- |The depth of a logic is the logiest path from any of the depth 0 logics.
--
--  NOTE: We are defining depth to help us induce a proof that _⇾_ and its
--        transitive closure _<_ are well-founded relations.
--
depth : Logic → ℕ
depth QF-AX     = 0
depth QF-IDL    = 0
depth QF-LIA    = 1
depth QF-NIA    = 2
depth NIA       = 3
depth UFNIA     = 4
depth AUFNIRA   = 5
depth LIA       = 2
depth AUFLIRA   = 4
depth ALIA      = 3
depth AUFLIA    = 4
depth QF-ALIA   = 2
depth QF-AUFLIA = 3
depth QF-UFIDL  = 1
depth QF-UFLIA  = 2
depth QF-UFNIA  = 3
depth QF-UF     = 0
depth QF-UFLRA  = 1
depth UFLRA     = 3
depth QF-UFNRA  = 3
depth QF-UFBV   = 1
depth QF-AUFBV  = 2
depth QF-BV     = 0
depth QF-ABV    = 1
depth QF-RDL    = 0
depth QF-LRA    = 1
depth NRA       = 3
depth LRA       = 2
depth QF-NRA    = 2

private
  auto : ∀ {n₁ n₂} {p : True (n₁ Nat.<? n₂)} → n₁ Nat.< n₂
  auto {p = p} = toWitness p

-- |The ⇾-relation respects depth.
⇾-depth : l₁ ⇾ l₂ → depth l₁ Nat.< depth l₂
⇾-depth QF-IDL⇾QF-LIA      = auto
⇾-depth QF-LIA⇾QF-NIA      = auto
⇾-depth QF-NIA⇾NIA         = auto
⇾-depth NIA⇾UFNIA          = auto
⇾-depth UFNIA⇾AUFNIRA      = auto
⇾-depth QF-LIA⇾LIA         = auto
⇾-depth LIA⇾NIA            = auto
⇾-depth LIA⇾AUFLIRA        = auto
⇾-depth AUFLIRA⇾AUFNIRA    = auto
⇾-depth LIA⇾ALIA           = auto
⇾-depth ALIA⇾AUFLIA        = auto
⇾-depth QF-LIA⇾QF-ALIA     = auto
⇾-depth QF-ALIA⇾ALIA       = auto
⇾-depth QF-ALIA⇾QF-AUFLIA  = auto
⇾-depth QF-AUFLIA⇾AUFLIA   = auto
⇾-depth QF-LIA⇾QF-UFLIA    = auto
⇾-depth QF-UFLIA⇾QF-AUFLIA = auto
⇾-depth QF-UFLIA⇾QF-UFNIA  = auto
⇾-depth QF-UFNIA⇾UFNIA     = auto
⇾-depth QF-IDL⇾QF-UFIDL    = auto
⇾-depth QF-UFIDL⇾QF-UFLIA  = auto
⇾-depth QF-UF⇾QF-UFIDL     = auto
⇾-depth QF-UF⇾QF-UFLRA     = auto
⇾-depth QF-UFLRA⇾UFLRA     = auto
⇾-depth UFLRA⇾AUFLIRA      = auto
⇾-depth QF-UFLRA⇾QF-UFNRA  = auto
⇾-depth QF-UFNRA⇾AUFNIRA   = auto
⇾-depth QF-UF⇾QF-UFBV      = auto
⇾-depth QF-UFBV⇾QF-AUFBV   = auto
⇾-depth QF-BV⇾QF-UFBV      = auto
⇾-depth QF-BV⇾QF-ABV       = auto
⇾-depth QF-ABV⇾QF-AUFBV    = auto
⇾-depth QF-RDL⇾QF-LRA      = auto
⇾-depth QF-LRA⇾QF-UFNRA    = auto
⇾-depth QF-LRA⇾LRA         = auto
⇾-depth LRA⇾UFLRA          = auto
⇾-depth LRA⇾NRA            = auto
⇾-depth NRA⇾AUFNIRA        = auto
⇾-depth QF-LRA⇾QF-NRA      = auto
⇾-depth QF-NRA⇾QF-UFNRA    = auto
⇾-depth QF-NRA⇾NRA         = auto

private
  module <-depth⇒< = WF.InverseImage {_<_ = Nat._<_} depth
  module ⇾⇒<-depth = WF.Subrelation {_<₁_ = _⇾_} {_<₂_ = Nat._<_ on depth} ⇾-depth
  module ⊂⇒⇾ = WF.TransitiveClosure _⇾_

open ⊂⇒⇾ renaming (_<⁺_ to _⊂_) using ([_]; trans)

-- |The ⇾-relation is well-founded via depth.
⇾-wellFounded : WellFounded _⇾_
⇾-wellFounded = ⇾⇒<-depth.wellFounded (<-depth⇒<.wellFounded WfNat.<-wellFounded)

-- |The ⇾⁺-relation is a subrelation of the ⊂-relation.
⇾⁺-⊂ : l₁ ⇾⁺ l₃ → l₁ ⊂ l₃
⇾⁺-⊂ [ l₁⇾l₃ ] = [ l₁⇾l₃ ]
⇾⁺-⊂ (l₁⇾l₂ ∷ l₂⇾⁺l₃) = trans [ l₁⇾l₂ ] (⇾⁺-⊂ l₂⇾⁺l₃)

private
  module ⇾⁺⇒⊂ = WF.Subrelation {_<₁_ = _⇾⁺_} {_<₂_ = _⊂_} ⇾⁺-⊂

-- |The ⇾⁺-relation is well-founded.
⇾⁺-wellFounded : WellFounded _⇾⁺_
⇾⁺-wellFounded = ⇾⁺⇒⊂.wellFounded (⊂⇒⇾.wellFounded ⇾-wellFounded)


