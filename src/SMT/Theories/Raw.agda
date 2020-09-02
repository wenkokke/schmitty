-- This module contains the definition of the 'Raw' theory, which is intended to
-- be targeted by a translation from reflected Agda syntax. It re-exports the
-- basic definitions from SMT.Script.Base, the type names prefixed with 'Raw'.
module SMT.Theories.Raw where

open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.List as List using (List; []; _∷_)
open import Data.String as String using (String)
open import Data.Unit as Unit using (⊤; tt)
open import Function using (id)
import Reflection as Rfl
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theory

baseTheory : BaseTheory
BaseTheory.Sort       baseTheory = ⊤
BaseTheory._≟-Sort_   baseTheory = λ _ _ → yes refl
BaseTheory.BOOL       baseTheory = tt
BaseTheory.Value      baseTheory = λ _ → ⊥
BaseTheory.Literal    baseTheory = λ _ → Rfl.Term
BaseTheory.Identifier baseTheory = λ _ → Rfl.Name
BaseTheory.quoteSort  baseTheory = λ _ → Rfl.con (quote tt) []
BaseTheory.quoteValue baseTheory = λ _ → ⊥-elim

printable : Printable baseTheory
Printable.showSort       printable = λ _ → "⋆"
Printable.showLiteral    printable = Rfl.showTerm
Printable.showIdentifier printable = Rfl.showName

-- Export basic constructs from SMT.Script.Base, renamed to use 'Raw' whenever
-- conflicts with other theories are possible.
open import SMT.Script.Base baseTheory as RawScript public
  renaming ( Ctxt    to RawCtxt
           ; Term    to RawTerm
           ; Args    to RawArgs
           ; Command to RawCommand
           ; Script  to RawScript
           )
  using      -- Term
           ( var
           ; lit
           ; app
           ; forAll
           ; exists
             -- Command
           ; set-logic
           ; declare-const
           ; assert
           ; check-sat
           ; get-model
             -- Script
           ; []
           ; _∷_
           )

-- Define a raw variable, instead of re-exporting _∋_, since there is only a
-- single sort, so exposing the sort at the type-level is pointless.
RawVar : RawCtxt → Set
RawVar Γ = Γ RawScript.∋ tt
