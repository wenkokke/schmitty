module SMT.Theories.Raw where

open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.List as List using (List; []; _∷_)
open import Data.String as String using (String)
open import Data.Unit as Unit using (⊤)
open import Function using (id)
import Reflection as Rfl
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theory

baseTheory : BaseTheory
BaseTheory.Sort       baseTheory = ⊤
BaseTheory._≟-Sort_   baseTheory = λ _ _ → yes refl
BaseTheory.BOOL       baseTheory = Unit.tt
BaseTheory.Value      baseTheory = λ _ → ⊥
BaseTheory.Literal    baseTheory = λ _ → Rfl.Term
BaseTheory.Identifier baseTheory = λ _ → Rfl.Name
BaseTheory.quoteSort  baseTheory = λ _ → Rfl.con (quote Unit.tt) []
BaseTheory.quoteValue baseTheory = λ _ → ⊥-elim

printable : Printable baseTheory
Printable.showSort       printable = λ _ → "⋆"
Printable.showLiteral    printable = Rfl.showTerm
Printable.showIdentifier printable = Rfl.showName
