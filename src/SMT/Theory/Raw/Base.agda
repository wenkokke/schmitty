{-# OPTIONS --guardedness #-}

--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- This module contains the definition of the raw theory, whose identifiers are
-- reflected Agda names and whose literals are reflected Agda literals. The raw
-- theory does not correspond to any SMT-LIB theory. Instead, it is intended as
-- an intermediate language between reflected Agda syntax and the various
-- SMT-LIB theories.
--
-- This module re-exports the basic definitions from `SMT.Script.Base`, with the
-- type names prefixed with `Raw` and the symbols suffixed with `ᵣ`, e.g.,
-- `RawScript` and `varᵣ`.
--------------------------------------------------------------------------------

module SMT.Theory.Raw.Base where

open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Environment as Env using (Env; []; _∷_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.List as List using (List; []; _∷_)
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂)
open import Data.String as String using (String)
open import Function using (id)
open import Function.Equivalence using (equivalence)
import Reflection as Rfl
open import Reflection.Term using () renaming (_≟_ to _≟-Term_)
open import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import SMT.Theory.Base
open import Text.Parser.String

data RawSort : Set where
  ⋆    : RawSort
  TERM : Rfl.Term → RawSort

TERM-injective : ∀ {t t′} → TERM t ≡ TERM t′ → t ≡ t′
TERM-injective refl = refl

_≟-RawSort_ : (σ σ′ : RawSort) → Dec (σ ≡ σ′)
⋆      ≟-RawSort ⋆       = yes refl
⋆      ≟-RawSort TERM _  = no λ()
TERM x ≟-RawSort ⋆       = no λ()
TERM t ≟-RawSort TERM t′ = Dec.map (equivalence (cong TERM) TERM-injective) (t ≟-Term t′)

rawBaseTheory : BaseTheory
BaseTheory.Sort        rawBaseTheory = RawSort
BaseTheory._≟-Sort_    rawBaseTheory = _≟-RawSort_
BaseTheory.BOOL        rawBaseTheory = ⋆
BaseTheory.Value       rawBaseTheory = λ _ → ⊥
BaseTheory.Literal     rawBaseTheory = λ _ → Rfl.Literal
BaseTheory.Identifier  rawBaseTheory = λ _ → Rfl.Name
BaseTheory.quoteSort   rawBaseTheory = λ _ → Rfl.con (quote ⋆) []
BaseTheory.quoteValue  rawBaseTheory = λ _ → ⊥-elim
BaseTheory.interpValue rawBaseTheory = λ t → t

rawPrintable : Printable rawBaseTheory
Printable.showSort       rawPrintable = λ _ → "⋆"
Printable.showLiteral    rawPrintable = Rfl.showLiteral
Printable.showIdentifier rawPrintable = Rfl.showName

rawParsable : Parsable rawBaseTheory
Parsable.parseSort  rawParsable = ⋆ <$ lexeme "⋆"
Parsable.parseValue rawParsable = λ _ → fail

rawTheory : Theory
Theory.baseTheory  rawTheory = rawBaseTheory
Theory.printable   rawTheory = rawPrintable
Theory.parsable    rawTheory = rawParsable


-- Export basic constructs from SMT.Script.Base, renamed to use 'Raw' whenever
-- conflicts with other theories are possible.
open import SMT.Script.Base rawBaseTheory public
  using ()
  renaming ( OutputType      to RawOutputType
           ; OutputCtxt      to RawOutputCtxt
           ; Ctxt            to RawCtxt
           ; _∋_             to _∋ᵣ_
           ; Term            to RawTerm
           ; `var            to `varᵣ
           ; `lit            to `litᵣ
           ; `app            to `appᵣ
           ; `forall         to `forallᵣ
           ; `exists         to `existsᵣ
           ; `let            to `letᵣ
           ; Args            to RawArgs
           ; Command         to RawCommand
           ; `set-logic      to `set-logicᵣ
           ; `declare-const  to `declare-constᵣ
           ; `assert         to `assertᵣ
           ; `check-sat      to `check-satᵣ
           ; `get-model      to `get-modelᵣ
           ; Script          to RawScript
           ; []              to []ᵣ
           ; _∷_             to _∷ᵣ_
           )

open import SMT.Script.Names rawBaseTheory using (x′es)
open import SMT.Script.Show rawTheory using (showScriptS)

showRawScript : {Γᵣ : RawCtxt} {Ξᵣ : RawOutputCtxt} → RawScript [] Γᵣ Ξᵣ → String
showRawScript scrᵣ = String.unlines (proj₁ (proj₁ (showScriptS scrᵣ (x′es , []))))

-- Define a raw variable, instead of re-exporting _∋_, since there is only a
-- single sort, so exposing the sort at the type-level is pointless.
RawVar : RawCtxt → Set
RawVar Γ = Γ ∋ᵣ ⋆
