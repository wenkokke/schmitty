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
import Reflection as Rfl
open import Reflection.AST.Term using () renaming (_≟_ to _≟-Term_)
open import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import SMT.Theory.Base
open import SMT.Theory.Class.Parsable
open import SMT.Theory.Class.Printable
open import SMT.Theory.Class.Solvable
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
TERM t ≟-RawSort TERM t′ = Dec.map (Function.mk⇔ (cong TERM) TERM-injective) (t ≟-Term t′)

rawTheory : Theory
Theory.Sort        rawTheory = RawSort
Theory._≟-Sort_    rawTheory = _≟-RawSort_
Theory.BOOL        rawTheory = ⋆
Theory.Value       rawTheory = λ _ → ⊥
Theory.Literal     rawTheory = λ _ → Rfl.Literal
Theory.Identifier  rawTheory = λ _ → Rfl.Name
Theory.quoteSort   rawTheory = λ _ → Rfl.con (quote ⋆) []
Theory.quoteValue  rawTheory = λ _ → ⊥-elim
Theory.interpValue rawTheory = λ t → t

instance
  rawPrintable : Printable rawTheory
  Printable.showSort       rawPrintable = λ _ → "⋆"
  Printable.showLiteral    rawPrintable = Rfl.showLiteral
  Printable.showIdentifier rawPrintable = Rfl.showName

  rawParsable : Parsable rawTheory
  Parsable.parseSort  rawParsable = ⋆ <$ lexeme "⋆"
  Parsable.parseValue rawParsable = λ _ → fail

  rawSolvable : Solvable rawTheory
  rawSolvable = makeSolvable rawTheory


-- Export basic constructs from SMT.Script.Base, renamed to use 'Raw' whenever
-- conflicts with other theories are possible.
open import SMT.Script.Base rawTheory public
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
           ; `set-logic      to `set-logicᵣ
           ; `declare-const  to `declare-constᵣ
           ; `assert         to `assertᵣ
           ; `check-sat      to `check-satᵣ
           ; `get-model      to `get-modelᵣ
           ; Script          to RawScript
           ; []              to []ᵣ
           )

open import SMT.Script.Names rawTheory using (x′es)

showRawScript : {Γᵣ : RawCtxt} {Ξᵣ : RawOutputCtxt} → RawScript [] Γᵣ Ξᵣ → String
showRawScript scrᵣ = proj₁ (Solvable.toSMTLIBWithOutputParser rawSolvable scrᵣ)

-- Define a raw variable, instead of re-exporting _∋_, since there is only a
-- single sort, so exposing the sort at the type-level is pointless.
RawVar : RawCtxt → Set
RawVar Γ = Γ ∋ᵣ ⋆
