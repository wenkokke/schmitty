-- This module contains the definition of the 'Raw' theory, which is intended to
-- be targeted by a translation from reflected Agda syntax. It re-exports the
-- basic definitions from SMT.Script.Base, the type names prefixed with 'Raw'.
module SMT.Theories.Raw.Base where

open import Data.Empty as Empty using (⊥; ⊥-elim)
open import Data.Environment as Env using (Env; []; _∷_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.List as List using (List; []; _∷_)
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂)
open import Data.String as String using (String)
open import Data.Unit as Unit public using () renaming (⊤ to RawSort; tt to ⋆)
open import Function using (id)
import Reflection as Rfl
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theory
open import Text.Parser.String


rawBaseTheory : BaseTheory
BaseTheory.Sort       rawBaseTheory = RawSort
BaseTheory._≟-Sort_   rawBaseTheory = λ _ _ → yes refl
BaseTheory.BOOL       rawBaseTheory = ⋆
BaseTheory.Value      rawBaseTheory = λ _ → ⊥
BaseTheory.Literal    rawBaseTheory = λ _ → Rfl.Term
BaseTheory.Identifier rawBaseTheory = λ _ → Rfl.Name
BaseTheory.quoteSort  rawBaseTheory = λ _ → Rfl.con (quote ⋆) []
BaseTheory.quoteValue rawBaseTheory = λ _ → ⊥-elim

rawPrintable : Printable rawBaseTheory
Printable.showSort       rawPrintable = λ _ → "⋆"
Printable.showLiteral    rawPrintable = Rfl.showTerm
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
  renaming ( OutputType    to RawOutputType
           ; OutputCtxt    to RawOutputCtxt
           ; Ctxt          to RawCtxt
           ; _∋_           to _∋ᵣ_
           ; Term          to RawTerm
           ; var           to varᵣ
           ; lit           to litᵣ
           ; app           to appᵣ
           ; forAll        to forAllᵣ
           ; exists        to existsᵣ
           ; Args          to RawArgs
           ; Command       to RawCommand
           ; set-logic     to set-logicᵣ
           ; declare-const to declare-constᵣ
           ; assert        to assertᵣ
           ; check-sat     to check-satᵣ
           ; get-model     to get-modelᵣ
           ; Script        to RawScript
           ; []            to []ᵣ
           ; _∷_           to _∷ᵣ_
           )

open import SMT.Script.Names rawBaseTheory using (x′es)
open import SMT.Script.Show rawTheory using (showScriptS)

showRawScript : {Γᵣ : RawCtxt} {Ξᵣ : RawOutputCtxt} → RawScript [] Γᵣ Ξᵣ → String
showRawScript scrᵣ = String.unlines (proj₁ (proj₁ (showScriptS scrᵣ (x′es , []))))

-- Define a raw variable, instead of re-exporting _∋_, since there is only a
-- single sort, so exposing the sort at the type-level is pointless.
RawVar : RawCtxt → Set
RawVar Γ = Γ ∋ᵣ ⋆
