--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Defines the abstract syntax for SMT-LIB expressions:
--
-- Terms:
--   Schmitty defines a *subset* of SMT-LIB v2.6 terms. Notably, we omit
--   function symbols, data types and match expressions, annotations, and term
--   attributes.
--   See <http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf#section.3.6>.
--
-- Commands:
--   Schmitty defines a *subset* of SMT-LIB v2.6 commands. We include `assert`,
--   `check-sat`, `declare-const`, `get-model`, and `set-logic`. We omit the
--   remainder of the commands.
--   See <http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf#section.3.9>.
--
-- Scripts:
--   Scripts are lists of commands.
--
-- Models:
--   Models are lists of values.
--------------------------------------------------------------------------------

open import SMT.Theory.Base

module SMT.Script.Base (baseTheory : BaseTheory) where

open BaseTheory baseTheory

open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.List as List using (List; _∷_; []; _++_; _ʳ++_)
import Data.List.Properties as List
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any as Any using (here; there)
import Data.List.Relation.Binary.Subset.Propositional as Subset
import Data.List.Relation.Binary.Subset.Propositional.Properties as Subset
import Data.List.Relation.Binary.Subset.Propositional.ExtraProperties as Subset
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as Membership
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ; _<?_)
open import Data.Product as Prod using (∃; ∃-syntax; _×_; _,_)
open import Data.String as String using (String)
open import Data.Unit as Unit using (⊤)
open import Function using (_$_; _∘_; id)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Data.Environment as Env using (Env; _∷_; [])
import Reflection as Rfl
open import Text.Parser.String using (ParseErrorMsg; no-parse; ambiguous-parse)
open import Text.Printf

-------------------
-- SMT-LIB Terms --
-------------------

-- |Typing contexts.
Ctxt : Set
Ctxt = List Sort

private
  variable
    σ σ′ σ″ : Sort
    τ τ′ τ″ : Sort
    Γ Γ′ Γ″ : Ctxt
    δΓ      : Ctxt
    Δ Δ′    : Ctxt
    Σ       : Signature σ
    Σ′      : Signature σ′

-- |Well-typed variables.
_∋_ : (Γ : Ctxt) (σ : Sort) → Set
Γ ∋ σ = σ ∈ Γ

extendVar : Γ ∋ σ → (σ′ ∷ Γ) ∋ σ
extendVar = there

injectVar : (Γ : Ctxt) → Γ ∋ σ → (Γ ++ Γ′) ∋ σ
injectVar Γ = Subset.xs⊆xs++ys

raiseVar : (Γ′ : Ctxt) → Γ ∋ σ → (Γ′ ++ Γ) ∋ σ
raiseVar Γ = Subset.xs⊆ys++xs

reverseVar : (Γ {Γ′} : Ctxt) → (Γ ++ Γ′) ∋ σ → (Γ ʳ++ Γ′) ∋ σ
reverseVar Γ = Subset.↭⇒⊆ (Subset.++↭ʳ++ Γ _)

-- |SMT-LIB terms.
--
--  NOTE: match expressions are omitted, since we have no plans at the moment
--        to support datatype sorts.

mutual
  data Term (Γ : Ctxt) : (σ : Sort) → Set where
    `var           : ∀ {σ} (x : Γ ∋ σ) → Term Γ σ
    `lit           : ∀ {σ} (l : Literal σ) → Term Γ σ
    `app           : ∀ {σ} {Σ : Signature σ} (x : Identifier Σ) (xs : Args Γ (ArgSorts Σ)) → Term Γ σ
    `forall        : ∀ (n : String) (σ : Sort) (x : Term (σ ∷ Γ) BOOL) → Term Γ BOOL
    `exists        : ∀ (n : String) (σ : Sort) (x : Term (σ ∷ Γ) BOOL) → Term Γ BOOL
    `let           : ∀ (n : String) (σ : Sort) → Term Γ σ → Term (σ ∷ Γ) σ′ → Term Γ σ′

  Args : (Γ Δ : Ctxt) → Set
  Args Γ Δ = All (λ σ → Term Γ σ) Δ

Macro : (Σ : Signature σ) → Set
Macro {σ} Σ = ∀ {Γ} → Args Γ (ArgSorts Σ) → Term Γ σ

pattern `app₀ f       = `app f []
pattern `app₁ f x     = `app f (x ∷ [])
pattern `app₂ f x y   = `app f (x ∷ y ∷ [])
pattern `app₃ f x y z = `app f (x ∷ y ∷ z ∷ [])

private
  -- Add to stdlib
  lookup-∋ : ∀ i → List.lookup Γ i ≡ σ → Γ ∋ σ
  lookup-∋ {x ∷ Γ} zero    eq = here (Eq.sym eq)
  lookup-∋ {x ∷ Γ} (suc i) eq = there (lookup-∋ i eq)

-- |Helper function for writing variables.
#_ : {Γ : Ctxt} {σ : Sort} (n : ℕ)
     {n<∣Γ∣ : True (n <? List.length Γ)}
     {Γ∋σ : True (List.lookup Γ (Fin.fromℕ< (toWitness n<∣Γ∣)) ≟-Sort σ)} →
     Term Γ σ
#_ i {n<∣Γ∣} {Γ∋σ} = `var (lookup-∋ (Fin.fromℕ< (toWitness n<∣Γ∣)) (toWitness Γ∋σ))

Rename : Ctxt → Ctxt → Set
Rename = Subset._⊆_

extendRename : Rename Γ Γ′ → Rename (σ ∷ Γ) (σ ∷ Γ′)
extendRename = Subset.++⁺ʳ _

mutual
  renameTerm : Rename Γ Γ′ → Term Γ σ → Term Γ′ σ
  renameTerm r (`var i)        = `var (r i)
  renameTerm r (`lit l)        = `lit l
  renameTerm r (`app x xs)     = `app x (renameArgs r xs)
  renameTerm r (`forall n σ x) = `forall n σ (renameTerm (extendRename r) x)
  renameTerm r (`exists n σ x) = `exists n σ (renameTerm (extendRename r) x)
  renameTerm r (`let n σ x y)  = `let n σ (renameTerm r x) (renameTerm (extendRename r) y)

  renameArgs : Rename Γ Γ′ → Args Γ Δ → Args Γ′ Δ
  renameArgs r []       = []
  renameArgs r (x ∷ xs) = renameTerm r x ∷ renameArgs r xs

inject : (Γ : Ctxt) → Term Γ σ → Term (Γ ++ Γ′) σ
inject Γ = renameTerm (injectVar Γ)

raise : (Γ′ : Ctxt) → Term Γ σ → Term (Γ′ ++ Γ) σ
raise Γ′ = renameTerm (raiseVar Γ′)

reverse : (Γ : Ctxt) → Term (Γ ++ Γ′) σ → Term (Γ ʳ++ Γ′) σ
reverse Γ = renameTerm (reverseVar Γ)

---------------------
-- SMT-LIB Outputs --
---------------------

-- |SMT-LIB output types.
data OutputType : Set where
  SAT   : OutputType
  MODEL : Ctxt → OutputType

-- |Output contexts.
OutputCtxt : Set
OutputCtxt = List OutputType

private
  variable
    ξ ξ′    : OutputType
    Ξ Ξ′ δΞ : OutputCtxt


-- |SMT-LIB satisfiability.
data Sat : Set where
  sat     : Sat
  unsat   : Sat
  unknown : Sat

_≟-Sat_ : DecidableEquality Sat
sat     ≟-Sat sat     = yes refl
sat     ≟-Sat unsat   = no (λ ())
sat     ≟-Sat unknown = no (λ ())
unsat   ≟-Sat sat     = no (λ ())
unsat   ≟-Sat unsat   = yes refl
unsat   ≟-Sat unknown = no (λ ())
unknown ≟-Sat sat     = no (λ ())
unknown ≟-Sat unsat   = no (λ ())
unknown ≟-Sat unknown = yes refl

-- |SMT-LIB models.
--
-- The Model type *could* be defined as below, but it is defined as a
-- datatype of its own to help Rfl's reflection mechanism fill in the
-- implicit arguments during unquoting.
--
-- @
--   Model : (Γ : Ctxt) → Set
--   Model = Env (λ σ _Γ → Value σ)
-- @
--
data Model : (Γ : Ctxt) → Set where
  []  : Model []
  _∷_ : Value σ → Model Γ → Model (σ ∷ Γ)

QualifiedModel : (Γ : Ctxt) → Set
QualifiedModel Γ = ∃[ s ] (Model Γ if-sat s)
  where
    _if-sat_ : (A : Set) → Sat → Set
    A if-sat sat = A
    A if-sat _   = ⊤

-- |SMT-LIB script result.
Output : OutputType → Set
Output SAT       = Sat
Output (MODEL Γ) = QualifiedModel Γ

-- |List of SMT-LIB results.
--
-- The Outputs type *could* be defined as below, but it is defined as a
-- datatype of its own to help Rfl's reflection mechanism fill in the
-- implicit arguments during unquoting.
--
-- @
--   Outputs : (Ξ : OutputCtxt) → Set
--   Outputs = Env (λ ξ _Ξ → Output ξ)
-- @
--
data Outputs : (Ξ : OutputCtxt) → Set where
  []  : Outputs []
  _∷_ : Output ξ → Outputs Ξ → Outputs (ξ ∷ Ξ)


---------------------
-- Quoting outputs --
---------------------

-- |Quote a satisfiability result.
quoteSat : Sat → Rfl.Term
quoteSat sat     = Rfl.con (quote sat) []
quoteSat unsat   = Rfl.con (quote unsat) []
quoteSat unknown = Rfl.con (quote unknown) []

-- |Quote a model.
quoteModel : {Γ : Ctxt} → Model Γ → Rfl.Term
quoteModel [] =
  Rfl.con (quote Model.[]) []
quoteModel {σ ∷ Γ} (v ∷ vs) =
  Rfl.con (quote Model._∷_)
    $ Rfl.hArg Rfl.unknown
    ∷ Rfl.hArg (quoteSort σ)
    ∷ Rfl.vArg (quoteValue σ v)
    ∷ Rfl.vArg (quoteModel {Γ} vs) ∷ []

-- |Quote a qualified model.
quoteQualifiedModel : {Γ : Ctxt} → QualifiedModel Γ → Rfl.Term
quoteQualifiedModel {Γ} (s@sat , m) =
  Rfl.con (quote Prod._,_)
    $ Rfl.vArg (quoteSat s)
    ∷ Rfl.vArg (quoteModel {Γ} m)
    ∷ []
quoteQualifiedModel {Γ} (s@unsat , m) =
  Rfl.con (quote Prod._,_)
    $ Rfl.vArg (quoteSat s)
    ∷ Rfl.vArg (Rfl.con (quote Unit.tt) [])
    ∷ []
quoteQualifiedModel {Γ} (s@unknown , m) =
  Rfl.con (quote Prod._,_)
    $ Rfl.vArg (quoteSat s)
    ∷ Rfl.vArg (Rfl.con (quote Unit.tt) [])
    ∷ []

ValueInterps : Ctxt → Set
ValueInterps = All (λ _ → Rfl.Term)

-- |Quote a model as a list of values, applying interpValue.
quoteInterpValues : {Γ : Ctxt} → Model Γ → ValueInterps Γ
quoteInterpValues {[]}    []       = []
quoteInterpValues {σ ∷ Γ} (v ∷ vs) = interpValue (quoteValue σ v) ∷ quoteInterpValues {Γ} vs

-- |Quote a result.
quoteOutput : Output ξ → Rfl.Term
quoteOutput {SAT}     = quoteSat
quoteOutput {MODEL Γ} = quoteQualifiedModel {Γ}

-- |Quote a list of results.
quoteOutputs : Outputs Ξ → Rfl.Term
quoteOutputs [] =
  Rfl.con (quote Outputs.[]) $ []
quoteOutputs (r ∷ rs) =
  Rfl.con (quote Outputs._∷_)
    $ Rfl.vArg (quoteOutput r)
    ∷ Rfl.vArg (quoteOutputs rs) ∷ []

----------------------
-- SMT-LIB Commands --
----------------------

Logic : Set
Logic = String

-- |SMT-LIB commands.
--
--  NOTE: Scripts are lists of commands. Unfortunately, some commands,
--        such as `declare-const`, bind variables. Command has
--        two type-level arguments, `Γ` and `δΓ`, which represent the binding
--        context before executing the command, and the new variables bound
--        after executing the command. We use a similar trick to gather the
--        types of the outputs, using `Ξ` and `δΞ`.
--
data Command (Γ : Ctxt) : (δΓ : Ctxt) (δΞ : OutputCtxt) → Set where
  `set-logic     : (l : Logic) → Command Γ [] []
  `declare-const : (n : String) (σ : Sort) → Command Γ (σ ∷ []) []
  `assert        : Term Γ BOOL → Command Γ [] []
  `check-sat     : Command Γ [] (SAT ∷ [])
  `get-model     : Command Γ [] (MODEL Γ ∷ [])


---------------------
-- SMT-LIB Scripts --
---------------------

-- |SMT-LIB scripts.
data Script (Γ : Ctxt) : (Γ′ : Ctxt) (Ξ : OutputCtxt) → Set where
  []  : Script Γ Γ []
  _∷_ : Command Γ δΓ δΞ → Script (δΓ ++ Γ) Γ′ Ξ → Script Γ Γ′ (δΞ ++ Ξ)

infixr 5 _◆_

_◆_ : Script Γ Γ′ Ξ → Script Γ′ Γ″ Ξ′ → Script Γ Γ″ (Ξ ++ Ξ′)
_◆_ {Ξ′ = Ξ′} [] scr′ = scr′
_◆_ {Ξ′ = Ξ′} (_∷_ {δΞ = δΞ} {Ξ = Ξ} cmd scr) scr′ rewrite List.++-assoc δΞ Ξ Ξ′ = cmd ∷ (scr ◆ scr′)

--------------------
-- Useful aliases --
--------------------

Var : Ctxt → Set
Var Γ = ∃[ σ ] (Γ ∋ σ)

Val : Set
Val = ∃[ σ ] (Value σ)

Defn : Ctxt → Set
Defn Γ = ∃[ σ ] (Γ ∋ σ × Value σ)


----------------------
-- Useful functions --
----------------------

`declare-named-consts : (δΓ : Ctxt) → (name : String) → Script (δΓ ʳ++ Γ) Γ′ Ξ → Script Γ Γ′ Ξ
`declare-named-consts {Γ} []       name scr = scr
`declare-named-consts {Γ} (σ ∷ δΓ) name scr
  rewrite List.ʳ++-++ (σ ∷ []) {δΓ} {Γ} = `declare-const name σ ∷ `declare-named-consts δΓ name scr

`declare-consts : (δΓ : Ctxt) → Script (δΓ ʳ++ Γ) Γ′ Ξ → Script Γ Γ′ Ξ
`declare-consts δΓ scr = `declare-named-consts δΓ "_" scr

VarNames : Ctxt → Set
VarNames = All (λ _ → String)

scriptVarNames : Script [] Γ Ξ → VarNames Γ
scriptVarNames s = scriptVarNames′ s []
  where
    scriptVarNames′ : Script Γ′ Γ Ξ → VarNames Γ′ → VarNames Γ
    scriptVarNames′ [] acc = acc
    scriptVarNames′ (`set-logic l       ∷ s) acc = scriptVarNames′ s acc
    scriptVarNames′ (`declare-const x σ ∷ s) acc = scriptVarNames′ s (x ∷ acc)
    scriptVarNames′ (`assert x          ∷ s) acc = scriptVarNames′ s acc
    scriptVarNames′ (`check-sat         ∷ s) acc = scriptVarNames′ s acc
    scriptVarNames′ (`get-model         ∷ s) acc = scriptVarNames′ s acc

----------------------
-- Parser utilities --
----------------------

-- |Format a parser error to the user.
parseErrorMsg : ParseErrorMsg →  String
parseErrorMsg no-parse        = "Failed to parse output"
parseErrorMsg ambiguous-parse = "Ambiguous parse of output"

-- |Display a parser error to the user.
parseError : ∀ {a} {A : Set a} (output : String) (errMsg : ParseErrorMsg) (cmd : String) (input : String) → Rfl.TC A
parseError output errMsg cmd input = Rfl.typeError (Rfl.strErr msg ∷ [])
  where msg = printf "%s:\n\n%s\nwhen running script:\n\n%s\n%s" (parseErrorMsg errMsg) output cmd input
