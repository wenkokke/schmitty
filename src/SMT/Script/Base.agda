open import SMT.Theory

module SMT.Script.Base (baseTheory : BaseTheory) where

open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.List as List using (List; _∷_; []; _++_; _ʳ++_)
import Data.List.Properties as List
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.List.Relation.Unary.All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ; _<?_)
open import Data.Product as Prod using (∃; ∃-syntax; _×_; _,_)
open import Data.String as String using (String)
open import Data.Unit as Unit using (⊤)
open import Function using (_$_; _∘_; id)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import SMT.Logics
open import Data.Environment as Env using (Env; _∷_; [])
import Reflection as Rfl
open import Text.Parser.String using (ParseErrorMsg; no-parse; ambiguous-parse)

open BaseTheory baseTheory


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
Γ ∋ σ = ∃[ i ] (List.lookup Γ i ≡ σ)

-- |SMT-LIB terms.
--
--  NOTE: match expressions are omitted, since we have no plans at the moment
--        to support datatype sorts.
mutual
  data Term (Γ : Ctxt) : (σ : Sort) → Set where
    var    : ∀ {σ} (x : Γ ∋ σ) → Term Γ σ
    lit    : ∀ {σ} (l : Literal σ) → Term Γ σ
    app    : ∀ {σ} {Σ : Signature σ} (x : Identifier Σ) (xs : Args Γ (ArgTypes Σ)) → Term Γ σ
    forAll : ∀ (σ : Sort) (x : Term (σ ∷ Γ) BOOL) → Term Γ BOOL
    exists : ∀ (σ : Sort) (x : Term (σ ∷ Γ) BOOL) → Term Γ BOOL

  Args : (Γ Δ : Ctxt) → Set
  Args Γ = Env (λ σ _Δ → Term Γ σ)

pattern app₁ f x     = app f (x ∷ [])
pattern app₂ f x y   = app f (x ∷ y ∷ [])
pattern app₃ f x y z = app f (x ∷ y ∷ z ∷ [])

-- |Helper function for writing variables.
#_ : {Γ : Ctxt} {σ : Sort} (n : ℕ)
     {n<∣Γ∣ : True (n <? List.length Γ)}
     {Γ∋σ : True (List.lookup Γ (Fin.fromℕ< (toWitness n<∣Γ∣)) ≟-Sort σ)} → Term Γ σ
#_ {Γ} {σ} n {n<∣Γ∣} {Γ∋σ} = var (Fin.fromℕ< (toWitness n<∣Γ∣) , toWitness Γ∋σ)

Rename : (Γ Δ : Ctxt) → Set
Rename Γ Δ = ∀ {σ} → Γ ∋ σ → Δ ∋ σ

extendVar : Γ ∋ σ → (σ′ ∷ Γ) ∋ σ
extendVar (i , p) = suc i , p

extendRename : Rename Γ Γ′ → Rename (σ ∷ Γ) (σ ∷ Γ′)
extendRename r (zero  , p) = zero , p
extendRename r (suc i , p) = extendVar (r (i , p))

mutual
  renameTerm : Rename Γ Γ′ → Term Γ σ → Term Γ′ σ
  renameTerm r (var i)      = var (r i)
  renameTerm r (lit l)      = lit l
  renameTerm r (app x xs)   = app x (renameArgs r xs)
  renameTerm r (forAll σ x) = forAll σ (renameTerm (extendRename r) x)
  renameTerm r (exists σ x) = exists σ (renameTerm (extendRename r) x)

  renameArgs : Rename Γ Γ′ → Args Γ Δ → Args Γ′ Δ
  renameArgs r [] = []
  renameArgs r (x ∷ xs) = renameTerm r x ∷ renameArgs r xs

injectVar : (Γ : Ctxt) → Γ ∋ σ → (Γ ++ Γ′) ∋ σ
injectVar (σ′ ∷ Γ) (zero  , p) = zero , p
injectVar (σ′ ∷ Γ) (suc i , p) = extendVar (injectVar Γ (i , p))

raiseVar : (Γ′ : Ctxt) → Γ ∋ σ → (Γ′ ++ Γ) ∋ σ
raiseVar []       x = x
raiseVar (σ ∷ Γ′) x = extendVar (raiseVar Γ′ x)

swapVar : (Γ : Ctxt) → (Γ ++ τ ∷ τ′ ∷ Γ′) ∋ σ → (Γ ++ τ′ ∷ τ ∷ Γ′) ∋ σ
swapVar [] (zero        , p) = (suc zero    , p)
swapVar [] (suc zero    , p) = (zero        , p)
swapVar [] (suc (suc i) , p) = (suc (suc i) , p)
swapVar (σ′ ∷ Γ) (zero  , p) = (zero        , p)
swapVar (σ′ ∷ Γ) (suc i , p) = extendVar (swapVar Γ (i , p))

moveVar : (Γ Γ′ {Γ″} : Ctxt) → (Γ ++ τ ∷ Γ′ ++ Γ″) ∋ σ → (Γ ++ Γ′ ++ τ ∷ Γ″) ∋ σ
moveVar {τ} {σ} Γ []        {Γ″} x = x
moveVar {τ} {σ} Γ (σ′ ∷ Γ′) {Γ″} x = x″
  where
    x′ : ((Γ ++ σ′ ∷ []) ++ τ ∷ Γ′ ++ Γ″) ∋ σ
    x′ rewrite List.++-assoc Γ (σ′ ∷ []) (τ ∷ Γ′ ++ Γ″) = swapVar Γ x
    x″ : (Γ ++ σ′ ∷ Γ′ ++ τ ∷ Γ″) ∋ σ
    x″ rewrite Eq.sym (List.++-assoc Γ (σ′ ∷ []) (Γ′ ++ τ ∷ Γ″)) = moveVar (Γ ++ σ′ ∷ []) Γ′ x′

reverseVar : (Γ {Γ′} : Ctxt) → (Γ ++ Γ′) ∋ σ → (Γ ʳ++ Γ′) ∋ σ
reverseVar [] x = x
reverseVar {σ} (σ′ ∷ Γ) {Γ′} x rewrite List.ʳ++-++ (σ′ ∷ []) {Γ} {Γ′} = reverseVar Γ (moveVar [] Γ x)

inject : (Γ : Ctxt) → Term Γ σ → Term (Γ ++ Γ′) σ
inject Γ = renameTerm (injectVar Γ)

raise : (Γ′ : Ctxt) → Term Γ σ → Term (Γ′ ++ Γ) σ
raise Γ′ = renameTerm (raiseVar Γ′)

reverse : (Γ : Ctxt) → Term (Γ ++ Γ′) σ → Term (Γ ʳ++ Γ′) σ
reverse Γ = renameTerm (reverseVar Γ)

--------------------------
-- SMT-LIB Outputs --
--------------------------

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

_≟-Sat_ : (s₁ s₂ : Sat) → Dec (s₁ ≡ s₂)
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

_if-sat_ : (A : Set) → Sat → Set
A if-sat sat = A
A if-sat _   = ⊤

QualifiedModel : (Γ : Ctxt) → Set
QualifiedModel Γ = ∃[ s ] (Model Γ if-sat s)


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
quoteModel : (Γ : Ctxt) → Model Γ → Rfl.Term
quoteModel [] [] =
  Rfl.con (quote Model.[]) []
quoteModel (σ ∷ Γ) (v ∷ vs) =
  Rfl.con (quote Model._∷_)
    $ Rfl.hArg Rfl.unknown
    ∷ Rfl.hArg (quoteSort σ)
    ∷ Rfl.vArg (quoteValue σ v)
    ∷ Rfl.vArg (quoteModel Γ vs) ∷ []

-- |Quote a qualified model.
quoteQualifiedModel : (Γ : Ctxt) → QualifiedModel Γ → Rfl.Term
quoteQualifiedModel Γ (s@sat , m) =
  Rfl.con (quote Prod._,_)
    $ Rfl.vArg (quoteSat s)
    ∷ Rfl.vArg (quoteModel Γ m)
    ∷ []
quoteQualifiedModel Γ (s@unsat , m) =
  Rfl.con (quote Prod._,_)
    $ Rfl.vArg (quoteSat s)
    ∷ Rfl.vArg (Rfl.con (quote Unit.tt) [])
    ∷ []
quoteQualifiedModel Γ (s@unknown , m) =
  Rfl.con (quote Prod._,_)
    $ Rfl.vArg (quoteSat s)
    ∷ Rfl.vArg (Rfl.con (quote Unit.tt) [])
    ∷ []

-- |Quote a result.
quoteOutput : Output ξ → Rfl.Term
quoteOutput {SAT}     = quoteSat
quoteOutput {MODEL Γ} = quoteQualifiedModel Γ

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
  set-logic     : (l : Logic) → Command Γ [] []
  declare-const : (x : String) (σ : Sort) → Command Γ (σ ∷ []) []
  assert        : Term Γ BOOL → Command Γ [] []
  check-sat     : Command Γ [] (SAT ∷ [])
  get-model     : Command Γ [] (MODEL Γ ∷ [])


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

declare-consts : (δΓ : Ctxt) → Script (δΓ ʳ++ Γ) Γ′ Ξ → Script Γ Γ′ Ξ
declare-consts {Γ} [] scr = scr
declare-consts {Γ} (σ ∷ δΓ) scr
  rewrite List.ʳ++-++ (σ ∷ []) {δΓ} {Γ} = declare-const "_" σ ∷ declare-consts δΓ scr

VarNames : Ctxt → Set
VarNames = All (λ _ → String)

private
  scriptVarNames′ : Script Γ′ Γ Ξ → VarNames Γ′ → VarNames Γ
  scriptVarNames′ [] acc = acc
  scriptVarNames′ (set-logic l       ∷ s) acc = scriptVarNames′ s acc
  scriptVarNames′ (declare-const x σ ∷ s) acc = scriptVarNames′ s (x ∷ acc)
  scriptVarNames′ (assert x          ∷ s) acc = scriptVarNames′ s acc
  scriptVarNames′ (check-sat         ∷ s) acc = scriptVarNames′ s acc
  scriptVarNames′ (get-model         ∷ s) acc = scriptVarNames′ s acc

scriptVarNames : Script [] Γ Ξ → VarNames Γ
scriptVarNames s = scriptVarNames′ s []

----------------------
-- Parser utilities --
----------------------

-- |Format a parser error to the user.
parseErrorMsg : (input : String) → ParseErrorMsg →  String
parseErrorMsg input no-parse        = "Failed to parse '" String.++ input String.++ "'"
parseErrorMsg input ambiguous-parse = "Ambiguous parse '" String.++ input String.++ "'"

-- |Display a parser error to the user.
parseError : ∀ {a} {A : Set a} (input : String) (errMsg : ParseErrorMsg) → Rfl.TC A
parseError input errMsg = Rfl.typeError (Rfl.strErr (parseErrorMsg input errMsg) ∷ [])
