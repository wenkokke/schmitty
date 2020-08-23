open import SMT.Theory

module SMT.Script.Base (baseTheory : BaseTheory) where

open import Data.Fin as Fin using (Fin)
open import Data.List as List using (List; _∷_; []; _++_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Nat as Nat using (ℕ; _<?_)
open import Data.Product as Prod using (∃; ∃-syntax; _×_; _,_)
open import Function using (_$_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Logics
open import Data.Environment as Env using (Env; _∷_; [])
import Reflection as Agda

open BaseTheory baseTheory


-------------------
-- SMT-LIB Terms --
-------------------

-- |Typing contexts.
Ctxt : Set
Ctxt = List Sort

private
  variable
    σ σ′    : Sort
    Γ Γ′ δΓ : Ctxt
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
extendVar (i , p) = Fin.suc i , p

extendRename : Rename Γ Γ′ → Rename (σ ∷ Γ) (σ ∷ Γ′)
extendRename r (Fin.zero  , p) = Fin.zero , p
extendRename r (Fin.suc i , p) = extendVar (r (i , p))

mutual
  rename : Rename Γ Γ′ → Term Γ σ → Term Γ′ σ
  rename r (var i)      = var (r i)
  rename r (lit l)      = lit l
  rename r (app x xs)   = app x (renameArgs r xs)
  rename r (forAll σ x) = forAll σ (rename (extendRename r) x)
  rename r (exists σ x) = exists σ (rename (extendRename r) x)

  renameArgs : Rename Γ Γ′ → Args Γ Δ → Args Γ′ Δ
  renameArgs r [] = []
  renameArgs r (x ∷ xs) = rename r x ∷ renameArgs r xs

injectVar : (Γ′ : Ctxt) → Γ ∋ σ → (Γ List.++ Γ′) ∋ σ
injectVar {σ′ ∷ Γ} Γ′ (Fin.zero  , p) = Fin.zero , p
injectVar {σ′ ∷ Γ} Γ′ (Fin.suc i , p) = extendVar (injectVar {Γ} Γ′ (i , p))

weaken : Term Γ σ → Term (σ′ ∷ Γ) σ
weaken = rename extendVar

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
-- datatype of its own to help Agda's reflection mechanism fill in the
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


-- |SMT-LIB script result.
Output : OutputType → Set
Output SAT       = Sat
Output (MODEL Γ) = Model Γ

-- |List of SMT-LIB results.
--
-- The Outputs type *could* be defined as below, but it is defined as a
-- datatype of its own to help Agda's reflection mechanism fill in the
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
quoteSat : Sat → Agda.Term
quoteSat sat     = Agda.con (quote sat) []
quoteSat unsat   = Agda.con (quote unsat) []
quoteSat unknown = Agda.con (quote unknown) []

-- |Quote a model.
quoteModel : (Γ : Ctxt) → Model Γ → Agda.Term
quoteModel [] [] =
  Agda.con (quote Model.[]) []
quoteModel (σ ∷ Γ) (v ∷ vs) =
  Agda.con (quote Model._∷_)
    $ Agda.hArg Agda.unknown
    ∷ Agda.hArg (quoteSort σ)
    ∷ Agda.vArg (quoteValue σ v)
    ∷ Agda.vArg (quoteModel Γ vs) ∷ []

-- |Quote a result.
quoteOutput : Output ξ → Agda.Term
quoteOutput {SAT}     = quoteSat
quoteOutput {MODEL Γ} = quoteModel Γ

-- |Quote a list of results.
quoteOutputs : Outputs Ξ → Agda.Term
quoteOutputs [] =
  Agda.con (quote Outputs.[]) $ []
quoteOutputs (r ∷ rs) =
  Agda.con (quote Outputs._∷_)
    $ Agda.vArg (quoteOutput r)
    ∷ Agda.vArg (quoteOutputs rs) ∷ []

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
  declare-const : (σ : Sort) → Command Γ (σ ∷ []) []
  assert        : Term Γ BOOL → Command Γ [] []
  check-sat     : Command Γ [] (SAT ∷ [])
  get-model     : Command Γ [] (MODEL Γ ∷ [])


---------------------
-- SMT-LIB Scripts --
---------------------

-- |SMT-LIB scripts.
data Script (Γ : Ctxt) : (Γ′ : Ctxt) (Ξ : OutputCtxt) → Set where
  []  : Script Γ Γ []
  _∷_ : Command Γ δΓ δΞ → Script (δΓ ++ Γ) Γ′ Ξ → Script Γ Γ′ (Ξ ++ δΞ)


--------------------
-- Useful aliases --
--------------------

Var : Ctxt → Set
Var Γ = ∃[ σ ] (Γ ∋ σ)

Val : Set
Val = ∃[ σ ] (Value σ)

Defn : Ctxt → Set
Defn Γ = ∃[ σ ] (Γ ∋ σ × Value σ)
