open import SMT.Theory

module SMT.Script {s i l} (theory : Theory s i l) where

open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.List as List using (List; _∷_; []; _++_)
open import Data.Product using (∃-syntax; _,_)
open import Level using (Lift; lift; lower; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Theory theory

-- |Typing contexts.
Ctxt : Set s
Ctxt = List Sort

-- |Possible results.
data OutputType : Set s where
  SAT   : OutputType
  MODEL : Ctxt → OutputType

-- |Result contexts.
OutputCtxt : Set s
OutputCtxt = List OutputType

private
  variable
    σ σ′    : Sort
    ξ ξ′    : OutputType
    Γ Γ′ Γ″ : Ctxt
    Δ Δ′    : Ctxt
    Ξ Ξ′    : OutputCtxt
    Σ Σ′    : Signature Sort

-- |Well-typed variables.
_∋_ : (Γ : Ctxt) (σ : Sort) → Set s
Γ ∋ σ = ∃[ i ] (List.lookup Γ i ≡ σ)

-- |SMT-LIB terms.
--
--  NOTE: match expressions are omitted, since we have no plans at the moment
--        to support datatype sorts.
mutual
  data Term (Γ : Ctxt) : (σ : Sort) → Set (s ⊔ i ⊔ l) where
    var    : ∀ {σ} (x : Γ ∋ σ) → Term Γ σ
    lit    : ∀ {σ} (l : Literal σ) → Term Γ σ
    app    : ∀ {σ} {Σ : Signature σ} (x : Identifier Σ) (xs : Args Γ (ArgTypes Σ)) → Term Γ σ
    forAll : ∀ {σ} (x : Term (σ ∷ Γ) BOOL) → Term Γ BOOL
    exists : ∀ {σ} (x : Term (σ ∷ Γ) BOOL) → Term Γ BOOL

  data Args (Γ : Ctxt) : (Δ : Ctxt) → Set (s ⊔ i ⊔ l) where
    []  : Args Γ []
    _∷_ : Term Γ σ → Args Γ Δ → Args Γ (σ ∷ Δ)

pattern app₁ f x     = app f (x ∷ [])
pattern app₂ f x y   = app f (x ∷ y ∷ [])
pattern app₃ f x y z = app f (x ∷ y ∷ z ∷ [])

-- |SMT-LIB commands.
--
--  NOTE: It is most natural to think of scripts as a list of commands,
--        but unfortunatly, commands such as `declare-const` bind a new
--        variable. Therefore, Command has two type-level arguments, `Γ`
--        and `Γ′`, which represent the binding context before and after
--        executing the command. Similarly, scripts have outputs. Therefore,
--        Commands have two more type-level arguments, `Ξ` and `Ξ′`, which
--        represent the list of outputs given by the SMT solver in order.
--
data Command (Γ : Ctxt) : (Ξ : OutputCtxt) (Γ′ : Ctxt) (Ξ′ : OutputCtxt) → Set (s ⊔ i ⊔ l) where
  declare-const : (σ : Sort) → Command Γ Ξ (σ ∷ Γ) Ξ
  assert        : Term Γ BOOL → Command Γ Ξ Γ Ξ
  check-sat     : Command Γ Ξ Γ (SAT ∷ Ξ)
  get-model     : Command Γ (SAT ∷ Ξ) Γ (MODEL Γ ∷ SAT ∷ Ξ)

-- |SMT-LIB scripts.
data Script (Γ : Ctxt) : (Γ″ : Ctxt) (Ξ : OutputCtxt) → Set (s ⊔ i ⊔ l) where
  []  : Script Γ Γ []
  _∷_ : Command Γ Ξ Γ′ Ξ′ → Script Γ′ Γ″ Ξ → Script Γ Γ″ Ξ′

-- |SMT-LIB satisfiability.
data Sat : Set where
  sat unsat unknown : Sat

-- |SMT-LIB script result.
Result : OutputType → Set (s ⊔ i ⊔ l)
Result SAT       = Lift _ Sat
Result (MODEL Γ) = Args [] Γ

-- |List of SMT-LIB results.
data Results : (Ξ : OutputCtxt) → Set (s ⊔ i ⊔ l) where
  []  : Results []
  _∷_ : Result ξ → Results Ξ → Results (ξ ∷ Ξ)
