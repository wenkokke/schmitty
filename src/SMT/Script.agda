open import Data.List using (List)

module SMT.Script
  {s i l}
  (Sort : Set s)
  (Bool : Sort)
  (Literal : Sort → Set l)
  (Identifier : List Sort → Sort → Set i)
  where

open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.List as List using (_∷_; []; _++_)
open import Data.Product using (∃-syntax; _,_)
open import Level using (Lift; lift; lower; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- |Typing contexts.
Ctxt : Set s
Ctxt = List Sort

-- |Possible results.
data ResultSort : Set s where
  SAT   : ResultSort
  MODEL : Ctxt → ResultSort

-- |Result contexts.
ResultCtxt : Set s
ResultCtxt = List ResultSort

private
  variable
    σ σ′    : Sort
    ξ ξ′    : ResultSort
    Γ Γ′ Γ″ : Ctxt
    Ξ Ξ′    : ResultCtxt
    Σ Σ′    : Ctxt

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
    app    : ∀ {σ} {Σ : List Sort} (x : Identifier Σ σ) (xs : Args Γ Σ) → Term Γ σ
    forAll : ∀ {σ} (x : Term (σ ∷ Γ) Bool) → Term Γ Bool
    exists : ∀ {σ} (x : Term (σ ∷ Γ) Bool) → Term Γ Bool

  data Args (Γ : Ctxt) : (Σ : Ctxt) → Set (s ⊔ i ⊔ l) where
    []  : Args Γ []
    _∷_ : Term Γ σ → Args Γ Σ → Args Γ (σ ∷ Σ)

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
data Command (Γ : Ctxt) : (Ξ : ResultCtxt) (Γ′ : Ctxt) (Ξ′ : ResultCtxt) → Set (s ⊔ i ⊔ l) where
  declare-const : (σ : Sort) → Command Γ Ξ (σ ∷ Γ) Ξ
  assert        : Term Γ Bool → Command Γ Ξ Γ Ξ
  check-sat     : Command Γ Ξ Γ (SAT ∷ Ξ)
  get-model     : Command Γ (SAT ∷ Ξ) Γ (MODEL Γ ∷ SAT ∷ Ξ)

-- |SMT-LIB scripts.
data Script (Γ : Ctxt) : (Γ″ : Ctxt) (Ξ : ResultCtxt) → Set (s ⊔ i ⊔ l) where
  []  : Script Γ Γ []
  _∷_ : Command Γ Ξ Γ′ Ξ′ → Script Γ′ Γ″ Ξ → Script Γ Γ″ Ξ′

-- |SMT-LIB satisfiability.
data Sat : Set where
  sat unsat unknown : Sat

-- |SMT-LIB script result.
Result : ResultSort → Set (s ⊔ i ⊔ l)
Result SAT       = Lift _ Sat
Result (MODEL Γ) = Args [] Γ

-- |List of SMT-LIB results.
data Results : (Ξ : ResultCtxt) → Set (s ⊔ i ⊔ l) where
  []  : Results []
  _∷_ : Result ξ → Results Ξ → Results (ξ ∷ Ξ)
