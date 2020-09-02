{-# OPTIONS --allow-exec #-}
module SMT.ReflectionTest where

open import Level hiding (suc)
open import Data.Bool hiding (_≤_; not)
open import Data.List
open import Data.List.Properties
open import Data.Maybe hiding (_>>=_)
open import Data.Maybe.Categorical
open import Data.Product hiding (_<*>_)
import Data.Nat as ℕ
open ℕ hiding (_≤_; _+_; _*_)
open import Data.Fin as Fin hiding (_≤_; _+_)
open import Data.Nat.Literals as NatLit
open import Data.Integer hiding (suc)
open import Data.Integer.Literals as IntLit
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Function renaming (_∋_ to _∋ᶠ_)
open import Data.Unit hiding (_≤_)
open import Relation.Nullary

import Reflection as R
open R hiding (Term; _>>=_; return; _>>_; _≟-Sort_)
open import Reflection.TypeChecking.Monad.Categorical as TC

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg

open import SMT.Theories.Core
open import SMT.Theories.Ints as Ints
open import SMT.Backend.Z3 Ints.theory

private
  variable
    ℓ : Level
    A B : Set ℓ

instance
  _ = NatLit.number
  _ = IntLit.number
  _ = IntLit.negative

data Preterm : Set where
  var         : (x : ℕ) → Preterm
  lit         : (x : ℕ) → Preterm
  eq leq lt   : (a b : Preterm) → Preterm
  add sub mul : (a b : Preterm) → Preterm
  neg not     : (a : Preterm) → Preterm
  -- more

data Predecl : Set where
  declare-const : Predecl
  assert        : Preterm → Predecl

Prescript : Set
Prescript = List Predecl

module MonadTC    {ℓ} = RawMonad {ℓ} TC.monad renaming (_⊛_ to _<*>_)
module MonadMaybe {ℓ} = RawMonad {ℓ} Data.Maybe.Categorical.monad renaming (_⊛_ to _<*>_)

module _ where

  open MonadTC

  pattern argᵛ a = arg (arg-info visible relevant) a

  pattern _`+_ a b = def (quote Data.Integer._+_) (arg _ a ∷ arg _ b ∷ [])
  pattern _`-_ a b = def (quote Data.Integer._-_) (arg _ a ∷ arg _ b ∷ [])
  pattern _`*_ a b = def (quote Data.Integer._*_) (arg _ a ∷ arg _ b ∷ [])
  pattern `fromNat a = def (quote Number.fromNat) (_ ∷ _ ∷ _ ∷ arg _ a ∷ _ ∷ [])
  pattern `fromNeg a = def (quote Negative.fromNeg) (_ ∷ _ ∷ _ ∷ arg _ a ∷ _ ∷ [])

  pattern _`≤_ a b = def (quote _≤_) (arg _ a ∷ arg _ b ∷ [])
  pattern _`≡_ a b = def (quote _≡_) (arg _ _ ∷ arg _ _ ∷ arg _ a ∷ arg _ b ∷ [])
  pattern _∶_`→_ x a b = pi (arg _ a) (abs x b)
  pattern `ℤ = def (quote ℤ) []

  decodeTerm : ℕ → R.Term → TC Preterm
  decodeTerm n (a `≤ b) = ⦇ leq (decodeTerm n a) (decodeTerm n b) ⦈
  decodeTerm n (a `≡ b) = ⦇ eq  (decodeTerm n a) (decodeTerm n b) ⦈
  decodeTerm n (a `+ b) = ⦇ add (decodeTerm n a) (decodeTerm n b) ⦈
  decodeTerm n (a `* b) = ⦇ mul (decodeTerm n a) (decodeTerm n b) ⦈
  decodeTerm n (a `- b) = ⦇ sub (decodeTerm n a) (decodeTerm n b) ⦈
  decodeTerm n (`fromNat (lit (nat a))) = pure (lit a)
  decodeTerm n (`fromNeg (lit (nat a))) = pure (neg (lit a))
  decodeTerm n (var x []) =
    case x ℕ.<? n of λ where
      (yes _) → typeErrorFmt "Variable index %u refers to an assertion and not a constant." x
      (no _)  → return (var (x ∸ n))
  decodeTerm n t = typeErrorFmt "The term %t cannot be interpreted as valid assertion" t

  decodeScript : ℕ → R.Term → TC Prescript
  decodeScript 0 (_ ∶ `ℤ `→ t) = extendContext (argᵛ `ℤ) $ declare-const ∷_ <$> decodeScript 0 t
  decodeScript n (_ ∶ h `→ t)  = extendContext (argᵛ h)  $ ⦇ ⦇ assert (decodeTerm n h) ⦈ ∷ decodeScript (suc n) t ⦈
  decodeScript n t         = [_] ∘ Predecl.assert ∘ not <$> decodeTerm n t

module _ where

  open MonadMaybe

  private
    variable
      Γ Γ′ δΓ : Ctxt
      Ξ Ξ₁ Ξ₂ : OutputCtxt

  cons : Command Γ δΓ [] → Script (δΓ ++ Γ) Γ′ Ξ → Script Γ Γ′ Ξ
  cons c s = subst (Script _ _) (++-identityʳ _) (c ∷ s)

  prescriptContext : Prescript → Ctxt
  prescriptContext []                   = []
  prescriptContext (declare-const ∷ ps) = INT ∷ prescriptContext ps
  prescriptContext (assert _      ∷ ps) = []

  private
    variable
      σ τ : Ints.Sort

  vSuc : Γ ∋ τ → (σ ∷ Γ) ∋ τ
  vSuc (i , refl) = suc i , refl

  checkVar : (Γ : Ctxt) (τ : Ints.Sort) (x : ℕ) → Maybe (Γ ∋ τ)
  checkVar [] _ _ = nothing
  checkVar (σ ∷ Γ) τ zero    =
    case σ ≟-Sort τ of λ where
      (yes p) → just (Fin.zero , p)
      (no _)  → nothing
  checkVar (σ ∷ Γ) τ (suc x) = ⦇ vSuc (checkVar Γ τ x) ⦈

  checkTerm : (Γ : Ctxt) (τ : Ints.Sort) → Preterm → Maybe (Term Γ τ)
  checkTerm Γ τ (var x) = ⦇ var (checkVar Γ τ x) ⦈
  checkTerm Γ (CORE BOOL) (eq  a b) = ⦇ (app₂ eq)  (checkTerm Γ INT a) (checkTerm Γ INT b) ⦈
  checkTerm Γ (CORE BOOL) (leq a b) = ⦇ (app₂ leq) (checkTerm Γ INT a) (checkTerm Γ INT b) ⦈
  checkTerm Γ (CORE BOOL) (lt  a b) = ⦇ (app₂ lt)  (checkTerm Γ INT a) (checkTerm Γ INT b) ⦈
  checkTerm Γ (CORE BOOL) (not a)   = ⦇ (app₁ (core not)) (checkTerm Γ (CORE BOOL) a) ⦈
  checkTerm Γ INT (add a b) = ⦇ (app₂ add) (checkTerm Γ INT a) (checkTerm Γ INT b) ⦈
  checkTerm Γ INT (sub a b) = ⦇ (app₂ sub) (checkTerm Γ INT a) (checkTerm Γ INT b) ⦈
  checkTerm Γ INT (mul a b) = ⦇ (app₂ mul) (checkTerm Γ INT a) (checkTerm Γ INT b) ⦈
  checkTerm Γ INT (neg a)   = ⦇ (app₁ neg) (checkTerm Γ INT a) ⦈
  checkTerm Γ INT (lit n) = pure (lit (int n))
  checkTerm _ _ _ = nothing

  checkScript′ : (Γ : Ctxt) → Prescript → Maybe (Script Γ Γ (SAT ∷ []))
  checkScript′ Γ []                   = just (check-sat ∷ [])
  checkScript′ Γ (declare-const ∷ ps) = checkScript′ Γ ps
  checkScript′ Γ (assert t ∷ ps)      = ⦇ ⦇ assert (checkTerm Γ (CORE BOOL) t) ⦈ ∷ checkScript′ Γ ps ⦈

  declare : (Γ : Ctxt) → Script Γ Γ′ Ξ → Script [] Γ′ Ξ
  declare []      s = s
  declare (τ ∷ Γ) s = declare Γ (cons (declare-const τ) s)

  checkScript : (ps : Prescript) → Maybe (Script [] (prescriptContext ps) (SAT ∷ []))
  checkScript ps = declare (prescriptContext ps) <$> checkScript′ (prescriptContext ps) ps

postulate
  because-z3 : A

macro
  by-z3 : R.Term → TC ⊤
  by-z3 hole = do
    goal ← inferType hole
    ps ← decodeScript 0 goal
    just s ← pure (checkScript ps)
      where nothing → do
              `ps ← withNormalisation true $ quoteTC ps
              typeErrorFmt "Not type correct: %t" `ps
    unsat ∷ [] ← TC (Outputs (SAT ∷ [])) ∋ᶠ unquoteTC =<< z3TC s -- quote/unquote here is silly
      where _ → typeErrorFmt "Z3 says no!"  -- if no, run again to get counterexample
    unify hole (def (quote because-z3) [])  -- (or get both the first time)!
    where open MonadTC

test : (a b c : ℤ) → a * a ≤ b → a ≤ b
test = by-z3 -- because-z3
