{-# OPTIONS --guardedness #-}

--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Defines `reflectToScript`, which uses an instance of the `Reflectable` class
-- to convert reflected Agda syntax to an SMT-LIB script.
--------------------------------------------------------------------------------

open import SMT.Theory

module SMT.Script.Reflection (theory : Theory) {{reflectable : Reflectable theory}} where

open Theory theory
open Reflectable reflectable

open import Level using (0ℓ)
open import Category.Monad
open import Data.Bool.Base using (Bool; true; false)
open import Data.Environment as Env using (Env; _∷_; [])
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.List as List using (List; _∷_; []; length)
open import Data.List.Relation.Unary.All using (All; _∷_; []; all?)
open import Data.List.Relation.Unary.Any as Any using (here; there)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Sum.Base as Sum using (_⊎_) renaming (inj₁ to left; inj₂ to right)
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Product as Prod using (∃; ∃-syntax; -,_; _×_; _,_; proj₁; proj₂)
open import Data.String as String using (String; _++_)
open import Data.Unit as Unit using (⊤)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Function using (Morphism; _$_; case_of_; _∘_; const; flip; id)
import Level
import Reflection as Rfl
open import Reflection.DeBruijn using (η-expand)
import Reflection.TypeChecking.Monad.Syntax as TC
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (True)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import SMT.Script.Base theory

private
  variable
    A B     : Set
    σ σ′    : Sort
    Γ Γ′ δΓ : Ctxt
    Δ Δ′    : Ctxt
    Σ       : Signature σ
    Σ′      : Signature σ′
    ξ ξ′    : OutputType
    Ξ Ξ′ δΞ : OutputCtxt

-- * Reflection hooks

data Error : Set where
  sort-mismatch : (σ σ′ : Sort) → σ ≢ σ′ → Error
  unbound-variable : Error
  higher-order-variable : Error
  disallowed-variable : String → Error
  undefined-core : String → String → Error
  invalid-syntax : String → Error
  bad-literal : Rfl.Literal → Error
  bad-identifier : Rfl.Name → Error
  arity-mismatch : Rfl.Name → Error
  out-of-fuel : Error
  should-not-happen : String → Error

module _ where
  showError : Error → String
  showError (sort-mismatch σ σ′ _) = "Sort mismatch"
  -- TODO: add Printable instance as a module parameter
  showError unbound-variable = "Unbound variable"
  showError higher-order-variable = "Higher-order variable"
  showError (disallowed-variable name)
    = "disallowed variable " ++ name ++ ": dependently typed formulas are not expressible in SMT-LIB"
  showError (undefined-core name msg) = "Undefined core symbol " ++ name ++ ": " ++ msg
  showError (invalid-syntax desc) = "invalid syntax: " ++ desc
  showError (bad-literal l) = "Bad literal " ++ Rfl.showLiteral l
  showError (bad-identifier n) = "Unrecognized identifier " ++ Rfl.showName n
  showError (arity-mismatch f) = "Arity mismatch in arguments of " ++ Rfl.showName f
  showError out-of-fuel = "Out of fuel"
  showError (should-not-happen msg) = "The impossible happened! " ++ msg

getImplies : ∀ {Γ} → Error ⊎ (Term Γ BOOL → Term Γ BOOL → Term Γ BOOL)
getImplies with checkIdentifier BOOL (quote Morphism)
... | nothing = left (undefined-core "IMPLIES" "missing Morphism binding")
... | just (Σ , implies) with all? (BOOL ≟-Sort_) (ArgSorts Σ)
... | yes (refl ∷ refl ∷ []) = right (λ x y → implies (x ∷ y ∷ []))
... | _ = left (undefined-core "IMPLIES" "sort should be BOOL × BOOL → BOOL")

getAnd : ∀ {Γ} → Error ⊎ (Term Γ BOOL → Term Γ BOOL → Term Γ BOOL)
getAnd with checkIdentifier BOOL (quote _×_)
... | nothing = left (undefined-core "IMPLIES" "missing _×_ binding")
... | just (Σ , implies) with all? (BOOL ≟-Sort_) (ArgSorts Σ)
... | yes (refl ∷ refl ∷ []) = right (λ x y → implies (x ∷ y ∷ []))
... | _ = left (undefined-core "IMPLIES" "sort should be BOOL × BOOL → BOOL")

getNegation : ∀ {Γ} → Error ⊎ (Term Γ BOOL → Term Γ BOOL)
getNegation with checkIdentifier BOOL (quote ¬_)
... | nothing = left (undefined-core "NOT" "missing ¬_ binding")
... | just (Σ , neg) with all? (BOOL ≟-Sort_) (ArgSorts Σ)
... | yes (refl ∷ []) = right (λ x → neg (x ∷ []))
... | _ = left (undefined-core "NOT" "sort should be BOOL → BOOL")

module ETC where
  record M (A : Set) : Set where
    constructor mkM
    field
      run : Rfl.TC (Error ⊎ A)

  open M public

  throw : Error → M A
  throw = mkM ∘ TC.pure ∘ left

  monad : RawMonad M
  monad = record
    { return = mkM ∘ pure ∘ right
    ; _>>=_ = λ m k → mkM (run m >>= Sum.[ pure ∘ left , run ∘ k ])
    } where open TC

  open RawMonad monad

  lift : Rfl.TC A → M A
  lift m = mkM (right TC.<$> m)

  hoist : Error ⊎ A → M A
  hoist = Sum.[ throw , pure ]

  extendContext : Rfl.Arg Rfl.Type → M A → M A
  extendContext a (mkM m) = mkM (Rfl.extendContext a m)


  -- Assert that two sorts are equal
  _≡!-Sort_ : (σ σ′ : Sort) → M (σ ≡ σ′)
  σ ≡!-Sort σ′ with σ ≟-Sort σ′
  ... | yes σ≡σ′ = pure σ≡σ′
  ... | no  σ≢σ′ = throw (sort-mismatch σ σ′ σ≢σ′)

  _<?>_ : Maybe A → Error → M A
  nothing <?> e = throw e
  just x <?> e = pure x

open ETC

-- Non-dependent functions are translated to implication, but they still bring
-- a variable into scope in the reflected syntax. Those variables are
-- "disallowed" from being used in a term.
--
-- Function arguments that could not be encoded to SMT sorts or terms are
-- also disallowed, and we remember the error from the encoding attempt.
-- The user should know what failed, if a counterexample turns out to violate
-- an ignored assumption that they thought should be taken into account.
AllowedVar : Set
AllowedVar = Maybe (String × Maybe (Rfl.Term × Error))

AllowedVars : Set
AllowedVars = List AllowedVar

-- 'nothing' indicates an allowed variable
-- 'just' indicates a disallowed variable, with extra info for error reporting:
-- - variable name
-- - if the variable is disallowed because we couldn't encode its type,
--   we also remember its type (pretty-printed) and the error.
pattern allowed = nothing
pattern disallowed name = just (name , nothing)
pattern disallowed-because name t e = just (name , just (t , e))

private module _ where
  open import Agda.Builtin.FromNat
  open import Agda.Builtin.FromNeg
  open Rfl

  pattern `fromNat = quote Number.fromNat
  pattern `fromNeg = quote Negative.fromNeg

  pattern `Σ  a b = def (quote Prod.Σ)        (_ ∷ _ ∷ a ∷ vArg b ∷ [])
  pattern `Σˢ a b = def (quote Prod.Σ-syntax) (_ ∷ _ ∷ a ∷ vArg b ∷ [])
  pattern `∃  a b = def (quote Prod.∃)        (_ ∷ _ ∷ a ∷ vArg b ∷ [])
  pattern `∃ˢ a b = def (quote Prod.∃-syntax) (_ ∷ _ ∷ a ∷ vArg b ∷ [])

-- TODO: sort inference? (right now all functions must be given the sort of the output term.)
module _ where
  open RawMonad ETC.monad renaming (_⊛_ to _<*>_)
  open Rfl.Term
  open Rfl.Arg
  open Rfl.Abs

  toVar : (σ : Sort) → (Γ : Ctxt) → AllowedVars → ℕ → M (Γ ∋ σ)
  toVar σ Γ (just (name , _) ∷ fv) zero = throw (disallowed-variable name)
  toVar σ Γ (just _ ∷ fv) (suc n) = toVar σ Γ fv n
  toVar σ (σ′ ∷ Γ) (nothing ∷ fv) zero = here <$> (σ ≡!-Sort σ′)
  toVar σ (σ′ ∷ Γ) (nothing ∷ fv) (suc n) = there <$> toVar σ Γ fv n
  toVar σ Γ fv n = throw unbound-variable  -- If the terms come from Agda this shouldn't happen

  mutual

    -- |To avoid having to deal with overloaded literals in the different theories (the dictionaries
    --  are hard to deal with), we normalise any calls to fromNat and fromNeg.  To convince the
    --  termination checker that this is fine there's a fuel parameter limiting how many nested
    --  normalisations we are allowed to do. Overloading will not create any nested calls to fromNat
    --  or fromNeg so it's enough to provide 1 fuel for this.
    --  However we also use the fuel when eta-expanding the predicate in existentials, and since these
    --  can be arbitrarily nested we need a reasonable amount of fuel.
    toTerm′ toTerm-decr :
      (fuel : ℕ) (Γ : Ctxt) (fv : AllowedVars) (σ : Sort) → Rfl.Term → M (Term Γ σ)
    toTerm′ fuel Γ fv σ (var x []) = `var <$> toVar σ Γ fv x
    toTerm′ fuel Γ fv σ (var x (_ ∷ _)) = throw higher-order-variable
    toTerm′ fuel Γ fv σ (lit l) = `lit <$> checkLiteral σ l <?> bad-literal l
    toTerm′ fuel Γ fv σ t@(def `fromNat _) = toTerm-decr fuel Γ fv σ =<< lift (Rfl.normalise t)
    toTerm′ fuel Γ fv σ t@(def `fromNeg _) = toTerm-decr fuel Γ fv σ =<< lift (Rfl.normalise t)
    toTerm′ fuel Γ fv σ (`Σ  a b) = toExist fuel Γ fv σ a b
    toTerm′ fuel Γ fv σ (`Σˢ a b) = toExist fuel Γ fv σ a b
    toTerm′ fuel Γ fv σ (`∃  a b) = toExist fuel Γ fv σ a b
    toTerm′ fuel Γ fv σ (`∃ˢ a b) = toExist fuel Γ fv σ a b
    toTerm′ fuel Γ fv σ (def f args) = toApp fuel Γ fv σ f args
    toTerm′ fuel Γ fv σ (con f args) = toApp fuel Γ fv σ f args
    toTerm′ fuel Γ fv σ (pi a b) = toQuantifier `forall getImplies fuel Γ fv σ a b
    toTerm′ fuel Γ fv σ (meta x _) = lift (Rfl.blockOnMeta x)
    toTerm′ fuel Γ fv σ (lam v t) = throw (invalid-syntax "lam")
    toTerm′ fuel Γ fv σ (pat-lam cs args) = throw (invalid-syntax "pat-lam")
    toTerm′ fuel Γ fv σ (agda-sort s) = throw (invalid-syntax "agda-sort")
    toTerm′ fuel Γ fv σ unknown = throw (invalid-syntax "unknown")

    toTerm-decr (suc fuel) = toTerm′ fuel
    toTerm-decr zero Γ fv σ t = throw out-of-fuel

    toApp : (fuel : ℕ) (Γ : Ctxt) (fv : AllowedVars) (σ : Sort)
      → Rfl.Name → List (Rfl.Arg Rfl.Term) → M (Term Γ σ)
    toApp fuel Γ fv σ fname args = do
      Σ , f ← checkIdentifier σ fname <?> bad-identifier fname
      args ← toArgs fname fuel Γ fv (ArgSorts Σ) args
      pure (f args)

    -- Heuristic: translate all visible relevant arguments, and ignore the rest.
    -- TODO a better way would be for the `theory` to tell us how to map the
    -- arguments of an Agda symbol to those of its SMT counterpart.
    --
    -- The name `fname` is used for error messages.
    toArgs : (fname : Rfl.Name) (fuel : ℕ) (Γ : Ctxt) (fv : AllowedVars)
      → (sorts : List Sort) → List (Rfl.Arg Rfl.Term) → M (Args Γ sorts)
    toArgs fname fuel Γ fv [] [] = pure []
    toArgs fname fuel Γ fv (_ ∷ _) [] = throw (arity-mismatch fname)
    toArgs fname fuel Γ fv [] (Rfl.vArg t ∷ args) = throw (arity-mismatch fname)
    toArgs fname fuel Γ fv (σ ∷ sorts) (Rfl.vArg t ∷ args) =
      ⦇ toTerm′ fuel Γ fv σ t ∷ toArgs fname fuel Γ fv sorts args ⦈
    toArgs fname fuel Γ fv sorts (_ ∷ args) = toArgs fname fuel Γ fv sorts args

    -- Depending on whether `A` turns out to be a sort or a term,
    -- - encode `∀ (x : A) → B` with either `forall or _`⇒_ (given by getImplies), or
    -- - encode `Σ[ x ∈ A ] → B` with either `exists or _`∧_ (given by getAnd)
    --
    -- `quant : `forall or `exists
    -- getConj : getImplies or getAnd
    toQuantifier :
      (`quant : {Γ : Ctxt} → String → (σ : Sort) → Term (σ ∷ Γ) BOOL → Term Γ BOOL) →
      (getConj : {Γ : Ctxt} → Error ⊎ (Term Γ BOOL → Term Γ BOOL → Term Γ BOOL)) →
      (fuel : ℕ) (Γ : Ctxt) (fv : AllowedVars) →
      (σ : Sort) → Rfl.Arg Rfl.Term → Rfl.Abs Rfl.Term → M (Term Γ σ)
    toQuantifier `quant getConj fuel Γ fv σ dom@(arg _ a) (abs x b) = do
      refl ← BOOL ≡!-Sort σ
      sot ← sortOrTerm′ fuel Γ fv a
      extendContext dom $
        case sot of λ where
          (left σ′) → `quant x σ′ <$> toTerm′ fuel (σ′ ∷ Γ) (allowed ∷ fv) σ b
          (right t) → do
            conj ← hoist getConj
            conj t <$> toTerm′ fuel Γ (disallowed x ∷ fv) σ b

    toExist : (fuel : ℕ) (Γ : Ctxt) (fv : AllowedVars) →
      (σ : Sort) → Rfl.Arg Rfl.Term → Rfl.Term → M (Term Γ σ)
    toExist zero Γ fv σ a b = throw out-of-fuel
    toExist (suc fuel) Γ fv σ a b = do
      lam _ b ← pure $ η-expand Rfl.visible b
        where _ → throw (should-not-happen "failed to η-expand existential predicate")
      toQuantifier `exists getAnd fuel Γ fv σ a b

    -- Try encoding an Agda term as a sort or a term.
    -- Could this be ambiguous, with a term encodable as both?
    -- Idk but if that happens, this implementation tries sorts first.
    sortOrTerm′ : (fuel : ℕ) (Γ : Ctxt) (fv : AllowedVars) → Rfl.Term → M (Sort ⊎ Term Γ BOOL)
    sortOrTerm′ fuel Γ fv t with checkSort t
    ... | just σ = pure (left σ)
    ... | nothing = right <$> toTerm′ fuel Γ fv BOOL t

  maxFuel : ℕ
  maxFuel = 1000

  toTerm : (Γ : Ctxt) (fv : AllowedVars) (σ : Sort) → Rfl.Term → Rfl.TC (Error ⊎ Term Γ σ)
  toTerm Γ fv σ t = run (toTerm′ maxFuel Γ fv σ t)

  sortOrTerm : (Γ : Ctxt) (fv : AllowedVars) → Rfl.Term → Rfl.TC (Error ⊎ (Sort ⊎ Term Γ BOOL))
  sortOrTerm Γ fv t = run (sortOrTerm′ maxFuel Γ fv t)

module _ where
  open TC
  open Rfl.Term
  open Rfl.Arg
  open Rfl.Abs
  open Rfl.ErrorPart

  _<$$>_ : ∀ {P Q : A → B → Set} → (∀ {x y} → P x y → Q x y) → Rfl.TC (∃ (∃ ∘ P)) → Rfl.TC (∃ (∃ ∘ Q))
  f <$$> m = Prod.map₂ (Prod.map₂ f) <$> m

  hoistTC : Error ⊎ A → Rfl.TC A
  hoistTC = Sum.[ Rfl.typeErrorFmt "%s" ∘ showError , pure ]

  show-ignored : AllowedVar → Maybe String
  show-ignored (disallowed-because x t e)
    = just $ x ++ " : " ++ Rfl.showTerm t ++ " --- " ++ showError e ++ "\n"
      -- TODO Rfl.showTerm's output is ugly but we have to wait for Agda 2.6.3 for a better alternative.
  show-ignored _ = nothing

  warn-if-ignored : AllowedVars → String
  warn-if-ignored fv with List.mapMaybe show-ignored fv
  ... | [] = ""
  ... | ignored@(_ ∷ _) = String.concat
    ("Some assumptions could not be encoded; they may invalidate counterexamples:\n" ∷ ignored)

  -- Convert a term to an SMT-LIB script.
  --
  -- In Agda, `pi` expresses both universal quantification and implication.
  -- Those are different constructs in SMT-LIB. To disambiguate whether
  -- `∀ (x : A) → B` should be encoded as a quantifier (`A` is a sort) or as an
  -- implication `A → B` (`A` is an term), we just try both (`sortOrTerm`)
  -- and pick whichever succeeds.
  --
  -- If we cannot encode `A` as either a sort or a term, we ignore it.
  -- Ignoring unencodable assumptions lets us call the solver deep in a
  -- term with a lot of junk in the context.
  -- This strengthens the proposition being proved, so there may be false
  -- negatives: counterexamples may violate the ignored assumptions.
  --
  -- Note that ignoring assumptions like that is only sound to do in `toScript`.
  -- In `toTerm′`, which uses similar logic to handle `pi` and also `∃`/`Σ`,
  -- we can only abort when `sortOrTerm` returns an error.
  --
  -- The `AllowedVars` parameter remembers, for each variable, whether its
  -- type was encoded as a sort, a term, or neither (so it is ignored).
  toScript : (Γ : Ctxt) (fv : AllowedVars) → Rfl.Term
    → Rfl.TC (∃[ Γ′ ] AllowedVars × Script Γ Γ′ [])
  toScript Γ fv (pi dom@(arg _ a) (abs x b)) = do
    sot ← sortOrTerm Γ fv a
    Rfl.extendContext dom $
      case sot of λ where
        (right (left σ)) → `declare-const x σ <$$> toScript (σ ∷ Γ) (allowed ∷ fv) b
        (right (right t)) → `assert t <$$> toScript Γ (disallowed x ∷ fv) b
        (left e) → toScript Γ (disallowed-because x a e ∷ fv) b
  toScript Γ fv t = toTerm Γ fv BOOL t >>= λ where
    (left e) → Rfl.typeErrorFmt "%s" (showError e)
    (right t) → do
      neg ← hoistTC getNegation
      pure (Γ , fv , `assert (neg t) [])

-- | Encode a reflected Agda type as an SMT-LIB script.
--
--  Functions are encoded as a series of assertions, with the result type
--  negated. For instance, the type `(x y : ℤ) → x - y ≤ x + y → x ≡ y`
--  is encoded as:
--
--  @
--    (declare-const ⋆ x)
--    (declare-const ⋆ y)
--    (assert (≤ (- x y) (+ x y)))
--    (assert (not (= x y)))
--  @
--
--  Which corresponds to `∃[ x ] ∃[ y ] (x - y ≤ x + y × x ≢ y)`, i.e.,
--  the negation of the Agda type. If the solver can find an inhabitant
--  for this type, then we have a counter-example for the original type.
--
--  Along with the script, return a list which records whether argument types
--  are interpreted as sorts (encoded using `declare-const`), as terms (encoded
--  using `assert`), or neither. This information is to be displayed in error
--  messages.
reflectToScript : Rfl.Term → Rfl.TC (∃[ Γ ] AllowedVars × Script [] Γ [])
reflectToScript t = toScript [] [] t
