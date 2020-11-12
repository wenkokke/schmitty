--------------------------------------------------------------------------------
-- Schmitty the Solver
--
-- Defines `reflectToRawScript`, which converts reflected Agda syntax to scripts
-- in the raw theory.
--------------------------------------------------------------------------------

module SMT.Theory.Raw.Reflection where

open import Category.Monad
open import Data.Bool as Bool using (Bool; true; false)
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.Integer as Int using (ℤ; +_; -[1+_])
open import Data.List as List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Nat as Nat using (ℕ; zero; suc; _∸_)
import Data.Nat.Literals as NatLits using (number)
open import Data.Product as Prod using (Σ; ∃; Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit as Unit using (⊤)
open import Function
open import Level using (Level)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)
open import Reflection as Rfl hiding (return; _>>=_)
import Reflection.TypeChecking.Monad.Categorical as TC
open import Reflection.DeBruijn using (η-expand; _∈FV_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (isYes)
open import SMT.Theory
open import SMT.Theory.Raw.Base

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg

instance _ = NatLits.number

private
  open module TCMonad {ℓ} = Category.Monad.RawMonad {ℓ} TC.monad renaming (_⊛_ to _<*>_)

private
  variable
    ℓ : Level
    A : Set ℓ


private
  -- We don't know the type of raw function symbols, so just look at
  -- the arguments. Design decision: only keep visible arguments.
  argTypes : List (Arg A) → Signature ⋆
  argTypes []              .ArgSorts = []
  argTypes (vArg _ ∷ args) .ArgSorts = ⋆ ∷ argTypes args .ArgSorts
  argTypes (_      ∷ args) .ArgSorts =     argTypes args .ArgSorts


reflectToRawVar : (Γ : RawCtxt) (n : ℕ) → TC (∃[ σ ] (Γ ∋ᵣ σ))
reflectToRawVar []      n       = typeErrorFmt "Variable out of bounds"
reflectToRawVar (x ∷ Γ) zero    = return (_ , here refl)
reflectToRawVar (x ∷ Γ) (suc n) = do
  σ , p ← reflectToRawVar Γ n
  return (σ , there p)

-- | Keep track of which variables are allowed to be used by a script and which are not.
--   Non-dependent functions are translated to implication, but they still bring a variable
--   into scope in the reflected syntax. This will be marked "not allowed" for the script.
AllowedVars = List Bool

-- | If Γ ⊢ x, then |Γ| ⊢ strengthenVar x, where |Γ| is the restriction of Γ to
--   only the allowed variables. Fails if x is not an allowed variable.
strengthenVar : (fv : AllowedVars) (n : ℕ) → TC ℕ
strengthenVar []            _       = typeErrorFmt "Free variable in goal"
strengthenVar (true  ∷ _)   0       = return 0
strengthenVar (false ∷ _)   0       = typeErrorFmt "Dependent quantification in term"
strengthenVar (false ∷ fvs) (suc n) = strengthenVar fvs n
strengthenVar (true  ∷ fvs) (suc n) = suc <$> strengthenVar fvs n

-- Placeholder name used as a function symbol of type TERM _ → ⋆ to wrap variables.
rawVar : ⊤
rawVar = _

private
  pattern `fromNat = quote Number.fromNat
  pattern `fromNeg = quote Negative.fromNeg

  pattern `Σ  a b = def (quote Σ)        (_ ∷ _ ∷ vArg a ∷ vArg b ∷ [])
  pattern `Σˢ a b = def (quote Σ-syntax) (_ ∷ _ ∷ vArg a ∷ vArg b ∷ [])
  pattern `∃  a b = def (quote ∃)        (_ ∷ _ ∷ hArg a ∷ vArg b ∷ [])
  pattern `∃ˢ a b = def (quote ∃-syntax) (_ ∷ _ ∷ hArg a ∷ vArg b ∷ [])

mutual
  -- |To avoid having to deal with overloaded literals in the different theories (the dictionaries
  --  are hard to deal with), we normalise any calls to fromNat and fromNeg.  To convince the
  --  termination checker that this is fine there's a fuel parameter limiting how many nested
  --  normalisations we are allowed to do. Overloading will not create any nested calls to fromNat
  --  or fromNeg so it's enough to provide 1 fuel for this.
  --  However we also use the fuel when eta-expanding the predicate in existentials, and since these
  --  can be arbitrarily nested we need a reasonable amount of fuel.
  reflectToRawTerm : (Γ : RawCtxt) (fv : AllowedVars) → Term → TC (RawTerm Γ ⋆)
  reflectToRawTerm = reflectToRawTerm′ 1000

  reflectToRawTerm′ : (fuel : ℕ) (Γ : RawCtxt) (fv : AllowedVars) → Term → TC (RawTerm Γ ⋆)
  reflectToRawTerm′ fuel Γ fv (var x []) = do
    σ , y ← reflectToRawVar Γ =<< strengthenVar fv x
    return (`appᵣ {Σ = record{ArgSorts = σ ∷ []}} (quote rawVar) (`varᵣ y ∷ []))
  reflectToRawTerm′ fuel Γ _  (var _ _)  = typeErrorFmt "Higher-order variable"
  reflectToRawTerm′ fuel Γ _  (lit l)    = return (`litᵣ l)
  reflectToRawTerm′ (suc fuel) Γ fv t@(def `fromNat _) = reflectToRawTerm′ fuel Γ fv =<< normalise t
  reflectToRawTerm′ (suc fuel) Γ fv t@(def `fromNeg _) = reflectToRawTerm′ fuel Γ fv =<< normalise t
  reflectToRawTerm′ (suc fuel) Γ fv (`Σ  a b) = reflectExist fuel Γ fv a b
  reflectToRawTerm′ (suc fuel) Γ fv (`Σˢ a b) = reflectExist fuel Γ fv a b
  reflectToRawTerm′ (suc fuel) Γ fv (`∃  a b) = reflectExist fuel Γ fv a b
  reflectToRawTerm′ (suc fuel) Γ fv (`∃ˢ a b) = reflectExist fuel Γ fv a b
  reflectToRawTerm′ fuel Γ fv (def f ts) = `appᵣ {Σ = argTypes ts} f <$> reflectToRawArgs fuel Γ fv ts
  reflectToRawTerm′ fuel Γ fv (con c ts) = `appᵣ {Σ = argTypes ts} c <$> reflectToRawArgs fuel Γ fv ts
  reflectToRawTerm′ fuel Γ fv (pi dom@(arg _ a) (abs x b)) = do
    case 0 ∈FV b of λ where
      true  →
        `forallᵣ x (TERM a) <$> extendContext dom (reflectToRawTerm′ fuel (TERM a ∷ Γ) (true ∷ fv) b)
      false → do
        a ← reflectToRawTerm′ fuel Γ fv a
        b ← extendContext dom (reflectToRawTerm′ fuel Γ (false ∷ fv) b)
        return (`appᵣ {Σ = record {ArgSorts = ⋆ ∷ ⋆ ∷ []}} (quote Morphism) (a ∷ b ∷ []))
  reflectToRawTerm′ fuel Γ fv (meta x _) = blockOnMeta x
  reflectToRawTerm′ fuel Γ fv t = typeErrorFmt "reflectToRawTerm′ failed"

  reflectExist : (fuel : ℕ) (Γ : RawCtxt) (fv : AllowedVars) → Term → Term → TC (RawTerm Γ ⋆)
  reflectExist fuel Γ fv a b = do
    lam _ (abs x b) ← return $ η-expand visible b
      where _ → typeErrorFmt "reflectedToRawTerm′ failed to η-expand existential predicate"
    `existsᵣ x (TERM a) <$> extendContext (vArg a) (reflectToRawTerm′ fuel (TERM a ∷ Γ) (true ∷ fv) b)

  reflectToRawArgs : ∀ (fuel : ℕ) Γ (fv : AllowedVars) (ts : List (Arg Term)) → TC (RawArgs Γ (ArgSorts (argTypes ts)))
  reflectToRawArgs fuel Γ fv [] = return []
  reflectToRawArgs fuel Γ fv (vArg t ∷ ts) = ⦇ reflectToRawTerm′ fuel Γ fv t ∷ reflectToRawArgs fuel Γ fv ts ⦈
  reflectToRawArgs fuel Γ fv (hArg _ ∷ ts) = reflectToRawArgs fuel Γ fv ts
  reflectToRawArgs fuel Γ fv (iArg _ ∷ ts) = reflectToRawArgs fuel Γ fv ts
  reflectToRawArgs fuel Γ fv (arg (arg-info visible   irrelevant) _ ∷ ts) = reflectToRawArgs fuel Γ fv ts
  reflectToRawArgs fuel Γ fv (arg (arg-info hidden    irrelevant) t ∷ ts) = reflectToRawArgs fuel Γ fv ts
  reflectToRawArgs fuel Γ fv (arg (arg-info instance′ irrelevant) t ∷ ts) = reflectToRawArgs fuel Γ fv ts

-- |Decode a reflected Agda type to a raw SMT-LIB script.
--
--  Functions are decoded as a series of assertions, with the result type
--  negated. For instance, the type `(x y : ℤ) → x - y ≤ x + y → x ≡ y`
--  is decoded as:
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
reflectToRawScript : Term → TC (∃[ Γ ] RawScript [] Γ [])
reflectToRawScript = reflectToRawScript′ [] []
  where
    reflectToRawScript′ : (Γ : RawCtxt) (fv : AllowedVars) → Term → TC (∃[ Γ′ ] RawScript Γ Γ′ [])
    reflectToRawScript′ Γ fv (pi dom@(arg _ a) (abs x b)) =
      case 0 ∈FV b of λ where
        true → do
          Γ′ , s ← extendContext dom $ reflectToRawScript′ (TERM a ∷ Γ) (true ∷ fv) b
          return (Γ′ , `declare-constᵣ x (TERM a) ∷ᵣ s)
        false → do
          t ← reflectToRawTerm Γ fv a
          Γ′ , s ← extendContext dom $ reflectToRawScript′ Γ (false ∷ fv) b
          return (Γ′ , `assertᵣ t ∷ᵣ s)
    reflectToRawScript′ Γ fv t = do
      t ← reflectToRawTerm Γ fv t
      return (Γ , `assertᵣ (`appᵣ (quote ¬_) (t ∷ [])) ∷ᵣ []ᵣ)
