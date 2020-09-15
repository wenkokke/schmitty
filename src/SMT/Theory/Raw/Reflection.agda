module SMT.Theory.Raw.Reflection where

open import Category.Monad
open import Data.Bool as Bool using (Bool; true; false; _∨_)
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.Integer as Int using (ℤ; +_; -[1+_])
open import Data.List as List using (List; _∷_; []; length)
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Nat as Nat using (ℕ; zero; suc; _∸_)
import Data.Nat.Literals as NatLits using (number)
open import Data.Product as Prod using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit as Unit using (⊤)
open import Function
open import Level using (Level)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl)
open import Reflection as Rfl hiding (return; _>>=_)
import Reflection.TypeChecking.Monad.Categorical as TC
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
reflectToRawVar (x ∷ Γ) zero    = return (_ , zero , refl)
reflectToRawVar (x ∷ Γ) (suc n) = do
  σ , i , refl ← reflectToRawVar Γ n
  return (σ , suc i , refl)


strengthenVar : (fv n : ℕ) → TC ℕ
strengthenVar fv n =
  case n Nat.<? fv of λ where
    (yes _) → typeErrorFmt "Dependent quantification in term"
    (no _)  → return (n ∸ fv)


private
  _∈-FVArgs_    : ℕ → List (Arg Term) → Bool
  _∈-FVClauses_ : ℕ → List Clause → Bool
  _∈-FVClause_  : ℕ → Clause → Bool
  _∈-FVSort_    : ℕ → Sort → Bool

  _∈-FV_ : ℕ → Term → Bool
  x ∈-FV var y args             = isYes (x Nat.≟ y) ∨ x ∈-FVArgs args
  x ∈-FV con _ args             = x ∈-FVArgs args
  x ∈-FV def _ args             = x ∈-FVArgs args
  x ∈-FV lam _ (abs _ t)        = suc x ∈-FV t
  x ∈-FV pat-lam cs args        = x ∈-FVClauses cs ∨ x ∈-FVArgs args
  x ∈-FV pi (arg _ a) (abs _ b) = x ∈-FV a ∨ suc x ∈-FV b
  x ∈-FV agda-sort s            = x ∈-FVSort s
  x ∈-FV lit l                  = false
  x ∈-FV meta _ args            = x ∈-FVArgs args
  x ∈-FV unknown                = false

  _ ∈-FVArgs []             = false
  x ∈-FVArgs (arg _ t ∷ ts) = x ∈-FV t ∨ x ∈-FVArgs ts

  x ∈-FVClauses []       = false
  x ∈-FVClauses (c ∷ cs) = x ∈-FVClause c ∨ x ∈-FVClauses cs

  -- Ignores types of bound variables
  x ∈-FVClause Clause.clause        tel ps t = (x Nat.+ length tel) ∈-FV t
  x ∈-FVClause Clause.absurd-clause tel ps   = false

  x ∈-FVSort Sort.set t   = x ∈-FV t
  x ∈-FVSort Sort.lit n   = false
  x ∈-FVSort Sort.unknown = false

-- Dummy name used as a function symbol of type TERM _ → ⋆ to wrap variables.
rawVar : ⊤
rawVar = _

private
  pattern `fromNat = quote Number.fromNat
  pattern `fromNeg = quote Negative.fromNeg

mutual
  -- |To avoid having to deal with overloaded literals in the different theories (the dictionaries
  --  are hard to deal with), we normalise any calls to fromNat and fromNeg.  To convince the
  --  termination checker that this is fine there's a fuel parameter limiting how many nested
  --  normalisations we are allowed to do. Overloading will not create any nested calls to fromNat
  --  or fromNeg so it's enough to provide 1 fuel.
  reflectToRawTerm : (fuel : ℕ) (Γ : RawCtxt) (fv : ℕ) → Term → TC (RawTerm Γ ⋆)
  reflectToRawTerm fuel Γ fv (var x []) = do
    σ , y ← reflectToRawVar Γ =<< strengthenVar fv x
    return (appᵣ {Σ = record{ArgSorts = σ ∷ []}} (quote rawVar) (varᵣ y ∷ []))
  reflectToRawTerm fuel Γ _  (var _ _)  = typeErrorFmt "Higher-order variable"
  reflectToRawTerm fuel Γ _  (lit l)    = return (litᵣ l)
  reflectToRawTerm (suc fuel) Γ fv t@(def `fromNat _) = reflectToRawTerm fuel Γ fv =<< normalise t
  reflectToRawTerm (suc fuel) Γ fv t@(def `fromNeg _) = reflectToRawTerm fuel Γ fv =<< normalise t
  reflectToRawTerm fuel Γ fv (def f ts) = appᵣ {Σ = argTypes ts} f <$> reflectToRawArgs fuel Γ fv ts
  reflectToRawTerm fuel Γ fv (con c ts) = appᵣ {Σ = argTypes ts} c <$> reflectToRawArgs fuel Γ fv ts
  reflectToRawTerm fuel Γ fv (pi (arg _ a) (abs _ b)) = do
    a ← reflectToRawTerm fuel Γ fv a
    b ← reflectToRawTerm fuel Γ (suc fv) b
    return (appᵣ {Σ = record {ArgSorts = ⋆ ∷ ⋆ ∷ []}} (quote Morphism) (a ∷ b ∷ []))
  reflectToRawTerm fuel Γ fv (meta x _) = blockOnMeta x
  reflectToRawTerm fuel Γ fv t = typeErrorFmt "reflectToRawTerm failed"

  reflectToRawArgs : ∀ (fuel : ℕ) Γ (fv : ℕ) (ts : List (Arg Term)) → TC (RawArgs Γ (ArgSorts (argTypes ts)))
  reflectToRawArgs fuel Γ fv [] = return []
  reflectToRawArgs fuel Γ fv (vArg t ∷ ts) = ⦇ reflectToRawTerm fuel Γ fv t ∷ reflectToRawArgs fuel Γ fv ts ⦈
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
reflectToRawScript = reflectToRawScript′ [] 0
  where
    reflectToRawScript′ : (Γ : RawCtxt) (fv : ℕ) → Term → TC (∃[ Γ′ ] RawScript Γ Γ′ [])
    reflectToRawScript′ Γ fv (pi (arg _ a) (abs x b)) =
      case 0 ∈-FV b of λ where
        true → do
          Γ′ , s ← reflectToRawScript′ (TERM a ∷ Γ) fv b
          return (Γ′ , declare-constᵣ x (TERM a) ∷ᵣ s)
        false → do
          t ← reflectToRawTerm 1 Γ fv a
          Γ′ , s ← reflectToRawScript′ Γ (suc fv) b
          return (Γ′ , assertᵣ t ∷ᵣ s)
    reflectToRawScript′ Γ fv t = do
      t ← reflectToRawTerm 1 Γ fv t
      return (Γ , assertᵣ (appᵣ (quote ¬_) (t ∷ [])) ∷ᵣ []ᵣ)
