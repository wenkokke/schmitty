
module SMT.Theories.Raw.Reflection where

open import Level using (Level)
open import Data.Bool
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat as Nat using (ℕ; zero; suc; _∸_)
open import Data.Integer as Int using (ℤ; +_; -[1+_])
open import Data.List using (List; _∷_; []; length)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Maybe hiding (_>>=_)
open import Data.Product as Prod using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Reflection as Rfl hiding (_>>=_; return)
import Reflection.TypeChecking.Monad.Categorical as TC
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Unit

open import Function

open import Category.Monad
open import Data.Environment

open import SMT.Theory
open import SMT.Theories.Raw

open module TCMonad {ℓ} = Category.Monad.RawMonad {ℓ} TC.monad renaming (_⊛_ to _<*>_)

private
  variable
    ℓ : Level
    A : Set ℓ

private
  -- We don't know the type of raw function symbols, so just look at
  -- the arguments. Design decision: only keep visible arguments.
  argTypes : List (Arg A) → Signature ⋆
  argTypes []              .ArgTypes = []
  argTypes (vArg _ ∷ args) .ArgTypes = _ ∷ argTypes args .ArgTypes
  argTypes (_      ∷ args) .ArgTypes =     argTypes args .ArgTypes

decodeVar : (Γ : RawCtxt) (n : ℕ) → TC (RawVar Γ)
decodeVar []      n       = typeErrorFmt "Variable out of bounds"
decodeVar (x ∷ Γ) zero    = return (zero , refl)
decodeVar (x ∷ Γ) (suc n) = do
  i , refl ← decodeVar Γ n
  return (suc i , refl)

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

decodeArgs : ∀ Γ (fv : ℕ) (ts : List (Arg Term)) → TC (RawArgs Γ (ArgTypes (argTypes ts)))

decodeTerm : (Γ : RawCtxt) (fv : ℕ) → Term → TC (RawTerm Γ ⋆)
decodeTerm Γ fv (var x [])  = varᵣ <$> (decodeVar Γ =<< strengthenVar fv x)
decodeTerm Γ _  (var _ _)   = typeErrorFmt "Higher-order variable"
decodeTerm Γ _ t@(lit _)   = return (litᵣ t)
decodeTerm Γ fv (def f ts)  = appᵣ {Σ = argTypes ts} f <$> decodeArgs Γ fv ts
decodeTerm Γ fv (con c ts)  = appᵣ {Σ = argTypes ts} c <$> decodeArgs Γ fv ts
decodeTerm Γ fv (pi (arg _ a) (abs _ b)) = do
  a ← decodeTerm Γ fv a
  b ← decodeTerm Γ (suc fv) b
  return (appᵣ {Σ = record {ArgTypes = ⋆ ∷ ⋆ ∷ []}} (quote Morphism) (a ∷ b ∷ []))
decodeTerm Γ fv (meta x _) = blockOnMeta x
decodeTerm Γ fv t = typeErrorFmt "decodeTerm failed"

decodeArgs Γ fv [] = return []
decodeArgs Γ fv (vArg t ∷ ts) = ⦇ decodeTerm Γ fv t ∷ decodeArgs Γ fv ts ⦈
decodeArgs Γ fv (hArg _ ∷ ts) = decodeArgs Γ fv ts
decodeArgs Γ fv (iArg _ ∷ ts) = decodeArgs Γ fv ts
decodeArgs Γ fv (arg (arg-info visible   irrelevant) _ ∷ ts) = decodeArgs Γ fv ts
decodeArgs Γ fv (arg (arg-info hidden    irrelevant) t ∷ ts) = decodeArgs Γ fv ts
decodeArgs Γ fv (arg (arg-info instance′ irrelevant) t ∷ ts) = decodeArgs Γ fv ts

decodeScript : (Γ : RawCtxt) (fv : ℕ) → Term → TC (∃[ Γ′ ] RawScript Γ Γ′ [])
decodeScript Γ fv (pi (arg _ a) (abs _ b)) =
  case 0 ∈-FV b of λ where
    true → do
      Γ′ , s ← decodeScript (⋆ ∷ Γ) fv b
      return (Γ′ , declare-constᵣ ⋆ ∷ᵣ s)
    false → do
      t ← decodeTerm Γ fv a
      Γ′ , s ← decodeScript Γ (suc fv) b
      return (Γ′ , assertᵣ t ∷ᵣ s)
decodeScript Γ fv t = do
  t ← decodeTerm Γ fv t
  return (Γ , assertᵣ (appᵣ {Σ = record{ArgTypes = ⋆ ∷ []}} (quote ¬_) (t ∷ [])) ∷ᵣ []ᵣ)

postulate
  debug : {A B : Set} → A → B

`debug : Term → Term
`debug t = def (quote debug) (vArg t ∷ [])

macro
  testDecode : Term → TC ⊤
  testDecode hole = do
    goal ← inferType hole
    Γ , s ← decodeScript [] 0 goal
    unify hole ∘ `debug =<< quoteTC s

test : (x y : ℤ) → x Int.- y Int.≤ x Int.+ y → x ≡ y
test = testDecode

_ : test ≡ debug {A = RawScript [] (⋆ ∷ ⋆ ∷ []) []}
                 (  declare-constᵣ ⋆
                 ∷ᵣ declare-constᵣ ⋆
                 ∷ᵣ assertᵣ
                      (appᵣ (quote Int._≤_)
                        (appᵣ (quote Int._-_)
                          (varᵣ (suc zero , refl) ∷ (varᵣ (zero , refl) ∷ [])) ∷
                          (appᵣ (quote Int._+_)
                            (varᵣ (suc zero , refl) ∷ (varᵣ (zero , refl) ∷ [])) ∷ [])))
                 ∷ᵣ assertᵣ
                      (appᵣ (quote ¬_)
                        (appᵣ (quote _≡_)
                          (varᵣ (suc zero , refl) ∷ (varᵣ (zero , refl) ∷ [])) ∷ []))
                 ∷ᵣ []ᵣ)
_ = refl
