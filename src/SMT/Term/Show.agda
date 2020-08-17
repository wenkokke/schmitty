open import Data.List using (List)
open import Data.String using (String)

module SMT.Term.Show
  {s i l}
  (Sort : Set s)
  (Bool : Sort)
  (Literal : Sort → Set l)
  (Identifier : List Sort → Sort → Set i)
  (showSort : Sort → String)
  (showLiteral : ∀ {σ} → Literal σ → String)
  (showIdentifier : ∀ {Σ : List Sort} {σ} → Identifier Σ σ → String)
  where

open import Category.Monad.State using (RawIMonadState; StateTIMonadState; IStateT)
open import Codata.Musical.Stream as Stream using (Stream)
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.List as List using (_∷_; [])
open import Data.Nat as Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product as Product using (proj₁; _,_)
open import Data.String as String using (_++_)
open import Data.Unit as Unit using (⊤)
open import Function using (const; id; _∘_)
import Function.Identity.Categorical as Identity
open import Level using (Lift; lift; lower)
open import SMT.Term Sort Bool Literal Identifier

private
  variable
    σ : Sort
    Σ : Ctxt
    Γ : Ctxt
    T : Sort → Set

-- |Environments, i.e., lists where the types of the elements
--  are determined by a type-level list.
data Env (T : Sort → Set) : (Γ : Ctxt) → Set where
  []  : Env T []
  _∷_ : T σ → Env T Γ → Env T (σ ∷ Γ)

-- |Name states, i.e., an environment of names, one for every
--  variable in the context Γ, and a supply  of fresh names.
--
--  NOTE: the current implementation does not guarantee that
--        each name in the supply is distinct. If we need this
--        in the future, there is `Data.List.Fresh`.
--
record Names (Γ : Ctxt) : Set s where
  field
    nameEnv    : Env (const String) Γ
    nameSupply : Stream String

open Names -- bring `nameEnv` and `nameSupply` in scope

-- When showing terms, we need to pass around a name state,
-- for which we'll use an indexed monad, indexed by the context,
-- so we bring the functions from the indexed monad in scope.
open RawIMonadState (StateTIMonadState Names Identity.monad)

-- |Get the first element in a non-empty environment.
head : Env T (σ ∷ Γ) → T σ
head (x ∷ _env) = x

-- |Remove the first element from a non-empty environment.
tail : Env T (σ ∷ Γ) → Env T Γ
tail (_x ∷ env) = env

-- |Get the i'th element from an environment.
lookup : (env : Env T Γ) (i : Fin _) → T (List.lookup Γ i)
lookup []          ()
lookup ( x ∷ _env) zero    = x
lookup (_x ∷  env) (suc i) = lookup env i

-- |Add a fresh name to the front of the name environment.
pushFreshName′ : (σ : Sort) → Names Γ → Names (σ ∷ Γ)
nameEnv    (pushFreshName′ σ names) = Stream.head (nameSupply names) ∷ nameEnv names
nameSupply (pushFreshName′ σ names) = Stream.tail (nameSupply names)

-- |Add a fresh name to the front of the name environment in the state monad.
pushFreshName : (σ : Sort) → IStateT Names id Γ (σ ∷ Γ) (Lift s String)
pushFreshName σ = do
  names ← get
  let names′ = pushFreshName′ σ names
  put names′
  return (lift (head (nameEnv names′)))

-- |Remove first name from the name environment.
popName′ : Names (σ ∷ Γ) → Names Γ
nameEnv    (popName′ names) = tail (nameEnv names)
nameSupply (popName′ names) = nameSupply names

-- |Remove first name from the name environment in the state monad.
popName : IStateT Names id (σ ∷ Γ) Γ (Lift s ⊤)
popName = modify popName′

-- |Get i'th name from the name environment in the state monad.
getName : (i : Γ ∋ σ) → IStateT Names id Γ Γ (Lift s String)
getName (i , _prf) = do
  names ← get
  return (lift (lookup (nameEnv names) i))

-- |Create an S-expression from a list of strings.
--
-- @
--   mkSExpr ("*" ∷ "4" ∷ "5") ≡ "(* 4 5)"
-- @
--
mkSExpr : List String → String
mkSExpr = String.parens ∘ String.unwords

mutual

  -- |Show a term as an S-expression. The code below passes a name state in
  --  a state monad. For the pure version, see `showTerm` below.
  --
  --  The state monad `IStateT` forces us the return-type to be in `Set s`,
  --  whereas `String : Set`. Therefore, we must use `Lift s String`. This
  --  inserts some noise, i.e., uses of the `lift` and `lower`.
  --
  showTerm′ : Term Γ σ → IStateT Names id Γ Γ (Lift s String)
  showTerm′ (var i) =
    getName i
  showTerm′ (lit l) =
    return (lift (showLiteral l))
  showTerm′ (app x xs) = do
    let x′ = showIdentifier x
    xs′ ← showArgs′ xs
    return (lift (mkSExpr (x′ ∷ lower xs′)))
  showTerm′ (forAll {σ} x) = do
    n′ ← pushFreshName σ
    let σ′ = showSort σ
    x′ ← showTerm′ x
    popName
    return (lift (mkSExpr ("forall" ∷ mkSExpr (lower n′ ∷ σ′ ∷ []) ∷ lower x′ ∷ [])))
  showTerm′ (exists {σ} x) = do
    n′ ← pushFreshName σ
    let σ′ = showSort σ
    x′ ← showTerm′ x
    popName
    return (lift (mkSExpr ("exists" ∷ mkSExpr (lower n′ ∷ σ′ ∷ []) ∷ lower x′ ∷ [])))

  -- |Show a series of terms as S-expression.
  --
  --  This is explicit to avoid sized-types, as Agda cannot infer that the call
  --  `mapM showTerm′ xs` terminates.
  --
  showArgs′ : Args Γ Σ → IStateT Names id Γ Γ (Lift s (List String))
  showArgs′ [] =
    return (lift [])
  showArgs′ (x ∷ xs) = do
    x′ ← showTerm′ x
    xs′ ← showArgs′ xs
    return (lift (lower x′ ∷ lower xs′))

-- |A name state for the empty context, which supplies the names x0, x1, x2, ...
x′es : Names []
nameEnv    x′es = []
nameSupply x′es = Stream.map (λ n → "x" ++ showℕ n) (Stream.iterate ℕ.suc 0)

-- |Show a term as an S-expression.
showTerm : Names Γ → Term Γ σ → String
showTerm names x = lower (proj₁ (showTerm′ x names))
