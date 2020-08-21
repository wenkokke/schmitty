{-# OPTIONS --without-K #-}

open import SMT.Theory

module SMT.Script {s i l} (theory : Theory s i l) where

open import Data.Fin as Fin using (Fin)
open import Data.List as List using (List; _∷_; [])
open import Data.Product using (∃-syntax; _,_)
open import Level using (Lift; lift; lower; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Logics

open Theory theory


-------------------
-- SMT-LIB Terms --
-------------------

-- |Typing contexts.
Ctxt : Set s
Ctxt = List Sort

private
  variable
    σ σ′    : Sort
    Γ Γ′ Γ″ : Ctxt
    Δ Δ′    : Ctxt
    Σ       : Signature σ
    Σ′      : Signature σ′

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

---------------------
-- SMT-LIB Results --
---------------------

-- |Possible results.
data OutputType : Set s where
  SAT   : OutputType
  MODEL : Ctxt → OutputType

-- |Result contexts.
OutputCtxt : Set s
OutputCtxt = List OutputType

private
  variable
    ξ ξ′    : OutputType
    Ξ Ξ′    : OutputCtxt

-- |SMT-LIB satisfiability.
data Sat : Set where
  sat     : Sat
  unsat   : Sat
  unknown : Sat

-- |SMT-LIB models.
data Model : (Γ : Ctxt) → Set (s ⊔ i ⊔ l) where
  []  : Model []
  _∷_ : Term [] σ → Model Γ → Model (σ ∷ Γ)

-- |SMT-LIB script result.
Result : OutputType → Set (s ⊔ i ⊔ l)
Result SAT       = Lift _ Sat
Result (MODEL Γ) = Model Γ

-- |List of SMT-LIB results.
data Results : (Ξ : OutputCtxt) → Set (s ⊔ i ⊔ l) where
  []  : Results []
  _∷_ : Result ξ → Results Ξ → Results (ξ ∷ Ξ)


----------------------
-- SMT-LIB Commands --
----------------------

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
  set-logic     : (l : Logic) → Command Γ Ξ Γ Ξ
  declare-const : (σ : Sort) → Command Γ Ξ (σ ∷ Γ) Ξ
  assert        : Term Γ BOOL → Command Γ Ξ Γ Ξ
  check-sat     : Command Γ Ξ Γ (SAT ∷ Ξ)
  get-model     : Command Γ (SAT ∷ Ξ) Γ (MODEL Γ ∷ SAT ∷ Ξ)


---------------------
-- SMT-LIB Scripts --
---------------------

-- |SMT-LIB scripts.
data Script (Γ : Ctxt) : (Γ″ : Ctxt) (Ξ : OutputCtxt) → Set (s ⊔ i ⊔ l) where
  []  : Script Γ Γ []
  _∷_ : Command Γ Ξ Γ′ Ξ′ → Script Γ′ Γ″ Ξ → Script Γ Γ″ Ξ′


--------------------------
-- Printing and Parsing --
--------------------------

module Interaction
  (printable : Printable theory)
  where

  open import Category.Monad.State using (RawIMonadState; StateTIMonadState; IStateT)
  open import Codata.Musical.Stream as Stream using (Stream)
  open import Data.Nat as Nat using (ℕ)
  open import Data.Nat.Show renaming (show to showℕ)
  open import Data.Product as Product using (proj₁)
  open import Data.String as String using (String; _++_)
  open import Data.Unit as Unit using (⊤)
  open import Function using (const; id; _∘_)
  import Function.Identity.Categorical as Identity
  open import Level using (Level; _⊔_; Lift; lift; lower)

  open Printable printable

  private
    variable
      ℓ : Level
      T : Sort → Set ℓ

  -- |Environments, i.e., lists where the types of the elements
  --  are determined by a type-level list.
  data Env (T : Sort → Set ℓ) : (Γ : Ctxt) → Set (s ⊔ ℓ) where
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
  lookup ( x ∷ _env) Fin.zero    = x
  lookup (_x ∷  env) (Fin.suc i) = lookup env i

  -- |Add a fresh name to the front of the name environment.
  pushFreshName : (σ : Sort) → IStateT Names id Γ (σ ∷ Γ) (Lift s String)
  pushFreshName σ = do
    names ← get
    let names′ = pushFreshName′ σ names
    put names′
    return (lift (head (nameEnv names′)))
    where
      pushFreshName′ : (σ : Sort) → Names Γ → Names (σ ∷ Γ)
      nameEnv    (pushFreshName′ σ names) = Stream.head (nameSupply names) ∷ nameEnv names
      nameSupply (pushFreshName′ σ names) = Stream.tail (nameSupply names)


  -- |Remove first name from the name environment.
  popName : IStateT Names id (σ ∷ Γ) Γ (Lift s ⊤)
  popName = modify popName′
    where
      popName′ : Names (σ ∷ Γ) → Names Γ
      nameEnv    (popName′ names) = tail (nameEnv names)
      nameSupply (popName′ names) = nameSupply names


  -- |Get i'th name from the name environment in the state monad.
  getName : (i : Γ ∋ σ) → IStateT Names id Γ Γ (Lift s String)
  getName (i , _prf) = do
    names ← get
    return (lift (lookup (nameEnv names) i))

  -- |Create an S-expression from a list of strings.
  --
  -- @
  --   mkSTerm ("*" ∷ "4" ∷ "5") ≡ "(* 4 5)"
  -- @
  --
  mkSTerm : List String → String
  mkSTerm = String.parens ∘ String.unwords

  mutual

    -- |Show a term as an S-expression. The code below passes a name state in
    --  a state monad. For the pure version, see `showTerm` below.
    --
    --  The state monad `IStateT` forces us the return-type to be in `Set s`,
    --  whereas `String : Set`. Therefore, we must use `Lift s String`. This
    --  inserts some noise, i.e., uses of the `lift` and `lower`.
    --
    showTermS : Term Γ σ → IStateT Names id Γ Γ (Lift s String)
    showTermS (var i) =
      getName i
    showTermS (lit l) =
      return (lift (showLiteral l))
    showTermS (app x xs) = do
      let x′ = showIdentifier x
      xs′ ← showArgsS xs
      return (lift (mkSTerm (x′ ∷ lower xs′)))
    showTermS (forAll {σ} x) = do
      n′ ← pushFreshName σ
      let σ′ = showSort σ
      x′ ← showTermS x
      popName
      let nσs′ = mkSTerm (mkSTerm (lower n′ ∷ σ′ ∷ []) ∷ [])
      return (lift (mkSTerm ("forall" ∷ nσs′ ∷ lower x′ ∷ [])))
    showTermS (exists {σ} x) = do
      n′ ← pushFreshName σ
      let σ′ = showSort σ
      x′ ← showTermS x
      popName
      let nσs′ = mkSTerm (mkSTerm (lower n′ ∷ σ′ ∷ []) ∷ [])
      return (lift (mkSTerm ("exists" ∷ nσs′ ∷ lower x′ ∷ [])))

    -- |Show a series of terms as S-expression.
    --
    --  This is explicit to avoid sized-types, as Agda cannot infer that the call
    --  `mapM showTermS xs` terminates.
    --
    showArgsS : Args Γ Δ → IStateT Names id Γ Γ (Lift s (List String))
    showArgsS [] =
      return (lift [])
    showArgsS (x ∷ xs) = do
      x′ ← showTermS x
      xs′ ← showArgsS xs
      return (lift (lower x′ ∷ lower xs′))

  -- |Show a command as an S-expression. The code below passes a name state in
  --  a state monad. For the pure version, see `showCommand` below.
  showCommandS : Command Γ′ Ξ′ Γ Ξ → IStateT Names id Γ′ Γ (Lift s String)
  showCommandS (set-logic l) =
    return (lift (mkSTerm ("set-logic" ∷ showLogic l ∷ [])))
  showCommandS (declare-const σ) = do
    n′ ← pushFreshName σ
    let σ′ = showSort σ
    return (lift (mkSTerm ("declare-const" ∷ lower n′ ∷ σ′ ∷ [])))
  showCommandS (assert x) = do
    x′ ← showTermS x
    return (lift (mkSTerm ("assert" ∷ lower x′ ∷ [])))
  showCommandS check-sat =
    return (lift (mkSTerm ("check-sat" ∷ [])))
  showCommandS get-model =
    return (lift (mkSTerm ("get-model" ∷ [])))

  -- |Show a script as an S-expression. The code below passes a name state in
  --  a state monad. For the pure version, see `showScript` below.
  showScriptS : Script Γ Γ′ Ξ → IStateT Names id Γ Γ′ (Lift s (List String))
  showScriptS [] =
    return (lift [])
  showScriptS (cmd ∷ cmds) = do
    cmd′ ← showCommandS cmd
    cmds′ ← showScriptS cmds
    return (lift (lower cmd′ ∷ lower cmds′))

  -- |A name state for the empty context, which supplies the names x0, x1, x2, ...
  x′es : Names []
  nameEnv    x′es = []
  nameSupply x′es = Stream.map (λ n → "x" ++ showℕ n) (Stream.iterate ℕ.suc 0)

  -- |Show a term as an S-expression.
  showTerm : Names Γ → Term Γ σ → String
  showTerm names x = lower (proj₁ (showTermS x names))

  -- |Show a command as an S-expression.
  showCommand : Names Γ → Command Γ Ξ Γ′ Ξ′ → String
  showCommand names cmd = lower (proj₁ (showCommandS cmd names))

  -- |Show a script as an S-expression.
  showScript : Names Γ → Script Γ Γ′ Ξ → String
  showScript names cmd = String.unlines (lower (proj₁ (showScriptS cmd names)))
