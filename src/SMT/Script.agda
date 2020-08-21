open import SMT.Theory

module SMT.Script (theory : Theory) where

open import Data.Fin as Fin using (Fin)
open import Data.List as List using (List; _∷_; []; _++_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Product as Prod using (∃; ∃-syntax; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Logics

open Theory theory


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
    forAll : ∀ {σ} (x : Term (σ ∷ Γ) BOOL) → Term Γ BOOL
    exists : ∀ {σ} (x : Term (σ ∷ Γ) BOOL) → Term Γ BOOL

  data Args (Γ : Ctxt) : (Δ : Ctxt) → Set where
    []  : Args Γ []
    _∷_ : Term Γ σ → Args Γ Δ → Args Γ (σ ∷ Δ)

pattern app₁ f x     = app f (x ∷ [])
pattern app₂ f x y   = app f (x ∷ y ∷ [])
pattern app₃ f x y z = app f (x ∷ y ∷ z ∷ [])

Rename : (Γ Δ : Ctxt) → Set
Rename Γ Δ = ∀ {σ} → Γ ∋ σ → Δ ∋ σ

extendVar : Γ ∋ σ → (σ′ ∷ Γ) ∋ σ
extendVar (i , p) = Fin.suc i , p

extendRename : Rename Γ Γ′ → Rename (σ ∷ Γ) (σ ∷ Γ′)
extendRename r (Fin.zero  , p) = Fin.zero , p
extendRename r (Fin.suc i , p) = extendVar (r (i , p))

mutual
  rename : Rename Γ Γ′ → Term Γ σ → Term Γ′ σ
  rename r (var i)    = var (r i)
  rename r (lit l)    = lit l
  rename r (app x xs) = app x (renameArgs r xs)
  rename r (forAll x) = forAll (rename (extendRename r) x)
  rename r (exists x) = exists (rename (extendRename r) x)

  renameArgs : Rename Γ Γ′ → Args Γ Δ → Args Γ′ Δ
  renameArgs r [] = []
  renameArgs r (x ∷ xs) = rename r x ∷ renameArgs r xs

weaken : Term Γ σ → Term (σ′ ∷ Γ) σ
weaken = rename extendVar

---------------------
-- SMT-LIB Results --
---------------------

-- |Possible results.
data OutputType : Set where
  SAT   : OutputType
  MODEL : Ctxt → OutputType

-- |Result contexts.
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
data Model : (Γ : Ctxt) → Set where
  []  : Model []
  _∷_ : Term [] σ → Model Γ → Model (σ ∷ Γ)

-- |SMT-LIB script result.
Result : OutputType → Set
Result SAT       = Sat
Result (MODEL Γ) = Model Γ

-- |List of SMT-LIB results.
data Results : (Ξ : OutputCtxt) → Set where
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
data Command (Γ : Ctxt) : (Ξ : OutputCtxt) (δΓ : Ctxt) (δΞ : OutputCtxt) → Set where
  set-logic     : (l : Logic) → Command Γ Ξ [] []
  declare-const : (σ : Sort) → Command Γ Ξ (σ ∷ []) []
  assert        : Term Γ BOOL → Command Γ Ξ [] []
  check-sat     : Command Γ Ξ [] (SAT ∷ [])
  get-model     : Command Γ (SAT ∷ Ξ) [] (MODEL Γ ∷ [])


---------------------
-- SMT-LIB Scripts --
---------------------

-- |SMT-LIB scripts.
data Script (Γ : Ctxt) : (Γ′ : Ctxt) (Ξ : OutputCtxt) → Set where
  []  : Script Γ Γ []
  _∷_ : Command Γ Ξ δΓ δΞ → Script (δΓ ++ Γ) Γ′ Ξ → Script Γ Γ′ (δΞ ++ Ξ)


--------------------------
-- Printing and Parsing --
--------------------------

module Interaction
  (printable : Printable theory)
  (parsable : Parsable theory)
  where

  open import Category.Monad
  open import Category.Monad.State as StateCat using (RawIMonadState; IStateT)
  open import Codata.Musical.Stream as Stream using (Stream)
  open import Data.Char as Char using (Char)
  open import Data.Nat as Nat using (ℕ)
  open import Data.Nat.Show renaming (show to showℕ)
  open import Data.Product as Product using (_×_; _,_; -,_; proj₁; proj₂)
  open import Data.String as String using (String)
  open import Data.Unit as Unit using (⊤)
  open import Data.Vec as Vec using (Vec)
  open import Function using (const; id; _∘_; _$_)
  import Function.Identity.Categorical as Identity
  open import Text.Parser.String
  open import Reflection using (con; hArg; vArg)

  open Printable printable
  open Parsable parsable

  private
    variable
      T T′ : Sort → Set


  -- |Names.
  Name : Set
  Name = List⁺ Char

  -- |Show names.
  showName : Name → String
  showName = String.fromList ∘ List⁺.toList


  -- |Environments, i.e., lists where the types of the elements
  --  are determined by a type-level list.
  data NameEnv : (Γ : Ctxt) → Set where
    []  : NameEnv []
    _∷_ : Name → NameEnv Γ → NameEnv (σ ∷ Γ)


  -- |Get the first element in a non-empty environment.
  headName : NameEnv (σ ∷ Γ) → Name
  headName (x ∷ _env) = x


  -- |Remove the first element from a non-empty environment.
  tailName : NameEnv (σ ∷ Γ) → NameEnv Γ
  tailName (_x ∷ env) = env


  -- |Get the i'th element from an environment.
  lookupName : (env : NameEnv Γ) (i : Fin (List.length Γ)) → Name
  lookupName []          ()
  lookupName ( x ∷ _env) Fin.zero    = x
  lookupName (_x ∷  env) (Fin.suc i) = lookupName env i


  -- |Name states, i.e., an environment of names, one for every
  --  variable in the context Γ, and a supply  of fresh names.
  --
  --  NOTE: the current implementation does not guarantee that
  --        each name in the supply is distinct. If we need this
  --        in the future, there is `Data.List.Fresh`.
  --
  record Names (Γ : Ctxt) : Set where
    field
      nameEnv    : NameEnv Γ
      nameSupply : Stream Name

  open Names -- bring `nameEnv` and `nameSupply` in scope

  -- When showing terms, we need to pass around a name state,
  -- for which we'll use an indexed monad, indexed by the context,
  -- so we bring the functions from the indexed monad in scope.
  private
    monadStateNameState = StateCat.StateTIMonadState Names Identity.monad

  open RawIMonadState monadStateNameState
    using (return; _>>=_; _>>_; put; get; modify)


  -- |Add a fresh name to the front of the name environment.
  pushFreshName : (σ : Sort) → IStateT Names id Γ (σ ∷ Γ) Name
  pushFreshName σ = do
    names ← get
    let names′ = pushFreshName′ σ names
    put names′
    return (headName (nameEnv names′))
    where
      pushFreshName′ : (σ : Sort) → Names Γ → Names (σ ∷ Γ)
      nameEnv    (pushFreshName′ σ names) = Stream.head (nameSupply names) ∷ nameEnv names
      nameSupply (pushFreshName′ σ names) = Stream.tail (nameSupply names)


  -- |Remove first name from the name environment.
  popName : IStateT Names id (σ ∷ Γ) Γ ⊤
  popName = do modify popName′; return _
    where
      popName′ : Names (σ ∷ Γ) → Names Γ
      nameEnv    (popName′ names) = tailName (nameEnv names)
      nameSupply (popName′ names) = nameSupply names


  -- |Get i'th name from the name environment in the state monad.
  getName : (i : Γ ∋ σ) → IStateT Names id Γ Γ Name
  getName (i , _prf) = do
    names ← get
    return (lookupName (nameEnv names) i)


  -- |Create an S-expression from a list of strings.
  --
  -- @
  --   mkSTerm ("*" ∷ "4" ∷ "5") ≡ "(* 4 5)"
  -- @
  --
  mkSTerm : List String → String
  mkSTerm = String.parens ∘ String.unwords


  data EnvParser : (Γ : Ctxt) → Set where
    []  : EnvParser []
    _∷_ : ∀[ Parser ((σ ∷ Γ) ∋ σ) ] → EnvParser Γ → EnvParser (σ ∷ Γ)

  -- |Extend an environment with a number of failing parsers.
  extendEP : (δΓ : Ctxt) → EnvParser Γ → EnvParser (δΓ ++ Γ)
  extendEP []       env = env
  extendEP (σ ∷ δΓ) env = fail ∷ extendEP δΓ env

  -- |An environment of failing variable parsers.
  failEP : (Γ : Ctxt) → EnvParser Γ
  failEP []      = []
  failEP (σ ∷ Γ) = fail ∷ failEP Γ

  -- |A singleton variable parser.
  varEP : Name → Γ ∋ σ → EnvParser Γ
  varEP {σ′ ∷ Γ} n x@(Fin.zero  , refl) = (x <$ exacts n) ∷ failEP Γ
  varEP {σ′ ∷ Γ} n   (Fin.suc i , p)    = fail ∷ varEP {Γ} n (i , p)

  -- |Remove the outermost variable parser.
  dropEP : EnvParser (σ ∷ Γ) → EnvParser Γ
  dropEP (_ ∷ env) = env

  -- |Merge two environments of variable parsers.
  _<||>_ : EnvParser Γ → EnvParser Γ → EnvParser Γ
  [] <||> [] = []
  (p₁ ∷ env₁) <||> (p₂ ∷ env₂) = (p₁ <|> p₂) ∷ (env₁ <||> env₂)

  mutual

    -- |Show a term as an S-expression. The code below passes a name state in
    --  a state monad. For the pure version, see `showTerm` below.
    --
    showTermS : Term Γ σ → IStateT Names id Γ Γ (String × EnvParser Γ)
    showTermS {Γ} {σ} (var i) = do
      n ← getName i
      return (showName n , varEP n i)
    showTermS {Γ} {σ} (lit l) =
      return (showLiteral l , failEP Γ)
    showTermS (app x xs) = do
      let x = showIdentifier x
      (xs , p) ← showArgsS xs
      return (mkSTerm (x ∷ xs) , p)
    showTermS (forAll {σ} x) = do
      n ← pushFreshName σ
      (x , p) ← showTermS x
      popName
      let nσs = mkSTerm (mkSTerm (showName n ∷ showSort σ ∷ []) ∷ [])
      return (mkSTerm ("forall" ∷ nσs ∷ x ∷ []) , dropEP p)
    showTermS (exists {σ} x) = do
      n ← pushFreshName σ
      (x , p) ← showTermS x
      popName
      let nσs = mkSTerm (mkSTerm (showName n ∷ showSort σ ∷ []) ∷ [])
      return (mkSTerm ("exists" ∷ nσs ∷ x ∷ []) , dropEP p)

    -- |Show a series of terms as S-expression.
    --
    --  This is explicit to avoid sized-types, as Agda cannot infer that the call
    --  `mapM showTermS xs` terminates.
    --
    showArgsS : Args Γ Δ → IStateT Names id Γ Γ (List String × EnvParser Γ)
    showArgsS {Γ} {Δ} [] =
      return ([] , failEP Γ)
    showArgsS {Γ} {Δ} (x ∷ xs) = do
      (x , p₁) ← showTermS x
      (xs , p₂) ← showArgsS xs
      return (x ∷ xs , (p₁ <||> p₂))


  -- |Show a command as an S-expression. The code below passes a name state in
  --  a state monad. For the pure version, see `showCommand` below.
  showCommandS : Command Γ Ξ δΓ δΞ → IStateT Names id Γ (δΓ ++ Γ) (String × EnvParser (δΓ ++ Γ))
  showCommandS {Γ′} {Ξ′} (set-logic l) =
    return (mkSTerm ("set-logic" ∷ showLogic l ∷ []) , failEP Γ′)
  showCommandS {Γ′} {Ξ′} (declare-const σ) = do
    n ← pushFreshName σ
    let p = varEP n (Fin.zero , refl)
    return (mkSTerm ("declare-const" ∷ showName n ∷ showSort σ ∷ []) , p)
  showCommandS {Γ′} {Ξ′} (assert x) = do
    (x , p) ← showTermS x
    return (mkSTerm ("assert" ∷ x ∷ []) , p)
  showCommandS {Γ′} {Ξ′} check-sat =
    return (mkSTerm ("check-sat" ∷ []) , failEP Γ′)
  showCommandS {Γ′} {Ξ′} get-model =
    return (mkSTerm ("get-model" ∷ []) , failEP Γ′)

  -- |Show a script as an S-expression. The code below passes a name state in
  --  a state monad. For the pure version, see `showScript` below.
  showScriptS : Script Γ Γ′ Ξ → IStateT Names id Γ Γ′ (List String × (EnvParser Γ → EnvParser Γ′))
  showScriptS {Γ} [] =
    return ([] , id)
  showScriptS (cmd ∷ scr) = do
    (cmd , p₁) ← showCommandS cmd
    (scr , δp) ← showScriptS scr
    return (cmd ∷ scr , λ p₂ → δp (p₁ <||> extendEP _ p₂))


  -- |A name state for the empty context, which supplies the names x0, x1, x2, ...
  x′es : Names []
  nameEnv    x′es = []
  nameSupply x′es = Stream.map (λ n → 'x' ∷ String.toList (showℕ n)) (Stream.iterate ℕ.suc 0)


  -- |Show a term as an S-expression.
  showTerm : Names Γ → Term Γ σ → String
  showTerm names x = proj₁ (proj₁ (showTermS x names))


  -- |Show a command as an S-expression.
  showCommand : Names Γ → Command Γ Ξ δΓ δΞ → String
  showCommand names cmd = proj₁ (proj₁ (showCommandS cmd names))


  -- |Show a script as an S-expression.
  showScript : Script [] Γ Ξ → String × EnvParser Γ
  showScript scr = Prod.map String.unlines (_$ []) (proj₁ (showScriptS scr x′es))


  -- |Parse a satisfiability result.
  parseSat : ∀[ Parser Sat ]
  parseSat = withSpaces (pSat <|> pUnsat <|> pUnknown)
    where
      pSat     = sat     <$ text "sat"
      pUnsat   = unsat   <$ text "unsat"
      pUnknown = unknown <$ text "unknown"


  _ : parseSat parses "sat" as (_≟-Sat sat)
  _ = _

  _ : parseSat parses "unsat" as (_≟-Sat unsat)
  _ = _

  _ : parseSat parses "unknown" as (_≟-Sat unknown)
  _ = _

  _ : parseSat rejects "dogfood"
  _ = _


  -- |Parse a result.
  parseResult : (ξ : OutputType) → ∀[ Parser (Result ξ) ]
  parseResult SAT       = parseSat
  parseResult (MODEL Γ) = notYetImplemented
    where
      postulate
        notYetImplemented : ∀[ Parser (Result (MODEL Γ))]

  -- |Parse a list of results.
  parseResults : (ξ : OutputType) (Ξ : OutputCtxt) → ∀[ Parser (Results (ξ ∷ Ξ)) ]
  parseResults ξ [] = (_∷ []) <$> parseResult ξ
  parseResults ξ (ξ′ ∷ Ξ) = _∷_ <$> parseResult ξ <*> box (parseResults ξ′ Ξ)


  -- |Quote a satisfiability result.
  quoteSat : Sat → Reflection.Term
  quoteSat sat     = con (quote sat) []
  quoteSat unsat   = con (quote unsat) []
  quoteSat unknown = con (quote unknown) []

  -- |Quote a result.
  quoteResult : Result ξ → Reflection.Term
  quoteResult {SAT}     r = quoteSat r
  quoteResult {MODEL Γ} r = notYetImplemented r
    where
      postulate
        notYetImplemented : Result (MODEL Γ) → Reflection.Term

  -- |Quote a list of results.
  quoteResults : Results Ξ → Reflection.Term
  quoteResults [] = con (quote Results.[]) []
  quoteResults (r ∷ rs) = con (quote Results._∷_) $ vArg (quoteResult r) ∷ vArg (quoteResults rs) ∷ []

-- -}
-- -}
-- -}
-- -}
-- -}
