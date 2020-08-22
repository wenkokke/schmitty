open import SMT.Theory

module SMT.Script {theory : Theory} (printable : Printable theory) (parsable : Parsable theory) where

open import Data.Fin as Fin using (Fin)
open import Data.List as List using (List; _∷_; []; _++_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Product as Prod using (∃; ∃-syntax; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Logics
open import Data.Environment as Env using (Env; _∷_; [])

open import Category.Monad
open import Category.Monad.State as StateCat using (RawIMonadState; IStateT)
open import Codata.Musical.Stream as Stream using (Stream)
open import Data.Char as Char using (Char)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product as Product using (_×_; _,_; -,_; proj₁; proj₂)
open import Data.String as String using (String)
open import Data.Unit as Unit using (⊤)
open import Data.Vec as Vec using (Vec)
open import Function using (const; id; _∘_; _$_)
import Function.Identity.Categorical as Identity
open import Text.Parser.String as P hiding (_>>=_)
open import Reflection using (con; vArg)

open import SMT.Script.Base theory
open import SMT.Script.Names theory

open Theory theory
open Printable printable
open Parsable parsable

private
  variable
    σ σ′    : Sort
    Γ Γ′ δΓ : Ctxt
    Δ Δ′    : Ctxt
    Σ       : Signature σ
    Σ′      : Signature σ′
    ξ ξ′    : OutputType
    Ξ Ξ′ δΞ : OutputCtxt


-- |Create an S-expression from a list of strings.
--
-- @
--   mkSTerm ("*" ∷ "4" ∷ "5") ≡ "(* 4 5)"
-- @
--
mkSTerm : List String → String
mkSTerm = String.parens ∘ String.unwords


-- * Variable parsers

-- |Environment of variable parsers.
VarParsers : Ctxt → Set
VarParsers = Env (λ σ Γ → ∀[ Parser ((σ ∷ Γ) ∋ σ) ])

-- |Construct a single variable parser from an environment of variable parsers.
mkVarParser : VarParsers Γ → ∀[ Parser (∃[ σ ] (Γ ∋ σ)) ]
mkVarParser []            = fail
mkVarParser (p ∷ env) {x} = (-,_ <$> p {x}) <|> (Prod.map id extendVar <$> mkVarParser env {x})


-- * Output parsers

-- |Mapping from output types to parser types.
OutputParser : OutputType → Set
OutputParser ξ = ∀[ Parser (Output ξ) ]

-- |Mapping from output contexts to parser types.
OutputParsers : OutputCtxt → Set
OutputParsers Ξ = Env (λ ξ _Ξ → OutputParser ξ) Ξ

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


-- Connect the output of showScript, via parseVarAssign, to parse models.
parseModel : VarParsers Γ → ∀[ Parser (Model Γ) ]
parseModel {Γ} vps =
  guardM checkModel ((unsafeBuildModel ∘ List⁺.toList) <$> parseVarAssigns)
  where
    parseVarName : ∀[ Parser (∃[ σ ] (Γ ∋ σ)) ]
    parseVarName = withSpaces (mkVarParser {Γ} vps)

    -- |Parse a variable assignment.
    parseVarAssign : ∀[ Parser (∃[ σ ] (Γ ∋ σ × Value σ)) ]
    parseVarAssign = parens (box (guardM checkVarAssign unsafeParseVarAssign))
      where
      -- Parse a pair of a sort and a value of that sort.
      parseSortValue : ∀[ Parser (∃[ σ ] (Value σ)) ]
      parseSortValue = readSort P.>>= λ σ → box (-,_ <$> readValue σ)

      -- Parse a variable assignment, with possibly distinct sorts.
      unsafeParseVarAssign : ∀[ Parser (∃[ σ ] (Γ ∋ σ) × ∃[ σ ] (Value σ)) ]
      unsafeParseVarAssign =
        text "define-fun" &> box (parseVarName <&> box (text "()" &> box parseSortValue))

      -- Check if the expect and actual sorts correspond.
      checkVarAssign : ∃[ σ ] (Γ ∋ σ) × ∃[ σ ] (Value σ) → Maybe (∃[ σ ] (Γ ∋ σ × Value σ))
      checkVarAssign ((σ₁ , x) , (σ₂ , v)) with σ₁ ≟-Sort σ₂
      ... | yes refl = just (σ₂ , x , v)
      ... | no  _    = nothing

    -- Parse a series of variable assigments.
    parseVarAssigns : ∀[ Parser (List⁺ (∃[ σ ] (Γ ∋ σ × Value σ))) ]
    parseVarAssigns = list⁺ parseVarAssign

    -- Insert a variable assignment into an unchecked model.
    unsafeInsertModel :
      ∀ {Γ} → ∃[ σ ] (Γ ∋ σ × Value σ) → Env (λ σ _Γ → List (Value σ)) Γ → Env (λ σ _Γ → List (Value σ)) Γ
    unsafeInsertModel {.σ ∷ Γ} (σ , (Fin.zero  , refl) , v) (vs ∷ env) = (v ∷ vs) ∷ env
    unsafeInsertModel {σ′ ∷ Γ} (σ , (Fin.suc i , p)    , v) (vs ∷ env) =
      vs ∷ unsafeInsertModel (σ , (i , p) , v) env

    -- Build an unchecked model from a list of variable assignments.
    unsafeBuildModel : List (∃[ σ ] (Γ ∋ σ × Value σ)) → Env (λ σ _Γ → List (Value σ)) Γ
    unsafeBuildModel []       = Env.repeat (λ _σ _Γ → []) Γ
    unsafeBuildModel (v ∷ vs) = unsafeInsertModel v (unsafeBuildModel vs)

    -- Check if each variable has been assigned a value, is essentially traverse.
    checkModel : ∀ {Γ} → Env (λ σ _Γ → List (Value σ)) Γ → Maybe (Model Γ)
    checkModel [] = just []
    checkModel (vs ∷ env) = Maybe.zipWith _∷_ (only vs) (checkModel env)
      where
        only : {A : Set} → List A → Maybe A
        only [] = nothing
        only (v ∷ []) = just v
        only (_ ∷ _ ∷ _) = nothing

mkOutputParsers⁺ : OutputParsers (ξ ∷ Ξ) → ∀[ Parser (Outputs (ξ ∷ Ξ)) ]
mkOutputParsers⁺ (op ∷ [])          = (_∷ []) <$> op
mkOutputParsers⁺ (op ∷ ops@(_ ∷ _)) = _∷_ <$> op <*> box (mkOutputParsers⁺ ops)

mkOutputParsers : OutputParsers Ξ → ∀[ Parser (Outputs Ξ) ]
mkOutputParsers [] = [] <$ spaces
mkOutputParsers ops@(_ ∷ _) = mkOutputParsers⁺ ops


-- * Name state monad

NameState : (Γ Γ′ : Ctxt) → Set → Set
NameState Γ Γ′ A = IStateT (λ Γ → Names Γ × VarParsers Γ) id Γ Γ′ A

-- When showing terms, we need to pass around a name state,
-- for which we'll use an indexed monad, indexed by the context,
-- so we bring the functions from the indexed monad in scope.
private
  monadStateNameState =
    StateCat.StateTIMonadState (λ Γ → Names Γ × VarParsers Γ) Identity.monad

open RawIMonadState monadStateNameState
  using (return; _>>=_; _>>_; put; get; modify)

freshNameS : (σ : Sort) → NameState Γ (σ ∷ Γ) Name
freshNameS σ = do
  (ns , vps) ← get
  let (n , ns) = freshName σ ns
  let vps = ((Fin.zero , refl) <$ exacts n) ∷ vps
  put (ns , vps)
  return n

dropNameS : NameState (σ ∷ Γ) Γ ⊤
dropNameS = do
  (ns , _ ∷ vps) ← get
  put (dropName ns , vps)
  return _

lookupNameS : (i : Γ ∋ σ) → NameState Γ Γ Name
lookupNameS (i , _p) = do
  (ns , _vps) ← get
  return $ Env.lookup (Names.nameEnv ns) i


-- * Printing functions

mutual

  -- |Show a term as an S-expression.
  showTermS : Term Γ σ → NameState Γ Γ String
  showTermS (var i) = do
    n ← lookupNameS i
    return $ showName n
  showTermS (lit l) = do
    return $ showLiteral l
  showTermS (app x xs) = do
    let x = showIdentifier x
    xs ← showArgsS xs
    return $ mkSTerm (x ∷ xs)
  showTermS (forAll σ x) = do
    n ← freshNameS σ
    x ← showTermS x
    dropNameS
    return $ mkSTerm ("forall" ∷ mkSTerm (showName n ∷ showSort σ ∷ []) ∷ x ∷ [])
  showTermS (exists σ x) = do
    n ← freshNameS σ
    x ← showTermS x
    dropNameS
    return $ mkSTerm ("exists" ∷ mkSTerm (showName n ∷ showSort σ ∷ []) ∷ x ∷ [])

  showArgsS : Args Γ Δ → NameState Γ Γ (List String)
  showArgsS []       = return []
  showArgsS (x ∷ xs) = do x ← showTermS x; xs ← showArgsS xs; return (x ∷ xs)


-- |Show a command as an S-expression, and build up an environment of output parsers.
showCommandS : Command Γ Ξ δΓ δΞ → NameState Γ (δΓ ++ Γ) (String × OutputParsers δΞ)
showCommandS (set-logic l) = do
  return $ mkSTerm ("set-logic" ∷ showLogic l ∷ []) , []
showCommandS (declare-const σ) = do
  n ← freshNameS σ
  return $ mkSTerm ("declare-const" ∷ showName n ∷ showSort σ ∷ []) , []
showCommandS (assert x) = do
  x ← showTermS x
  return $ mkSTerm ("assert" ∷ x ∷ []) , []
showCommandS check-sat = do
  return $ mkSTerm ("check-sat" ∷ []) , parseSat ∷ []
showCommandS get-model = do
  (_ns , vps) ← get
  return $ mkSTerm ("get-model" ∷ []) , parseModel vps ∷ []

-- |Show a script as an S-expression, and build up an environment of output parsers.
showScriptS : Script Γ Γ′ Ξ → NameState Γ Γ′ (List String × OutputParsers Ξ)
showScriptS [] = do
  return $ [] , []
showScriptS (cmd ∷ scr) = do
  (cmd , ops₁) ← showCommandS cmd
  (scr , ops₂) ← showScriptS scr
  return $ cmd ∷ scr , Env.append id ops₁ ops₂

-- |Show a script as an S-expression, and return an environment of output parsers.
showScript : Script [] Γ Ξ → String × ∀[ Parser (Outputs Ξ) ]
showScript scr = Prod.map String.unlines mkOutputParsers (proj₁ (showScriptS scr (x′es , [])))

-- -}
-- -}
-- -}
