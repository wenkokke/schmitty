module Text.Parser.String where

open import Data.Bool as Bool using (Bool; T; not; if_then_else_)
open import Data.Char as Char using (Char)
open import Data.Empty as Empty using (⊥)
open import Data.Integer as Int using (ℤ)
open import Data.List as List using (List; _∷_; [])
open import Data.List.NonEmpty as List⁺ using (List⁺)
import Data.List.Categorical as ListCat
open import Data.List.Sized.Interface
open import Data.Maybe as Maybe using (Maybe; just; nothing)
import Data.Maybe.Categorical as MaybeCat
open import Data.Nat as Nat using (ℕ)
import Data.Nat.Properties as Nat
open import Data.Product as Prod using (_×_; _,_)
open import Data.String as String using (String; _<+>_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Subset -- instances
open import Data.Unit as Unit using (⊤; tt)
open import Data.Vec as Vec using (Vec)
open import Function using (id; const; _∘_; _∘′_; _$_; case_of_)
open import Induction.Nat.Strong using (□_) public
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; ⌊_⌋)
open import Relation.Unary using (IUniversal; _⇒_) public -- imports ∀[_] syntax
open import Relation.Binary.PropositionalEquality.Decidable --instances

open import Data.Subset public

import Text.Parser.Monad as PM
import Text.Parser.Types as PI
import Text.Parser.Position as PP


data ParseErrorMsg : Set where
  no-parse        : ParseErrorMsg
  ambiguous-parse : ParseErrorMsg


private
  variable
    n : ℕ
    A B C : Set


private
  -- |The success type, specialised to strings.
  Success : (A : Set) (n : ℕ) → Set
  Success A n = PI.Success (Vec Char) A n

  -- |Check if a Success were, in fact, a success.
  runSuccess : Success A n → Maybe A
  runSuccess s =
    if ⌊ PI.Success.size s Nat.≟ 0 ⌋ then just (PI.Success.value s) else nothing


private
  -- |The result type, specialised to carry no error information or annotations.
  Result : (A : Set) → Set
  Result A = PM.Result ⊤ (A × PP.Position × List ⊥)

  -- |Discard errors, and return only the results.
  runResult : Result A → List A
  runResult = PM.result (const []) (const []) ((_∷ []) ∘ Prod.proj₁)

private
  fromSingleton : List A → ParseErrorMsg ⊎ A
  fromSingleton []          = inj₁ no-parse
  fromSingleton (v ∷ [])    = inj₂ v
  fromSingleton (_ ∷ _ ∷ _) = inj₁ ambiguous-parse


-- |The parser type, specialised to strings.
Parser : (A : Set) (n : ℕ) → Set
Parser = PI.Parser PM.Agdarsec′.chars

-- |Run a parser, and return a list of results.
runParser : ∀[ Parser A ] → String → ParseErrorMsg ⊎ A
runParser {A} p str

  -- Return the single parse, or an error:
  = fromSingleton

  -- Discard all "successful" parses which didn't consume all input:
  $ Maybe.maybe id [] ∘ mapM runSuccess

  -- Discard all errors, and return only the "successful" parses:
  $ runResult

  -- Run the parser:
  $ (λ input -> PI.runParser p (Nat.n≤1+n _) input (PP.start , []))

  -- Convert the input from a String to a length-indexed Vector:
  $ Vec.fromList (String.toList str)
  where
    -- Import mapM instance for List/Maybe
    mapM : ∀ {A B} → (A → Maybe B) → List A → Maybe (List B)
    mapM = ListCat.TraversableM.mapM MaybeCat.monad



---------------------------------------------------------------
-- Export the basic parser combinators with simplified types --
---------------------------------------------------------------

import Text.Parser.Combinators as PC
import Text.Parser.Combinators.Char as PCC
import Text.Parser.Combinators.Numbers as PCN


private
  instance
    Agdarsec′M  = PM.Agdarsec′.monad
    Agdarsec′M0 = PM.Agdarsec′.monadZero
    Agdarsec′M+ = PM.Agdarsec′.monadPlus


-- |Parser which...
guardM : (A → Maybe B) → ∀[ Parser A ⇒ Parser B ]
guardM = PC.guardM

-- |Parser which...
_>>=_ : ∀[ Parser A ⇒ (const A ⇒ □ Parser B) ⇒ Parser B ]
_>>=_ = PC._>>=_

infixl 4 _<&>_ _<&_ _&>_

-- |Parser which...
_<&>_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser (A × B) ]
_<&>_ = PC._<&>_

-- |Parser which...
_<&_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser A ]
_<&_ = PC._<&_

-- |Parser which...
_&>_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser B ]
_&>_ = PC._&>_

infixl 4 _<&?>_ _<&?_ _&?>_

-- |Parser which...
_<&?>_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser (A × Maybe B) ]
_<&?>_ = PC._<&?>_

-- |Parser which...
_<&?_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser A ]
_<&?_ = PC._<&?_

-- |Parser which...
_&?>_ : ∀[ Parser A ⇒ □ Parser B ⇒ Parser (Maybe B) ]
_&?>_ = PC._&?>_

infixl 4 _<?&>_ _<?&_ _?&>_

-- |Parser which...
_<?&>_ : ∀[ Parser A ⇒ Parser B ⇒ Parser (Maybe A × B) ]
_<?&>_ = PC._<?&>_

-- |Parser which...
_<?&_ : ∀[ Parser A ⇒ Parser B ⇒ Parser (Maybe A) ]
_<?&_ = PC._<?&_

-- |Parser which...
_?&>_ : ∀[ Parser A ⇒ Parser B ⇒ Parser B ]
_?&>_ = PC._?&>_

-- |Parser which...
box : ∀[ Parser A ⇒ □ Parser A ]
box = PC.box

-- |Parser which...
fail : ∀[ Parser A ]
fail = PC.fail

infixr 3 _<|>_

-- |Parser which...
_<|>_ : ∀[ Parser A ⇒ Parser A ⇒ Parser A ]
_<|>_ = PC._<|>_

infixr 5 _<$>_

-- |Parser which...
_<$>_ : (A → B) → ∀[ Parser A ⇒ Parser B ]
_<$>_ = PC._<$>_

infixr 5 _<$_

-- |Parser which...
_<$_ : B → ∀[ Parser A ⇒ Parser B ]
_<$_ = PC._<$_

infixl 4 _<*>_

-- |Parser which...
_<*>_ : ∀[ Parser (A → B) ⇒ □ Parser A ⇒ Parser B ]
_<*>_ = PC._<*>_

-- |Parser which...
alts : ∀[ List ∘′ Parser A ⇒ Parser A ]
alts = PC.alts

-- |Parser which...
ands : ∀[ List⁺ ∘′ Parser A ⇒ Parser (List⁺ A) ]
ands = PC.ands

-- |Parser which...
list⁺ : ∀[ Parser A ⇒ Parser (List⁺ A) ]
list⁺ = PC.list⁺

-- |Parser which...
char : Char → ∀[ Parser Char ]
char = PCC.char

-- |Parser which...
anyCharBut : Char → ∀[ Parser Char ]
anyCharBut = PCC.anyCharBut

-- |Parser which...
space : ∀[ Parser Char ]
space = PCC.space

-- |Parser which...
spaces : ∀[ Parser (List⁺ Char) ]
spaces = PCC.spaces

-- |Helper function which checks if a string is empty.
isEmpty : String → Bool
isEmpty = List.null ∘ String.toList

-- |Parser which...
text : (str : String) {p : T (not (isEmpty str))} → ∀[ Parser (List⁺ Char) ]
text = PCC.text

-- |Parser which...
withSpaces : ∀[ Parser A ⇒ Parser A ]
withSpaces = PCC.withSpaces

-- |Parser which...
lexeme : (str : String) {p : T (not (isEmpty str))} → ∀[ Parser (List⁺ Char) ]
lexeme str {p} = withSpaces (text str {p})

-- |Parser which...
exact : Char → ∀[ Parser Char ]
exact = PC.exact

-- |Parser which...
exacts : (str : List⁺ Char) → ∀[ Parser (List⁺ Char) ]
exacts = PC.exacts

-- |Parser which...
parens : ∀[ □ Parser A ⇒ Parser A ]
parens = PCC.parens

-- |Parser which...
lower : ∀[ Parser Char ]
lower = PCC.lowerAlpha

-- |Parser which...
upper : ∀[ Parser Char ]
upper = PCC.upperAlpha

-- |Parser which...
alpha : ∀[ Parser Char ]
alpha = PCC.alpha

-- |Parser which...
alphas⁺ : ∀[ Parser (List⁺ Char) ]
alphas⁺ = PCC.alphas⁺

-- |Parser which...
num : ∀[ Parser ℕ ]
num = PCC.num

-- |Parser which...
alphanum : ∀[ Parser (Char ⊎ ℕ) ]
alphanum = PCC.alphanum

-- |Parser which...
decimalDigit : ∀[ Parser ℕ ]
decimalDigit = PCN.decimalDigit

-- |Parser which...
decimalℕ : ∀[ Parser ℕ ]
decimalℕ = PCN.decimalℕ

-- |Parser which...
decimalℤ : ∀[ Parser ℤ ]
decimalℤ = PCN.decimalℤ


---------------------
-- Testing parsers --
---------------------


-- |Empty type which carries an error message.
data ParseError : ParseErrorMsg → Set where


infix 0 !_

-- |Singleton type to compare the test result.
data Singleton {A : Set} : (x : A) → Set where
  !_ : (x : A) → Singleton x


private
  testHelper : (p : ∀[ Parser A ]) (str : String) (f : ParseErrorMsg → Set) (t : A → Set) → Set
  testHelper p str f t = case runParser p str of Sum.[ f , t ]′

-- |Tests if the parser accepts a string.
--
--  The resulting value is passed to a continuation for further inspection,
--  for instance, to allow the user to compare it to the expected value.
_parses_ : (p : ∀[ Parser A ]) (str : String) → Set
p parses str = testHelper p str ParseError Singleton

-- |Example use of `_parses_as_`.
_ : decimalℕ parses "10"
_ = ! 10

-- |Tests if the parser accepts a string.
_accepts_ : (p : ∀[ Parser A ]) (str : String) → Set
p accepts str = testHelper p str (const ⊥) (const ⊤)

-- |Example use of `_accepts_`.
_ : decimalℤ accepts "-10"
_ = _

-- |Tests if the parser rejects a string.
_rejects_ : (p : ∀[ Parser A ]) (str : String) → Set
p rejects str = testHelper p str (const ⊤) (const ⊥)

-- |Example use of `_rejects_`.
_ : decimalℕ rejects "-10"
_ = _


