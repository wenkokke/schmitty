module Text.Parser.String where

open import Data.Bool.Base using (T; not)
open import Data.Char.Base using (Char)
open import Data.Empty using (⊥)
open import Data.List.Base using (null)
open import Data.List.NonEmpty using (List⁺)
open import Data.String.Base as String using (String)
import Data.Sum.Base as Sum
open import Data.Unit.Base using (⊤)
open import Function.Base using (case_of_; const)

open import Data.Singleton
  public
  renaming (_! to !_)
open import Text.Parser
  public

lexeme : (t : String) → {_ : T (not (null (String.toList t)))} →
         ∀[ Parser (List⁺ Char) ]
lexeme str {p} = withSpaces (text str {p})

---------------------
-- Testing parsers --
---------------------

-- Empty type for a better error message
data ParserErrorAt : Position → Set where

private
  variable
    A : Set

private
  testHelper : (p : ∀[ Parser A ]) (str : String) (f : Position → Set) (t : A → Set) → Set
  testHelper p str f t = case runParser p str of Sum.[ f , t ]′

-- |Tests if the parser accepts a string.
--
--  The resulting value is passed to a continuation for further inspection,
--  for instance, to allow the user to compare it to the expected value.
_parses_ : (p : ∀[ Parser A ]) (str : String) → Set
p parses str = testHelper p str ParserErrorAt Singleton

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
