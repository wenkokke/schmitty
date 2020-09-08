module SMT.Utils.Float where

open import Category.Monad
open import Data.Bool as Bool using (Bool; false; true; T; not; _∧_; if_then_else_)
open import Data.Char as Char using (Char)
open import Data.Float as Float using (Float; isNaN; _≤ᵇ_; _<ᵇ_)
open import Data.Integer as Int using (ℤ; _◃_; +_; -[1+_])
open import Data.List as List using (List; []; _∷_; _∷ʳ′_; initLast; _∷ʳ_; _++_; splitAt; replicate)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
import Data.Maybe.Categorical as MaybeCat
open import Data.Nat as Nat using (ℕ; suc; zero; _*_; _+_; _∸_)
open import Data.Product as Prod using (_×_; _,_)
import Data.Sign as Sign
open import Data.String as String using (String)
open import Function using (_$_; case_of_; _∘_; flip)
import Level
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

IsNaN : Float → Set
IsNaN x = T (isNaN x)

_≤_ : Rel Float _
x ≤ y = ¬ (IsNaN x) × ¬ (IsNaN x) × T (x ≤ᵇ y)

_<_ : Rel Float _
x < y = ¬ (IsNaN x) × ¬ (IsNaN x) × T (x <ᵇ y)

_≥_ : Rel Float _
_≥_ = flip _≤_

_>_ : Rel Float _
_>_ = flip _<_

module _ where

  open RawMonad (MaybeCat.monad {Level.zero}) renaming (_⊛_ to _<*>_)

  parseNat : List Char → Maybe ℕ
  parseNat = parseNat′ 0
    where
      parseNat′ : ℕ → List Char → Maybe ℕ
      parseNat′ n []         = just n
      parseNat′ n ('0' ∷ cs) = parseNat′ (10 * n + 0) cs
      parseNat′ n ('1' ∷ cs) = parseNat′ (10 * n + 1) cs
      parseNat′ n ('2' ∷ cs) = parseNat′ (10 * n + 2) cs
      parseNat′ n ('3' ∷ cs) = parseNat′ (10 * n + 3) cs
      parseNat′ n ('4' ∷ cs) = parseNat′ (10 * n + 4) cs
      parseNat′ n ('5' ∷ cs) = parseNat′ (10 * n + 5) cs
      parseNat′ n ('6' ∷ cs) = parseNat′ (10 * n + 6) cs
      parseNat′ n ('7' ∷ cs) = parseNat′ (10 * n + 7) cs
      parseNat′ n ('8' ∷ cs) = parseNat′ (10 * n + 8) cs
      parseNat′ n ('9' ∷ cs) = parseNat′ (10 * n + 9) cs
      parseNat′ n ( _  ∷ cs) = nothing

  parseInt : List Char → Maybe ℤ
  parseInt ('-' ∷ cs) = ⦇ (Sign.- ◃_) (parseNat cs) ⦈
  parseInt        cs  = ⦇ (Sign.+ ◃_) (parseNat cs) ⦈

  parseFloat : List Char → Maybe (List Char × List Char × ℤ)
  parseFloat = parseFloat′ WholeNum
    where
      data Q : Set where WholeNum Fraction Exponent : Q

      parseFloat′ : Q → List Char → Maybe (List Char × List Char × ℤ)
      parseFloat′ _        []         = return $ [] , [] , + 0
      parseFloat′ WholeNum ('.' ∷ cs) = parseFloat′ Fraction cs
      parseFloat′ WholeNum ( c  ∷ cs) = do x , y , z ← parseFloat′ WholeNum cs; return $ c ∷ x , y , z
      parseFloat′ Fraction ('e' ∷ cs) = parseFloat′ Exponent cs
      parseFloat′ Fraction ( c  ∷ cs) = do x , y , z ← parseFloat′ Fraction cs; return $ x , c ∷ y , z
      parseFloat′ Exponent        cs  = do z ← parseInt cs; return $ [] , [] , z

  -- TODO: does not deal with negative numbers
  showPosFloat : Float → String
  showPosFloat x = case parseFloat (String.toList (Float.show x)) of λ where
                nothing                   → "impossible"
                (just (n , f ,    + e  )) → moveDotRight e n f
                (just (n , f , -[1+ e ])) → moveDotLeft (suc e) n f
    where
      mkString : (wholeNum fraction : List Char) → String
      mkString n  [] = String.fromList $  n ++ '.' ∷ '0' ∷ []
      mkString [] f  = String.fromList $ '0' ∷ '.' ∷  f
      mkString n  f  = String.fromList $  n ++ '.' ∷  f

      moveDotRight : (exponent : ℕ) (wholeNum fraction : List Char) → String
      moveDotRight zero    n f       = mkString n f
      moveDotRight e       n []      = mkString (n ++ replicate e '0') []
      moveDotRight (suc e) n (c ∷ f) = moveDotRight e (n ∷ʳ c) f

      moveDotLeft : (exponent : ℕ) (wholeNum fraction : List Char) → String
      moveDotLeft e n f with initLast n
      moveDotLeft zero     n        f | _        = mkString n f
      moveDotLeft e       .[]       f | []       = mkString [] (replicate e '0' ++ f)
      moveDotLeft (suc e) .(cs ∷ʳ c) f | cs ∷ʳ′ c = moveDotLeft e cs (c ∷ f)
