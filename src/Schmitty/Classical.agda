{-# OPTIONS --safe --without-K #-}

module Schmitty.Classical where

open import Level using (Level)
open import Category.Functor using (RawFunctor)
open import Category.Applicative using (RawApplicative)
open import Category.Monad using (RawMonad)
open import Function using (_∘_)
open import Relation.Nullary using (¬_)

private
  variable
    ℓ   : Level
    a b : Level
    A   : Set a
    B   : Set b

record Classical (A : Set a) : Set a where
  constructor classical
  field
    runClassical : ¬ (¬ A)

open Classical public

functor : RawFunctor {ℓ} Classical
functor = record { _<$>_ = _<$>_ }
  where
    _<$>_ : (A → B) → Classical A → Classical B
    runClassical (A→B <$> classical ¬¬A) ¬B =
      ¬¬A (λ A → ¬B (A→B A))

applicative : RawApplicative {ℓ} Classical
applicative = record { pure = pure; _⊛_ = _<*>_ }
  where
    pure : A → Classical A
    runClassical (pure A) ¬A = ¬A A

    _<*>_ : Classical (A → B) → Classical A → Classical B
    runClassical (classical ¬¬[A→B] <*> classical ¬¬A) ¬B =
      ¬¬[A→B] (λ A→B → ¬¬A (λ A → ¬B (A→B A)))

monad : RawMonad {ℓ} Classical
monad = record { return = RawApplicative.pure applicative; _>>=_ = _>>=_ }
  where
    _>>=_ : Classical A → (A → Classical B) → Classical B
    runClassical (classical ¬¬A >>= A→¬¬B) ¬B =
      ¬¬A (λ A → runClassical (A→¬¬B A) ¬B)
