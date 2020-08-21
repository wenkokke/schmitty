{-# OPTIONS --without-K --safe #-}

module SMT.Theories.Core where

open import Data.Bool.Base as Bool using (Bool; false; true)
open import Data.List.Base as List using (List; _∷_; [])
open import Data.String.Base as String using (String)
open import Function using (id)
open import SMT.Theory

data CoreSort : Set where
  BOOL : CoreSort

data CoreLiteral : CoreSort → Set where
  bool : Bool → CoreLiteral BOOL

data CoreIdentifier : {σ : CoreSort} (Σ : Signature σ) → Set where
  not     : CoreIdentifier (Op₁ BOOL)
  implies : CoreIdentifier (Op₂ BOOL)
  and     : CoreIdentifier (Op₂ BOOL)
  or      : CoreIdentifier (Op₂ BOOL)
  xor     : CoreIdentifier (Op₂ BOOL)

coreTheory : Theory _ _ _
Theory.Sort       coreTheory = CoreSort
Theory.BOOL       coreTheory = BOOL
Theory.Literal    coreTheory = CoreLiteral
Theory.Identifier coreTheory = CoreIdentifier

showCoreSort : CoreSort → String
showCoreSort BOOL = "Bool"

showCoreLiteral : {σ : CoreSort} → CoreLiteral σ → String
showCoreLiteral (bool false) = "false"
showCoreLiteral (bool true)  = "true"

showCoreIdentifier : {σ : CoreSort} {Σ : Signature σ} → CoreIdentifier Σ → String
showCoreIdentifier not     = "not"
showCoreIdentifier implies = "=>"
showCoreIdentifier and     = "and"
showCoreIdentifier or      = "or"
showCoreIdentifier xor     = "xor"

corePrintable : Printable coreTheory
Printable.showSort       corePrintable = showCoreSort
Printable.showLiteral    corePrintable = showCoreLiteral
Printable.showIdentifier corePrintable = showCoreIdentifier
