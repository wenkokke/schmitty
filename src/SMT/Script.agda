open import SMT.Theory

module SMT.Script (theory : Theory) where

open Theory theory
open import SMT.Script.Base baseTheory public
open import SMT.Script.Show theory public
open import SMT.Script.Reflection theory public
