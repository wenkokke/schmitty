module SMT.Backend.Base where

open import Data.List as List using (List; _∷_; [])
open import Data.String as String using (String)
import Reflection as Rfl

postulate
  because : (solver : String) (A : Set) → A

`because : (solver : String) (A : Rfl.Type) → Rfl.Term
`because solver A = Rfl.def (quote because) (Rfl.vArg (Rfl.lit (Rfl.string solver)) ∷ Rfl.vArg A ∷ [])
