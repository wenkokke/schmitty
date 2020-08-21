{-# OPTIONS --without-K #-}

module SMT.Logics.Properties.Unsafe where

open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Equivalence using (equivalence)
open import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Sum using (_⊎-dec_)
open import SMT.Logics
open import SMT.Logics.Properties

infix 4 _⇾⁺?_

-- |Decision procedure for the transitive closure of the ⇾-relation.
--
--  NOTE: Walks down all possible paths in the graph from l₁ and checks
--        if it encounters l₃ at any point. May traverse certain nodes
--        multiple times. I've marked this function as TERMINATING, since
--        each step is guarded by a step along the ⇾-relation, and we've
--        already shown that ⇾ and ⇾⁺ are well-founded.
--
{-# TERMINATING #-}
_⇾⁺?_ : (l₁ l₃ : Logic) → Dec (l₁ ⇾⁺ l₃)
l₁ ⇾⁺? l₃ with l₁ ⇾? l₃
l₁ ⇾⁺? l₃ | yes l₁⇾l₃ = yes [ l₁⇾l₃ ]

QF-AX     ⇾⁺? l₃ | no ¬l₁⇾l₃
  = no λ { [ () ] ; (() ∷ _) }

QF-IDL    ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence to from) (QF-LIA ⇾⁺? l₃ ⊎-dec QF-UFIDL ⇾⁺? l₃)
  where
    to = [ QF-IDL⇾QF-LIA ∷_ , QF-IDL⇾QF-UFIDL ∷_ ]′
    from : (QF-IDL ⇾⁺ l₃) → (QF-LIA ⇾⁺ l₃ ⊎ QF-UFIDL ⇾⁺ l₃)
    from [ p ] = ⊥-elim (¬l₁⇾l₃ p)
    from (QF-IDL⇾QF-LIA   ∷ p) = inj₁ p
    from (QF-IDL⇾QF-UFIDL ∷ p) = inj₂ p

QF-LIA ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence to from) (QF-NIA ⇾⁺? l₃ ⊎-dec LIA ⇾⁺? l₃ ⊎-dec QF-ALIA ⇾⁺? l₃ ⊎-dec QF-UFLIA ⇾⁺? l₃)
  where
    to = [ QF-LIA⇾QF-NIA ∷_ , [ QF-LIA⇾LIA ∷_ , [ QF-LIA⇾QF-ALIA ∷_ , QF-LIA⇾QF-UFLIA ∷_ ]′ ]′ ]′
    from : (QF-LIA ⇾⁺ l₃) → (QF-NIA ⇾⁺ l₃ ⊎ LIA ⇾⁺ l₃ ⊎ QF-ALIA ⇾⁺ l₃ ⊎ QF-UFLIA ⇾⁺ l₃)
    from [ p ] = ⊥-elim (¬l₁⇾l₃ p)
    from (QF-LIA⇾QF-NIA   ∷ p) = inj₁ p
    from (QF-LIA⇾LIA      ∷ p) = inj₂ (inj₁ p)
    from (QF-LIA⇾QF-ALIA  ∷ p) = inj₂ (inj₂ (inj₁ p))
    from (QF-LIA⇾QF-UFLIA ∷ p) = inj₂ (inj₂ (inj₂ p))

QF-NIA    ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence
            (QF-NIA⇾NIA ∷_)
            (λ { [ l₁⇾l₃ ] → ⊥-elim (¬l₁⇾l₃ l₁⇾l₃) ; (QF-NIA⇾NIA ∷ p) → p}))
            (NIA ⇾⁺? l₃)

NIA       ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence
            (NIA⇾UFNIA ∷_)
            (λ { [ l₁⇾l₃ ] → ⊥-elim (¬l₁⇾l₃ l₁⇾l₃) ; (NIA⇾UFNIA ∷ p) → p}))
            (UFNIA ⇾⁺? l₃)

UFNIA     ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence
            (UFNIA⇾AUFNIRA ∷_)
            (λ { [ l₁⇾l₃ ] → ⊥-elim (¬l₁⇾l₃ l₁⇾l₃) ; (UFNIA⇾AUFNIRA ∷ p) → p}))
            (AUFNIRA ⇾⁺? l₃)

AUFNIRA   ⇾⁺? l₃ | no ¬l₁⇾l₃
  = no λ { [ () ] ; (() ∷ _) }

LIA       ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence to from) (NIA ⇾⁺? l₃ ⊎-dec AUFLIRA ⇾⁺? l₃ ⊎-dec ALIA ⇾⁺? l₃)
  where
    to = [ LIA⇾NIA ∷_ , [ LIA⇾AUFLIRA ∷_ , LIA⇾ALIA ∷_ ]′ ]′
    from : (LIA ⇾⁺ l₃) → (NIA ⇾⁺ l₃ ⊎ AUFLIRA ⇾⁺ l₃ ⊎ ALIA ⇾⁺ l₃)
    from [ l₁⇾l₃ ] = ⊥-elim (¬l₁⇾l₃ l₁⇾l₃ )
    from (LIA⇾NIA     ∷ p) = inj₁ p
    from (LIA⇾AUFLIRA ∷ p) = inj₂ (inj₁ p)
    from (LIA⇾ALIA    ∷ p) = inj₂ (inj₂ p)

AUFLIRA   ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence
            (AUFLIRA⇾AUFNIRA ∷_)
            (λ { [ l₁⇾l₃ ] → ⊥-elim (¬l₁⇾l₃ l₁⇾l₃) ; (AUFLIRA⇾AUFNIRA ∷ p) → p}))
            (AUFNIRA ⇾⁺? l₃)

ALIA      ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence
            (ALIA⇾AUFLIA ∷_)
            (λ { [ l₁⇾l₃ ] → ⊥-elim (¬l₁⇾l₃ l₁⇾l₃) ; (ALIA⇾AUFLIA ∷ p) → p}))
            (AUFLIA ⇾⁺? l₃)

AUFLIA    ⇾⁺? l₃ | no ¬l₁⇾l₃
  = no λ { [ () ] ; (() ∷ _) }

QF-ALIA   ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence to from) (ALIA ⇾⁺? l₃ ⊎-dec QF-AUFLIA ⇾⁺? l₃)
  where
    to = [ QF-ALIA⇾ALIA ∷_ , QF-ALIA⇾QF-AUFLIA ∷_ ]′
    from : (QF-ALIA ⇾⁺ l₃) → (ALIA ⇾⁺ l₃ ⊎ QF-AUFLIA ⇾⁺ l₃)
    from [ l₁⇾l₃ ] = ⊥-elim (¬l₁⇾l₃ l₁⇾l₃)
    from (QF-ALIA⇾ALIA      ∷ p) = inj₁ p
    from (QF-ALIA⇾QF-AUFLIA ∷ p) = inj₂ p

QF-AUFLIA ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence
            (QF-AUFLIA⇾AUFLIA ∷_)
            (λ { [ l₁⇾l₃ ] → ⊥-elim (¬l₁⇾l₃ l₁⇾l₃) ; (QF-AUFLIA⇾AUFLIA ∷ p) → p}))
            (AUFLIA ⇾⁺? l₃)

QF-UFIDL  ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence
            (QF-UFIDL⇾QF-UFLIA ∷_)
            (λ { [ l₁⇾l₃ ] → ⊥-elim (¬l₁⇾l₃ l₁⇾l₃) ; (QF-UFIDL⇾QF-UFLIA ∷ p) → p}))
            (QF-UFLIA ⇾⁺? l₃)

QF-UFLIA  ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence to from) (QF-AUFLIA ⇾⁺? l₃ ⊎-dec QF-UFNIA ⇾⁺? l₃)
  where
    to = [ QF-UFLIA⇾QF-AUFLIA ∷_ , QF-UFLIA⇾QF-UFNIA ∷_ ]′
    from : (QF-UFLIA ⇾⁺ l₃) → (QF-AUFLIA ⇾⁺ l₃ ⊎ QF-UFNIA ⇾⁺ l₃)
    from [ l₁⇾l₃ ] = ⊥-elim (¬l₁⇾l₃ l₁⇾l₃)
    from (QF-UFLIA⇾QF-AUFLIA ∷ p) = inj₁ p
    from (QF-UFLIA⇾QF-UFNIA  ∷ p) = inj₂ p

QF-UFNIA  ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence
            (QF-UFNIA⇾UFNIA ∷_)
            (λ { [ l₁⇾l₃ ] → ⊥-elim (¬l₁⇾l₃ l₁⇾l₃) ; (QF-UFNIA⇾UFNIA ∷ p) → p}))
            (UFNIA ⇾⁺? l₃)

QF-UF     ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence to from) (QF-UFIDL ⇾⁺? l₃ ⊎-dec QF-UFLRA ⇾⁺? l₃ ⊎-dec QF-UFBV ⇾⁺? l₃)
  where
    to = [ QF-UF⇾QF-UFIDL ∷_ , [ QF-UF⇾QF-UFLRA ∷_ , QF-UF⇾QF-UFBV ∷_ ]′ ]′
    from : (QF-UF ⇾⁺ l₃) → (QF-UFIDL ⇾⁺ l₃ ⊎ QF-UFLRA ⇾⁺ l₃ ⊎ QF-UFBV ⇾⁺ l₃)
    from [ l₁⇾l₃ ] = ⊥-elim (¬l₁⇾l₃ l₁⇾l₃ )
    from (QF-UF⇾QF-UFIDL ∷ p) = inj₁ p
    from (QF-UF⇾QF-UFLRA ∷ p) = inj₂ (inj₁ p)
    from (QF-UF⇾QF-UFBV  ∷ p) = inj₂ (inj₂ p)

QF-UFLRA  ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence to from) (UFLRA ⇾⁺? l₃ ⊎-dec QF-UFNRA ⇾⁺? l₃)
  where
    to = [ QF-UFLRA⇾UFLRA ∷_ , QF-UFLRA⇾QF-UFNRA ∷_ ]′
    from : (QF-UFLRA ⇾⁺ l₃) → (UFLRA ⇾⁺ l₃ ⊎ QF-UFNRA ⇾⁺ l₃)
    from [ l₁⇾l₃ ] = ⊥-elim (¬l₁⇾l₃ l₁⇾l₃)
    from (QF-UFLRA⇾UFLRA ∷ p) = inj₁ p
    from (QF-UFLRA⇾QF-UFNRA  ∷ p) = inj₂ p

UFLRA     ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence
            (UFLRA⇾AUFLIRA ∷_)
            (λ { [ l₁⇾l₃ ] → ⊥-elim (¬l₁⇾l₃ l₁⇾l₃) ; (UFLRA⇾AUFLIRA ∷ p) → p}))
            (AUFLIRA ⇾⁺? l₃)

QF-UFNRA  ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence
            (QF-UFNRA⇾AUFNIRA ∷_)
            (λ { [ l₁⇾l₃ ] → ⊥-elim (¬l₁⇾l₃ l₁⇾l₃) ; (QF-UFNRA⇾AUFNIRA ∷ p) → p}))
            (AUFNIRA ⇾⁺? l₃)

QF-UFBV   ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence
            (QF-UFBV⇾QF-AUFBV ∷_)
            (λ { [ l₁⇾l₃ ] → ⊥-elim (¬l₁⇾l₃ l₁⇾l₃) ; (QF-UFBV⇾QF-AUFBV ∷ p) → p}))
            (QF-AUFBV ⇾⁺? l₃)

QF-AUFBV  ⇾⁺? l₃ | no ¬l₁⇾l₃
  = no λ { [ () ] ; (() ∷ _) }

QF-BV     ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence to from) (QF-UFBV ⇾⁺? l₃ ⊎-dec QF-ABV ⇾⁺? l₃)
  where
    to = [ QF-BV⇾QF-UFBV ∷_ , QF-BV⇾QF-ABV ∷_ ]′
    from : (QF-BV ⇾⁺ l₃) → (QF-UFBV ⇾⁺ l₃ ⊎ QF-ABV ⇾⁺ l₃)
    from [ l₁⇾l₃ ] = ⊥-elim (¬l₁⇾l₃ l₁⇾l₃)
    from (QF-BV⇾QF-UFBV ∷ p) = inj₁ p
    from (QF-BV⇾QF-ABV  ∷ p) = inj₂ p

QF-ABV    ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence
            (QF-ABV⇾QF-AUFBV ∷_)
            (λ { [ l₁⇾l₃ ] → ⊥-elim (¬l₁⇾l₃ l₁⇾l₃) ; (QF-ABV⇾QF-AUFBV ∷ p) → p}))
            (QF-AUFBV ⇾⁺? l₃)

QF-RDL    ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence
            (QF-RDL⇾QF-LRA ∷_)
            (λ { [ l₁⇾l₃ ] → ⊥-elim (¬l₁⇾l₃ l₁⇾l₃) ; (QF-RDL⇾QF-LRA ∷ p) → p}))
            (QF-LRA ⇾⁺? l₃)

QF-LRA    ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence to from) (QF-UFNRA ⇾⁺? l₃ ⊎-dec LRA ⇾⁺? l₃ ⊎-dec QF-NRA ⇾⁺? l₃)
  where
    to = [ QF-LRA⇾QF-UFNRA ∷_ , [ QF-LRA⇾LRA ∷_ , QF-LRA⇾QF-NRA ∷_ ]′ ]′
    from : (QF-LRA ⇾⁺ l₃) → (QF-UFNRA ⇾⁺ l₃ ⊎ LRA ⇾⁺ l₃ ⊎ QF-NRA ⇾⁺ l₃)
    from [ l₁⇾l₃ ] = ⊥-elim (¬l₁⇾l₃ l₁⇾l₃ )
    from (QF-LRA⇾QF-UFNRA ∷ p) = inj₁ p
    from (QF-LRA⇾LRA      ∷ p) = inj₂ (inj₁ p)
    from (QF-LRA⇾QF-NRA   ∷ p) = inj₂ (inj₂ p)

NRA       ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence
            (NRA⇾AUFNIRA ∷_)
            (λ { [ l₁⇾l₃ ] → ⊥-elim (¬l₁⇾l₃ l₁⇾l₃) ; (NRA⇾AUFNIRA ∷ p) → p}))
            (AUFNIRA ⇾⁺? l₃)

LRA       ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence to from) (UFLRA ⇾⁺? l₃ ⊎-dec NRA ⇾⁺? l₃)
  where
    to = [ LRA⇾UFLRA ∷_ , LRA⇾NRA ∷_ ]′
    from : (LRA ⇾⁺ l₃) → (UFLRA ⇾⁺ l₃ ⊎ NRA ⇾⁺ l₃)
    from [ l₁⇾l₃ ] = ⊥-elim (¬l₁⇾l₃ l₁⇾l₃)
    from (LRA⇾UFLRA ∷ p) = inj₁ p
    from (LRA⇾NRA   ∷ p) = inj₂ p

QF-NRA    ⇾⁺? l₃ | no ¬l₁⇾l₃
  = Dec.map (equivalence to from) (QF-UFNRA ⇾⁺? l₃ ⊎-dec NRA ⇾⁺? l₃)
  where
    to = [ QF-NRA⇾QF-UFNRA ∷_ , QF-NRA⇾NRA ∷_ ]′
    from : (QF-NRA ⇾⁺ l₃) → (QF-UFNRA ⇾⁺ l₃ ⊎ NRA ⇾⁺ l₃)
    from [ l₁⇾l₃ ] = ⊥-elim (¬l₁⇾l₃ l₁⇾l₃)
    from (QF-NRA⇾QF-UFNRA ∷ p) = inj₁ p
    from (QF-NRA⇾NRA      ∷ p) = inj₂ p
