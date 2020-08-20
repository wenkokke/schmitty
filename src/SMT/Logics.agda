module SMT.Logics where

open import Algebra
open import Algebra.Structures
open import Data.Nat as Nat using (ℕ)
import Data.Nat.Induction as WfNat
open import Data.List
open import Data.Product
open import Function using (_on_)
open import Induction.WellFounded
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary

-- |Logics supported by SMT-LIB.
--
--  Logics and descriptions taken from <http://smtlib.cs.uiowa.edu/logics.shtml>.
--  Order is a linearisation of <http://smtlib.cs.uiowa.edu/Logics/logics.png>.
--
data Logic : Set where

  QF-AX     : Logic
  -- ^ Closed quantifier-free formulas over the theory of arrays with
  --   extensionality.
  QF-IDL    : Logic
  -- ^ Difference Logic over the integers. In essence, Boolean combinations of
  --   inequations of the form x - y < b where x and y are integer variables and
  --   b is an integer constant.
  QF-LIA    : Logic
  -- ^ Unquantified linear integer arithmetic. In essence, Boolean combinations
  --   of inequations between linear polynomials over integer variables.
  QF-NIA    : Logic
  -- ^ Quantifier-free integer arithmetic.
  NIA       : Logic
  -- ^ Non-linear integer arithmetic.
  UFNIA     : Logic
  -- ^ Non-linear integer arithmetic with uninterpreted sort and function symbols.
  AUFNIRA   : Logic
  -- ^ Closed formulas with free function and predicate symbols over a theory of
  --   arrays of arrays of integer index and real value.
  LIA       : Logic
  -- ^ Closed linear formulas over linear integer arithmetic.
  AUFLIRA   : Logic
  -- ^ Closed linear formulas with free sort and function symbols over one- and
  --   two-dimentional arrays of integer index and real value.
  ALIA      : Logic
  -- ^ Closed linear formulas over linear integer arithmetic and integer arrays.
  AUFLIA    : Logic
  -- ^ Closed formulas over the theory of linear integer arithmetic and arrays
  --   extended with free sort and function symbols but restricted to arrays
  --   with integer indices and values.
  QF-ALIA   : Logic
  -- ^ Unquantifier linear integer arithmetic and with one- and two-dimensional
  --   arrays of integers.
  QF-AUFLIA : Logic
  -- ^ Closed quantifier-free linear formulas over the theory of integer arrays
  --   extended with free sort and function symbols.
  QF-UFIDL  : Logic
  -- ^ Difference Logic over the integers (in essence) but with uninterpreted
  --   sort and function symbols.
  QF-UFLIA  : Logic
  -- ^ Unquantified linear integer arithmetic with uninterpreted sort and
  --   function symbols.
  QF-UFNIA  : Logic
  -- ^ Unquantified non-linear integer arithmetic with uninterpreted sort and
  --   function symbols.
  QF-UF     : Logic
  -- ^ Unquantified formulas built over a signature of uninterpreted (i.e.,
  --   free) sort and function symbols.
  QF-UFLRA  : Logic
  -- ^ Unquantified linear real arithmetic with uninterpreted sort and function
  --   symbols.
  UFLRA     : Logic
  -- ^ Linear real arithmetic with uninterpreted sort and function symbols.
  QF-UFNRA  : Logic
  -- ^ Unquantified non-linear real arithmetic with uninterpreted sort and
  --   function symbols.
  QF-UFBV   : Logic
  -- ^ Unquantified formulas over bitvectors with uninterpreted sort function
  --   and symbols.
  QF-AUFBV  : Logic
  -- ^ Closed quantifier-free formulas over the theory of bitvectors and
  --   bitvector arrays extended with free sort and function symbols.
  QF-BV     : Logic
  -- ^ Closed quantifier-free formulas over the theory of fixed-size bitvectors.
  QF-ABV    : Logic
  -- ^ Closed quantifier-free formulas over the theory of bitvectors and
  --   bitvector arrays.
  QF-RDL    : Logic
  -- ^ Difference Logic over the reals. In essence, Boolean combinations of
  --   inequations of the form x - y < b where x and y are real variables and b is
  --   a rational constant.
  QF-LRA    : Logic
  -- ^ Unquantified linear real arithmetic. In essence, Boolean combinations of
  --   inequations between linear polynomials over real variables.
  NRA       : Logic
  -- ^ Non-linear real arithmetic.
  LRA       : Logic
  -- ^ Closed linear formulas in linear real arithmetic.
  QF-NRA    : Logic
  -- ^ Quantifier-free real arithmetic.


-- |The ⊂-step-relation encodes the edges of the inclusion graph for SMT-LIB 2.
data _⊂-step_ : (l₁ l₂ : Logic) → Set where
  QF-IDL⊂-stepQF-LIA      : QF-IDL     ⊂-step QF-LIA
  QF-LIA⊂-stepQF-NIA      : QF-LIA     ⊂-step QF-NIA
  NIA⊂-stepUFNIA          : NIA        ⊂-step UFNIA
  UFNIA⊂-stepAUFNIRA      : UFNIA      ⊂-step AUFNIRA
  QF-LIA⊂-stepLIA         : QF-LIA     ⊂-step LIA
  LIA⊂-stepAUFLIRA        : LIA        ⊂-step AUFLIRA
  AUFLIRA⊂-stepAUFNIRA    : AUFLIRA    ⊂-step AUFNIRA
  LIA⊂-stepALIA           : LIA        ⊂-step ALIA
  ALIA⊂-stepAUFLIA        : ALIA       ⊂-step AUFLIA
  QF-LIA⊂-stepQF-ALIA     : QF-LIA     ⊂-step QF-ALIA
  QF-ALIA⊂-stepQF-AUFLIA  : QF-ALIA    ⊂-step QF-AUFLIA
  QF-AUFLIA⊂-stepAUFLIA   : QF-AUFLIA  ⊂-step AUFLIA
  QF-LIA⊂-stepQF-UFLIA    : QF-LIA     ⊂-step QF-UFLIA
  QF-UFLIA⊂-stepQF-AUFLIA : QF-UFLIA   ⊂-step QF-AUFLIA
  QF-UFLIA⊂-stepQF-UFNIA  : QF-UFLIA   ⊂-step QF-UFNIA
  QF-UFNIA⊂-stepUFNIA     : QF-UFNIA   ⊂-step UFNIA
  QF-IDL⊂-stepQF-UFIDL    : QF-IDL     ⊂-step QF-UFIDL
  QF-UFIDL⊂-stepQF-UFLIA  : QF-UFIDL   ⊂-step QF-UFLIA
  QF-UF⊂-stepQF-UFIDL     : QF-UF      ⊂-step QF-UFIDL
  QF-UF⊂-stepQF-UFLRA     : QF-UF      ⊂-step QF-UFLRA
  QF-UFLRA⊂-stepUFLRA     : QF-UFLRA   ⊂-step UFLRA
  UFLRA⊂-stepAUFLIRA      : UFLRA      ⊂-step AUFLIRA
  QF-UFLRA⊂-stepQF-UFNRA  : QF-UFLRA   ⊂-step QF-UFNRA
  QF-UFNRA⊂-stepAUFNIRA   : QF-UFNRA   ⊂-step AUFNIRA
  QF-UF⊂-stepQF-UFBV      : QF-UF      ⊂-step QF-UFBV
  QF-UFBV⊂-stepQF-AUFBV   : QF-UFBV    ⊂-step QF-AUFBV
  QF-BV⊂-stepQF-UFBV      : QF-BV      ⊂-step QF-UFBV
  QF-BV⊂-stepQF-ABV       : QF-BV      ⊂-step QF-ABV
  QF-ABV⊂-stepQF-AUFBV    : QF-ABV     ⊂-step QF-AUFBV
  QF-RDL⊂-stepQF-LRA      : QF-RDL     ⊂-step QF-LRA
  QF-LRA⊂-stepQF-UFNRA    : QF-LRA     ⊂-step QF-UFNRA
  QF-LRA⊂-stepLRA         : QF-LRA     ⊂-step LRA
  LRA⊂-stepUFLRA          : LRA        ⊂-step UFLRA
  LRA⊂-stepNRA            : LRA        ⊂-step NRA
  NRA⊂-stepAUFNIRA        : NRA        ⊂-step AUFNIRA
  QF-LRA⊂-stepQF-NRA      : QF-LRA     ⊂-step QF-NRA
  QF-NRA⊂-stepNRA         : QF-NRA     ⊂-step NRA


-- |The depth of a logic is the logiest path from any of the depth 0 logics.
--
--  NOTE: We are defining depth to help us induce a proof that _⊂-step_ and its
--        transitive closure _<_ are well-founded relations.
--
depth : Logic → ℕ
depth QF-AX     = 0
depth QF-IDL    = 0
depth QF-LIA    = 1
depth QF-NIA    = 2
depth NIA       = 3
depth UFNIA     = 4
depth AUFNIRA   = 5
depth LIA       = 2
depth AUFLIRA   = 4
depth ALIA      = 3
depth AUFLIA    = 4
depth QF-ALIA   = 2
depth QF-AUFLIA = 3
depth QF-UFIDL  = 1
depth QF-UFLIA  = 2
depth QF-UFNIA  = 3
depth QF-UF     = 0
depth QF-UFLRA  = 1
depth UFLRA     = 3
depth QF-UFNRA  = 3
depth QF-UFBV   = 1
depth QF-AUFBV  = 2
depth QF-BV     = 0
depth QF-ABV    = 1
depth QF-RDL    = 0
depth QF-LRA    = 1
depth NRA       = 3
depth LRA       = 2
depth QF-NRA    = 2

private
  auto : ∀ {n₁ n₂} {p : True (n₁ Nat.<? n₂)} → n₁ Nat.< n₂
  auto {p = p} = toWitness p

-- |The ⊂-step-relation respects depth.
⊂-step-depth : ∀ {l₁ l₂} → l₁ ⊂-step l₂ → depth l₁ Nat.< depth l₂
⊂-step-depth QF-IDL⊂-stepQF-LIA      = auto
⊂-step-depth QF-LIA⊂-stepQF-NIA      = auto
⊂-step-depth NIA⊂-stepUFNIA          = auto
⊂-step-depth UFNIA⊂-stepAUFNIRA      = auto
⊂-step-depth QF-LIA⊂-stepLIA         = auto
⊂-step-depth LIA⊂-stepAUFLIRA        = auto
⊂-step-depth AUFLIRA⊂-stepAUFNIRA    = auto
⊂-step-depth LIA⊂-stepALIA           = auto
⊂-step-depth ALIA⊂-stepAUFLIA        = auto
⊂-step-depth QF-LIA⊂-stepQF-ALIA     = auto
⊂-step-depth QF-ALIA⊂-stepQF-AUFLIA  = auto
⊂-step-depth QF-AUFLIA⊂-stepAUFLIA   = auto
⊂-step-depth QF-LIA⊂-stepQF-UFLIA    = auto
⊂-step-depth QF-UFLIA⊂-stepQF-AUFLIA = auto
⊂-step-depth QF-UFLIA⊂-stepQF-UFNIA  = auto
⊂-step-depth QF-UFNIA⊂-stepUFNIA     = auto
⊂-step-depth QF-IDL⊂-stepQF-UFIDL    = auto
⊂-step-depth QF-UFIDL⊂-stepQF-UFLIA  = auto
⊂-step-depth QF-UF⊂-stepQF-UFIDL     = auto
⊂-step-depth QF-UF⊂-stepQF-UFLRA     = auto
⊂-step-depth QF-UFLRA⊂-stepUFLRA     = auto
⊂-step-depth UFLRA⊂-stepAUFLIRA      = auto
⊂-step-depth QF-UFLRA⊂-stepQF-UFNRA  = auto
⊂-step-depth QF-UFNRA⊂-stepAUFNIRA   = auto
⊂-step-depth QF-UF⊂-stepQF-UFBV      = auto
⊂-step-depth QF-UFBV⊂-stepQF-AUFBV   = auto
⊂-step-depth QF-BV⊂-stepQF-UFBV      = auto
⊂-step-depth QF-BV⊂-stepQF-ABV       = auto
⊂-step-depth QF-ABV⊂-stepQF-AUFBV    = auto
⊂-step-depth QF-RDL⊂-stepQF-LRA      = auto
⊂-step-depth QF-LRA⊂-stepQF-UFNRA    = auto
⊂-step-depth QF-LRA⊂-stepLRA         = auto
⊂-step-depth LRA⊂-stepUFLRA          = auto
⊂-step-depth LRA⊂-stepNRA            = auto
⊂-step-depth NRA⊂-stepAUFNIRA        = auto
⊂-step-depth QF-LRA⊂-stepQF-NRA      = auto
⊂-step-depth QF-NRA⊂-stepNRA         = auto

module <-depth⇒< = InverseImage {_<_ = Nat._<_} depth
module ⊂-step⇒<-depth = Subrelation {_<₁_ = _⊂-step_} {_<₂_ = Nat._<_ on depth} ⊂-step-depth
module ⊂⇒⊂-step = TransitiveClosure _⊂-step_

open ⊂⇒⊂-step public
  using ([_]; trans)
  renaming (_<⁺_ to _⊂_; downwardsClosed to ⊂-downwardsClosed)

-- |The ⊂-step-relation is well-founded via depth.
⊂-step-wellFounded : WellFounded _⊂-step_
⊂-step-wellFounded = ⊂-step⇒<-depth.wellFounded (<-depth⇒<.wellFounded WfNat.<-wellFounded)

-- |The transitive closure of the ⊂-step-relation is well-founded via depth.
⊂-wellFounded : WellFounded _⊂_
⊂-wellFounded = ⊂⇒⊂-step.wellFounded ⊂-step-wellFounded

-- |Decision procedure for the ⊂-step relation.
_⊂-step?_ : (l₁ l₂ : Logic) → Dec (l₁ ⊂-step l₂)
QF-AX     ⊂-step? QF-AX     = no (λ ())
QF-AX     ⊂-step? QF-IDL    = no (λ ())
QF-AX     ⊂-step? QF-LIA    = no (λ ())
QF-AX     ⊂-step? QF-NIA    = no (λ ())
QF-AX     ⊂-step? NIA       = no (λ ())
QF-AX     ⊂-step? UFNIA     = no (λ ())
QF-AX     ⊂-step? AUFNIRA   = no (λ ())
QF-AX     ⊂-step? LIA       = no (λ ())
QF-AX     ⊂-step? AUFLIRA   = no (λ ())
QF-AX     ⊂-step? ALIA      = no (λ ())
QF-AX     ⊂-step? AUFLIA    = no (λ ())
QF-AX     ⊂-step? QF-ALIA   = no (λ ())
QF-AX     ⊂-step? QF-AUFLIA = no (λ ())
QF-AX     ⊂-step? QF-UFIDL  = no (λ ())
QF-AX     ⊂-step? QF-UFLIA  = no (λ ())
QF-AX     ⊂-step? QF-UFNIA  = no (λ ())
QF-AX     ⊂-step? QF-UF     = no (λ ())
QF-AX     ⊂-step? QF-UFLRA  = no (λ ())
QF-AX     ⊂-step? UFLRA     = no (λ ())
QF-AX     ⊂-step? QF-UFNRA  = no (λ ())
QF-AX     ⊂-step? QF-UFBV   = no (λ ())
QF-AX     ⊂-step? QF-AUFBV  = no (λ ())
QF-AX     ⊂-step? QF-BV     = no (λ ())
QF-AX     ⊂-step? QF-ABV    = no (λ ())
QF-AX     ⊂-step? QF-RDL    = no (λ ())
QF-AX     ⊂-step? QF-LRA    = no (λ ())
QF-AX     ⊂-step? NRA       = no (λ ())
QF-AX     ⊂-step? LRA       = no (λ ())
QF-AX     ⊂-step? QF-NRA    = no (λ ())
QF-IDL    ⊂-step? QF-AX     = no (λ ())
QF-IDL    ⊂-step? QF-IDL    = no (λ ())
QF-IDL    ⊂-step? QF-LIA    = yes QF-IDL⊂-stepQF-LIA
QF-IDL    ⊂-step? QF-NIA    = no (λ ())
QF-IDL    ⊂-step? NIA       = no (λ ())
QF-IDL    ⊂-step? UFNIA     = no (λ ())
QF-IDL    ⊂-step? AUFNIRA   = no (λ ())
QF-IDL    ⊂-step? LIA       = no (λ ())
QF-IDL    ⊂-step? AUFLIRA   = no (λ ())
QF-IDL    ⊂-step? ALIA      = no (λ ())
QF-IDL    ⊂-step? AUFLIA    = no (λ ())
QF-IDL    ⊂-step? QF-ALIA   = no (λ ())
QF-IDL    ⊂-step? QF-AUFLIA = no (λ ())
QF-IDL    ⊂-step? QF-UFIDL  = yes QF-IDL⊂-stepQF-UFIDL
QF-IDL    ⊂-step? QF-UFLIA  = no (λ ())
QF-IDL    ⊂-step? QF-UFNIA  = no (λ ())
QF-IDL    ⊂-step? QF-UF     = no (λ ())
QF-IDL    ⊂-step? QF-UFLRA  = no (λ ())
QF-IDL    ⊂-step? UFLRA     = no (λ ())
QF-IDL    ⊂-step? QF-UFNRA  = no (λ ())
QF-IDL    ⊂-step? QF-UFBV   = no (λ ())
QF-IDL    ⊂-step? QF-AUFBV  = no (λ ())
QF-IDL    ⊂-step? QF-BV     = no (λ ())
QF-IDL    ⊂-step? QF-ABV    = no (λ ())
QF-IDL    ⊂-step? QF-RDL    = no (λ ())
QF-IDL    ⊂-step? QF-LRA    = no (λ ())
QF-IDL    ⊂-step? NRA       = no (λ ())
QF-IDL    ⊂-step? LRA       = no (λ ())
QF-IDL    ⊂-step? QF-NRA    = no (λ ())
QF-LIA    ⊂-step? QF-AX     = no (λ ())
QF-LIA    ⊂-step? QF-IDL    = no (λ ())
QF-LIA    ⊂-step? QF-LIA    = no (λ ())
QF-LIA    ⊂-step? QF-NIA    = yes QF-LIA⊂-stepQF-NIA
QF-LIA    ⊂-step? NIA       = no (λ ())
QF-LIA    ⊂-step? UFNIA     = no (λ ())
QF-LIA    ⊂-step? AUFNIRA   = no (λ ())
QF-LIA    ⊂-step? LIA       = yes QF-LIA⊂-stepLIA
QF-LIA    ⊂-step? AUFLIRA   = no (λ ())
QF-LIA    ⊂-step? ALIA      = no (λ ())
QF-LIA    ⊂-step? AUFLIA    = no (λ ())
QF-LIA    ⊂-step? QF-ALIA   = yes QF-LIA⊂-stepQF-ALIA
QF-LIA    ⊂-step? QF-AUFLIA = no (λ ())
QF-LIA    ⊂-step? QF-UFIDL  = no (λ ())
QF-LIA    ⊂-step? QF-UFLIA  = yes QF-LIA⊂-stepQF-UFLIA
QF-LIA    ⊂-step? QF-UFNIA  = no (λ ())
QF-LIA    ⊂-step? QF-UF     = no (λ ())
QF-LIA    ⊂-step? QF-UFLRA  = no (λ ())
QF-LIA    ⊂-step? UFLRA     = no (λ ())
QF-LIA    ⊂-step? QF-UFNRA  = no (λ ())
QF-LIA    ⊂-step? QF-UFBV   = no (λ ())
QF-LIA    ⊂-step? QF-AUFBV  = no (λ ())
QF-LIA    ⊂-step? QF-BV     = no (λ ())
QF-LIA    ⊂-step? QF-ABV    = no (λ ())
QF-LIA    ⊂-step? QF-RDL    = no (λ ())
QF-LIA    ⊂-step? QF-LRA    = no (λ ())
QF-LIA    ⊂-step? NRA       = no (λ ())
QF-LIA    ⊂-step? LRA       = no (λ ())
QF-LIA    ⊂-step? QF-NRA    = no (λ ())
QF-NIA    ⊂-step? QF-AX     = no (λ ())
QF-NIA    ⊂-step? QF-IDL    = no (λ ())
QF-NIA    ⊂-step? QF-LIA    = no (λ ())
QF-NIA    ⊂-step? QF-NIA    = no (λ ())
QF-NIA    ⊂-step? NIA       = no (λ ())
QF-NIA    ⊂-step? UFNIA     = no (λ ())
QF-NIA    ⊂-step? AUFNIRA   = no (λ ())
QF-NIA    ⊂-step? LIA       = no (λ ())
QF-NIA    ⊂-step? AUFLIRA   = no (λ ())
QF-NIA    ⊂-step? ALIA      = no (λ ())
QF-NIA    ⊂-step? AUFLIA    = no (λ ())
QF-NIA    ⊂-step? QF-ALIA   = no (λ ())
QF-NIA    ⊂-step? QF-AUFLIA = no (λ ())
QF-NIA    ⊂-step? QF-UFIDL  = no (λ ())
QF-NIA    ⊂-step? QF-UFLIA  = no (λ ())
QF-NIA    ⊂-step? QF-UFNIA  = no (λ ())
QF-NIA    ⊂-step? QF-UF     = no (λ ())
QF-NIA    ⊂-step? QF-UFLRA  = no (λ ())
QF-NIA    ⊂-step? UFLRA     = no (λ ())
QF-NIA    ⊂-step? QF-UFNRA  = no (λ ())
QF-NIA    ⊂-step? QF-UFBV   = no (λ ())
QF-NIA    ⊂-step? QF-AUFBV  = no (λ ())
QF-NIA    ⊂-step? QF-BV     = no (λ ())
QF-NIA    ⊂-step? QF-ABV    = no (λ ())
QF-NIA    ⊂-step? QF-RDL    = no (λ ())
QF-NIA    ⊂-step? QF-LRA    = no (λ ())
QF-NIA    ⊂-step? NRA       = no (λ ())
QF-NIA    ⊂-step? LRA       = no (λ ())
QF-NIA    ⊂-step? QF-NRA    = no (λ ())
NIA       ⊂-step? QF-AX     = no (λ ())
NIA       ⊂-step? QF-IDL    = no (λ ())
NIA       ⊂-step? QF-LIA    = no (λ ())
NIA       ⊂-step? QF-NIA    = no (λ ())
NIA       ⊂-step? NIA       = no (λ ())
NIA       ⊂-step? UFNIA     = yes NIA⊂-stepUFNIA
NIA       ⊂-step? AUFNIRA   = no (λ ())
NIA       ⊂-step? LIA       = no (λ ())
NIA       ⊂-step? AUFLIRA   = no (λ ())
NIA       ⊂-step? ALIA      = no (λ ())
NIA       ⊂-step? AUFLIA    = no (λ ())
NIA       ⊂-step? QF-ALIA   = no (λ ())
NIA       ⊂-step? QF-AUFLIA = no (λ ())
NIA       ⊂-step? QF-UFIDL  = no (λ ())
NIA       ⊂-step? QF-UFLIA  = no (λ ())
NIA       ⊂-step? QF-UFNIA  = no (λ ())
NIA       ⊂-step? QF-UF     = no (λ ())
NIA       ⊂-step? QF-UFLRA  = no (λ ())
NIA       ⊂-step? UFLRA     = no (λ ())
NIA       ⊂-step? QF-UFNRA  = no (λ ())
NIA       ⊂-step? QF-UFBV   = no (λ ())
NIA       ⊂-step? QF-AUFBV  = no (λ ())
NIA       ⊂-step? QF-BV     = no (λ ())
NIA       ⊂-step? QF-ABV    = no (λ ())
NIA       ⊂-step? QF-RDL    = no (λ ())
NIA       ⊂-step? QF-LRA    = no (λ ())
NIA       ⊂-step? NRA       = no (λ ())
NIA       ⊂-step? LRA       = no (λ ())
NIA       ⊂-step? QF-NRA    = no (λ ())
UFNIA     ⊂-step? QF-AX     = no (λ ())
UFNIA     ⊂-step? QF-IDL    = no (λ ())
UFNIA     ⊂-step? QF-LIA    = no (λ ())
UFNIA     ⊂-step? QF-NIA    = no (λ ())
UFNIA     ⊂-step? NIA       = no (λ ())
UFNIA     ⊂-step? UFNIA     = no (λ ())
UFNIA     ⊂-step? AUFNIRA   = yes UFNIA⊂-stepAUFNIRA
UFNIA     ⊂-step? LIA       = no (λ ())
UFNIA     ⊂-step? AUFLIRA   = no (λ ())
UFNIA     ⊂-step? ALIA      = no (λ ())
UFNIA     ⊂-step? AUFLIA    = no (λ ())
UFNIA     ⊂-step? QF-ALIA   = no (λ ())
UFNIA     ⊂-step? QF-AUFLIA = no (λ ())
UFNIA     ⊂-step? QF-UFIDL  = no (λ ())
UFNIA     ⊂-step? QF-UFLIA  = no (λ ())
UFNIA     ⊂-step? QF-UFNIA  = no (λ ())
UFNIA     ⊂-step? QF-UF     = no (λ ())
UFNIA     ⊂-step? QF-UFLRA  = no (λ ())
UFNIA     ⊂-step? UFLRA     = no (λ ())
UFNIA     ⊂-step? QF-UFNRA  = no (λ ())
UFNIA     ⊂-step? QF-UFBV   = no (λ ())
UFNIA     ⊂-step? QF-AUFBV  = no (λ ())
UFNIA     ⊂-step? QF-BV     = no (λ ())
UFNIA     ⊂-step? QF-ABV    = no (λ ())
UFNIA     ⊂-step? QF-RDL    = no (λ ())
UFNIA     ⊂-step? QF-LRA    = no (λ ())
UFNIA     ⊂-step? NRA       = no (λ ())
UFNIA     ⊂-step? LRA       = no (λ ())
UFNIA     ⊂-step? QF-NRA    = no (λ ())
AUFNIRA   ⊂-step? QF-AX     = no (λ ())
AUFNIRA   ⊂-step? QF-IDL    = no (λ ())
AUFNIRA   ⊂-step? QF-LIA    = no (λ ())
AUFNIRA   ⊂-step? QF-NIA    = no (λ ())
AUFNIRA   ⊂-step? NIA       = no (λ ())
AUFNIRA   ⊂-step? UFNIA     = no (λ ())
AUFNIRA   ⊂-step? AUFNIRA   = no (λ ())
AUFNIRA   ⊂-step? LIA       = no (λ ())
AUFNIRA   ⊂-step? AUFLIRA   = no (λ ())
AUFNIRA   ⊂-step? ALIA      = no (λ ())
AUFNIRA   ⊂-step? AUFLIA    = no (λ ())
AUFNIRA   ⊂-step? QF-ALIA   = no (λ ())
AUFNIRA   ⊂-step? QF-AUFLIA = no (λ ())
AUFNIRA   ⊂-step? QF-UFIDL  = no (λ ())
AUFNIRA   ⊂-step? QF-UFLIA  = no (λ ())
AUFNIRA   ⊂-step? QF-UFNIA  = no (λ ())
AUFNIRA   ⊂-step? QF-UF     = no (λ ())
AUFNIRA   ⊂-step? QF-UFLRA  = no (λ ())
AUFNIRA   ⊂-step? UFLRA     = no (λ ())
AUFNIRA   ⊂-step? QF-UFNRA  = no (λ ())
AUFNIRA   ⊂-step? QF-UFBV   = no (λ ())
AUFNIRA   ⊂-step? QF-AUFBV  = no (λ ())
AUFNIRA   ⊂-step? QF-BV     = no (λ ())
AUFNIRA   ⊂-step? QF-ABV    = no (λ ())
AUFNIRA   ⊂-step? QF-RDL    = no (λ ())
AUFNIRA   ⊂-step? QF-LRA    = no (λ ())
AUFNIRA   ⊂-step? NRA       = no (λ ())
AUFNIRA   ⊂-step? LRA       = no (λ ())
AUFNIRA   ⊂-step? QF-NRA    = no (λ ())
LIA       ⊂-step? QF-AX     = no (λ ())
LIA       ⊂-step? QF-IDL    = no (λ ())
LIA       ⊂-step? QF-LIA    = no (λ ())
LIA       ⊂-step? QF-NIA    = no (λ ())
LIA       ⊂-step? NIA       = no (λ ())
LIA       ⊂-step? UFNIA     = no (λ ())
LIA       ⊂-step? AUFNIRA   = no (λ ())
LIA       ⊂-step? LIA       = no (λ ())
LIA       ⊂-step? AUFLIRA   = yes LIA⊂-stepAUFLIRA
LIA       ⊂-step? ALIA      = yes LIA⊂-stepALIA
LIA       ⊂-step? AUFLIA    = no (λ ())
LIA       ⊂-step? QF-ALIA   = no (λ ())
LIA       ⊂-step? QF-AUFLIA = no (λ ())
LIA       ⊂-step? QF-UFIDL  = no (λ ())
LIA       ⊂-step? QF-UFLIA  = no (λ ())
LIA       ⊂-step? QF-UFNIA  = no (λ ())
LIA       ⊂-step? QF-UF     = no (λ ())
LIA       ⊂-step? QF-UFLRA  = no (λ ())
LIA       ⊂-step? UFLRA     = no (λ ())
LIA       ⊂-step? QF-UFNRA  = no (λ ())
LIA       ⊂-step? QF-UFBV   = no (λ ())
LIA       ⊂-step? QF-AUFBV  = no (λ ())
LIA       ⊂-step? QF-BV     = no (λ ())
LIA       ⊂-step? QF-ABV    = no (λ ())
LIA       ⊂-step? QF-RDL    = no (λ ())
LIA       ⊂-step? QF-LRA    = no (λ ())
LIA       ⊂-step? NRA       = no (λ ())
LIA       ⊂-step? LRA       = no (λ ())
LIA       ⊂-step? QF-NRA    = no (λ ())
AUFLIRA   ⊂-step? QF-AX     = no (λ ())
AUFLIRA   ⊂-step? QF-IDL    = no (λ ())
AUFLIRA   ⊂-step? QF-LIA    = no (λ ())
AUFLIRA   ⊂-step? QF-NIA    = no (λ ())
AUFLIRA   ⊂-step? NIA       = no (λ ())
AUFLIRA   ⊂-step? UFNIA     = no (λ ())
AUFLIRA   ⊂-step? AUFNIRA   = yes AUFLIRA⊂-stepAUFNIRA
AUFLIRA   ⊂-step? LIA       = no (λ ())
AUFLIRA   ⊂-step? AUFLIRA   = no (λ ())
AUFLIRA   ⊂-step? ALIA      = no (λ ())
AUFLIRA   ⊂-step? AUFLIA    = no (λ ())
AUFLIRA   ⊂-step? QF-ALIA   = no (λ ())
AUFLIRA   ⊂-step? QF-AUFLIA = no (λ ())
AUFLIRA   ⊂-step? QF-UFIDL  = no (λ ())
AUFLIRA   ⊂-step? QF-UFLIA  = no (λ ())
AUFLIRA   ⊂-step? QF-UFNIA  = no (λ ())
AUFLIRA   ⊂-step? QF-UF     = no (λ ())
AUFLIRA   ⊂-step? QF-UFLRA  = no (λ ())
AUFLIRA   ⊂-step? UFLRA     = no (λ ())
AUFLIRA   ⊂-step? QF-UFNRA  = no (λ ())
AUFLIRA   ⊂-step? QF-UFBV   = no (λ ())
AUFLIRA   ⊂-step? QF-AUFBV  = no (λ ())
AUFLIRA   ⊂-step? QF-BV     = no (λ ())
AUFLIRA   ⊂-step? QF-ABV    = no (λ ())
AUFLIRA   ⊂-step? QF-RDL    = no (λ ())
AUFLIRA   ⊂-step? QF-LRA    = no (λ ())
AUFLIRA   ⊂-step? NRA       = no (λ ())
AUFLIRA   ⊂-step? LRA       = no (λ ())
AUFLIRA   ⊂-step? QF-NRA    = no (λ ())
ALIA      ⊂-step? QF-AX     = no (λ ())
ALIA      ⊂-step? QF-IDL    = no (λ ())
ALIA      ⊂-step? QF-LIA    = no (λ ())
ALIA      ⊂-step? QF-NIA    = no (λ ())
ALIA      ⊂-step? NIA       = no (λ ())
ALIA      ⊂-step? UFNIA     = no (λ ())
ALIA      ⊂-step? AUFNIRA   = no (λ ())
ALIA      ⊂-step? LIA       = no (λ ())
ALIA      ⊂-step? AUFLIRA   = no (λ ())
ALIA      ⊂-step? ALIA      = no (λ ())
ALIA      ⊂-step? AUFLIA    = yes ALIA⊂-stepAUFLIA
ALIA      ⊂-step? QF-ALIA   = no (λ ())
ALIA      ⊂-step? QF-AUFLIA = no (λ ())
ALIA      ⊂-step? QF-UFIDL  = no (λ ())
ALIA      ⊂-step? QF-UFLIA  = no (λ ())
ALIA      ⊂-step? QF-UFNIA  = no (λ ())
ALIA      ⊂-step? QF-UF     = no (λ ())
ALIA      ⊂-step? QF-UFLRA  = no (λ ())
ALIA      ⊂-step? UFLRA     = no (λ ())
ALIA      ⊂-step? QF-UFNRA  = no (λ ())
ALIA      ⊂-step? QF-UFBV   = no (λ ())
ALIA      ⊂-step? QF-AUFBV  = no (λ ())
ALIA      ⊂-step? QF-BV     = no (λ ())
ALIA      ⊂-step? QF-ABV    = no (λ ())
ALIA      ⊂-step? QF-RDL    = no (λ ())
ALIA      ⊂-step? QF-LRA    = no (λ ())
ALIA      ⊂-step? NRA       = no (λ ())
ALIA      ⊂-step? LRA       = no (λ ())
ALIA      ⊂-step? QF-NRA    = no (λ ())
AUFLIA    ⊂-step? QF-AX     = no (λ ())
AUFLIA    ⊂-step? QF-IDL    = no (λ ())
AUFLIA    ⊂-step? QF-LIA    = no (λ ())
AUFLIA    ⊂-step? QF-NIA    = no (λ ())
AUFLIA    ⊂-step? NIA       = no (λ ())
AUFLIA    ⊂-step? UFNIA     = no (λ ())
AUFLIA    ⊂-step? AUFNIRA   = no (λ ())
AUFLIA    ⊂-step? LIA       = no (λ ())
AUFLIA    ⊂-step? AUFLIRA   = no (λ ())
AUFLIA    ⊂-step? ALIA      = no (λ ())
AUFLIA    ⊂-step? AUFLIA    = no (λ ())
AUFLIA    ⊂-step? QF-ALIA   = no (λ ())
AUFLIA    ⊂-step? QF-AUFLIA = no (λ ())
AUFLIA    ⊂-step? QF-UFIDL  = no (λ ())
AUFLIA    ⊂-step? QF-UFLIA  = no (λ ())
AUFLIA    ⊂-step? QF-UFNIA  = no (λ ())
AUFLIA    ⊂-step? QF-UF     = no (λ ())
AUFLIA    ⊂-step? QF-UFLRA  = no (λ ())
AUFLIA    ⊂-step? UFLRA     = no (λ ())
AUFLIA    ⊂-step? QF-UFNRA  = no (λ ())
AUFLIA    ⊂-step? QF-UFBV   = no (λ ())
AUFLIA    ⊂-step? QF-AUFBV  = no (λ ())
AUFLIA    ⊂-step? QF-BV     = no (λ ())
AUFLIA    ⊂-step? QF-ABV    = no (λ ())
AUFLIA    ⊂-step? QF-RDL    = no (λ ())
AUFLIA    ⊂-step? QF-LRA    = no (λ ())
AUFLIA    ⊂-step? NRA       = no (λ ())
AUFLIA    ⊂-step? LRA       = no (λ ())
AUFLIA    ⊂-step? QF-NRA    = no (λ ())
QF-ALIA   ⊂-step? QF-AX     = no (λ ())
QF-ALIA   ⊂-step? QF-IDL    = no (λ ())
QF-ALIA   ⊂-step? QF-LIA    = no (λ ())
QF-ALIA   ⊂-step? QF-NIA    = no (λ ())
QF-ALIA   ⊂-step? NIA       = no (λ ())
QF-ALIA   ⊂-step? UFNIA     = no (λ ())
QF-ALIA   ⊂-step? AUFNIRA   = no (λ ())
QF-ALIA   ⊂-step? LIA       = no (λ ())
QF-ALIA   ⊂-step? AUFLIRA   = no (λ ())
QF-ALIA   ⊂-step? ALIA      = no (λ ())
QF-ALIA   ⊂-step? AUFLIA    = no (λ ())
QF-ALIA   ⊂-step? QF-ALIA   = no (λ ())
QF-ALIA   ⊂-step? QF-AUFLIA = yes QF-ALIA⊂-stepQF-AUFLIA
QF-ALIA   ⊂-step? QF-UFIDL  = no (λ ())
QF-ALIA   ⊂-step? QF-UFLIA  = no (λ ())
QF-ALIA   ⊂-step? QF-UFNIA  = no (λ ())
QF-ALIA   ⊂-step? QF-UF     = no (λ ())
QF-ALIA   ⊂-step? QF-UFLRA  = no (λ ())
QF-ALIA   ⊂-step? UFLRA     = no (λ ())
QF-ALIA   ⊂-step? QF-UFNRA  = no (λ ())
QF-ALIA   ⊂-step? QF-UFBV   = no (λ ())
QF-ALIA   ⊂-step? QF-AUFBV  = no (λ ())
QF-ALIA   ⊂-step? QF-BV     = no (λ ())
QF-ALIA   ⊂-step? QF-ABV    = no (λ ())
QF-ALIA   ⊂-step? QF-RDL    = no (λ ())
QF-ALIA   ⊂-step? QF-LRA    = no (λ ())
QF-ALIA   ⊂-step? NRA       = no (λ ())
QF-ALIA   ⊂-step? LRA       = no (λ ())
QF-ALIA   ⊂-step? QF-NRA    = no (λ ())
QF-AUFLIA ⊂-step? QF-AX     = no (λ ())
QF-AUFLIA ⊂-step? QF-IDL    = no (λ ())
QF-AUFLIA ⊂-step? QF-LIA    = no (λ ())
QF-AUFLIA ⊂-step? QF-NIA    = no (λ ())
QF-AUFLIA ⊂-step? NIA       = no (λ ())
QF-AUFLIA ⊂-step? UFNIA     = no (λ ())
QF-AUFLIA ⊂-step? AUFNIRA   = no (λ ())
QF-AUFLIA ⊂-step? LIA       = no (λ ())
QF-AUFLIA ⊂-step? AUFLIRA   = no (λ ())
QF-AUFLIA ⊂-step? ALIA      = no (λ ())
QF-AUFLIA ⊂-step? AUFLIA    = yes QF-AUFLIA⊂-stepAUFLIA
QF-AUFLIA ⊂-step? QF-ALIA   = no (λ ())
QF-AUFLIA ⊂-step? QF-AUFLIA = no (λ ())
QF-AUFLIA ⊂-step? QF-UFIDL  = no (λ ())
QF-AUFLIA ⊂-step? QF-UFLIA  = no (λ ())
QF-AUFLIA ⊂-step? QF-UFNIA  = no (λ ())
QF-AUFLIA ⊂-step? QF-UF     = no (λ ())
QF-AUFLIA ⊂-step? QF-UFLRA  = no (λ ())
QF-AUFLIA ⊂-step? UFLRA     = no (λ ())
QF-AUFLIA ⊂-step? QF-UFNRA  = no (λ ())
QF-AUFLIA ⊂-step? QF-UFBV   = no (λ ())
QF-AUFLIA ⊂-step? QF-AUFBV  = no (λ ())
QF-AUFLIA ⊂-step? QF-BV     = no (λ ())
QF-AUFLIA ⊂-step? QF-ABV    = no (λ ())
QF-AUFLIA ⊂-step? QF-RDL    = no (λ ())
QF-AUFLIA ⊂-step? QF-LRA    = no (λ ())
QF-AUFLIA ⊂-step? NRA       = no (λ ())
QF-AUFLIA ⊂-step? LRA       = no (λ ())
QF-AUFLIA ⊂-step? QF-NRA    = no (λ ())
QF-UFIDL  ⊂-step? QF-AX     = no (λ ())
QF-UFIDL  ⊂-step? QF-IDL    = no (λ ())
QF-UFIDL  ⊂-step? QF-LIA    = no (λ ())
QF-UFIDL  ⊂-step? QF-NIA    = no (λ ())
QF-UFIDL  ⊂-step? NIA       = no (λ ())
QF-UFIDL  ⊂-step? UFNIA     = no (λ ())
QF-UFIDL  ⊂-step? AUFNIRA   = no (λ ())
QF-UFIDL  ⊂-step? LIA       = no (λ ())
QF-UFIDL  ⊂-step? AUFLIRA   = no (λ ())
QF-UFIDL  ⊂-step? ALIA      = no (λ ())
QF-UFIDL  ⊂-step? AUFLIA    = no (λ ())
QF-UFIDL  ⊂-step? QF-ALIA   = no (λ ())
QF-UFIDL  ⊂-step? QF-AUFLIA = no (λ ())
QF-UFIDL  ⊂-step? QF-UFIDL  = no (λ ())
QF-UFIDL  ⊂-step? QF-UFLIA  = yes QF-UFIDL⊂-stepQF-UFLIA
QF-UFIDL  ⊂-step? QF-UFNIA  = no (λ ())
QF-UFIDL  ⊂-step? QF-UF     = no (λ ())
QF-UFIDL  ⊂-step? QF-UFLRA  = no (λ ())
QF-UFIDL  ⊂-step? UFLRA     = no (λ ())
QF-UFIDL  ⊂-step? QF-UFNRA  = no (λ ())
QF-UFIDL  ⊂-step? QF-UFBV   = no (λ ())
QF-UFIDL  ⊂-step? QF-AUFBV  = no (λ ())
QF-UFIDL  ⊂-step? QF-BV     = no (λ ())
QF-UFIDL  ⊂-step? QF-ABV    = no (λ ())
QF-UFIDL  ⊂-step? QF-RDL    = no (λ ())
QF-UFIDL  ⊂-step? QF-LRA    = no (λ ())
QF-UFIDL  ⊂-step? NRA       = no (λ ())
QF-UFIDL  ⊂-step? LRA       = no (λ ())
QF-UFIDL  ⊂-step? QF-NRA    = no (λ ())
QF-UFLIA  ⊂-step? QF-AX     = no (λ ())
QF-UFLIA  ⊂-step? QF-IDL    = no (λ ())
QF-UFLIA  ⊂-step? QF-LIA    = no (λ ())
QF-UFLIA  ⊂-step? QF-NIA    = no (λ ())
QF-UFLIA  ⊂-step? NIA       = no (λ ())
QF-UFLIA  ⊂-step? UFNIA     = no (λ ())
QF-UFLIA  ⊂-step? AUFNIRA   = no (λ ())
QF-UFLIA  ⊂-step? LIA       = no (λ ())
QF-UFLIA  ⊂-step? AUFLIRA   = no (λ ())
QF-UFLIA  ⊂-step? ALIA      = no (λ ())
QF-UFLIA  ⊂-step? AUFLIA    = no (λ ())
QF-UFLIA  ⊂-step? QF-ALIA   = no (λ ())
QF-UFLIA  ⊂-step? QF-AUFLIA = yes QF-UFLIA⊂-stepQF-AUFLIA
QF-UFLIA  ⊂-step? QF-UFIDL  = no (λ ())
QF-UFLIA  ⊂-step? QF-UFLIA  = no (λ ())
QF-UFLIA  ⊂-step? QF-UFNIA  = yes QF-UFLIA⊂-stepQF-UFNIA
QF-UFLIA  ⊂-step? QF-UF     = no (λ ())
QF-UFLIA  ⊂-step? QF-UFLRA  = no (λ ())
QF-UFLIA  ⊂-step? UFLRA     = no (λ ())
QF-UFLIA  ⊂-step? QF-UFNRA  = no (λ ())
QF-UFLIA  ⊂-step? QF-UFBV   = no (λ ())
QF-UFLIA  ⊂-step? QF-AUFBV  = no (λ ())
QF-UFLIA  ⊂-step? QF-BV     = no (λ ())
QF-UFLIA  ⊂-step? QF-ABV    = no (λ ())
QF-UFLIA  ⊂-step? QF-RDL    = no (λ ())
QF-UFLIA  ⊂-step? QF-LRA    = no (λ ())
QF-UFLIA  ⊂-step? NRA       = no (λ ())
QF-UFLIA  ⊂-step? LRA       = no (λ ())
QF-UFLIA  ⊂-step? QF-NRA    = no (λ ())
QF-UFNIA  ⊂-step? QF-AX     = no (λ ())
QF-UFNIA  ⊂-step? QF-IDL    = no (λ ())
QF-UFNIA  ⊂-step? QF-LIA    = no (λ ())
QF-UFNIA  ⊂-step? QF-NIA    = no (λ ())
QF-UFNIA  ⊂-step? NIA       = no (λ ())
QF-UFNIA  ⊂-step? UFNIA     = yes QF-UFNIA⊂-stepUFNIA
QF-UFNIA  ⊂-step? AUFNIRA   = no (λ ())
QF-UFNIA  ⊂-step? LIA       = no (λ ())
QF-UFNIA  ⊂-step? AUFLIRA   = no (λ ())
QF-UFNIA  ⊂-step? ALIA      = no (λ ())
QF-UFNIA  ⊂-step? AUFLIA    = no (λ ())
QF-UFNIA  ⊂-step? QF-ALIA   = no (λ ())
QF-UFNIA  ⊂-step? QF-AUFLIA = no (λ ())
QF-UFNIA  ⊂-step? QF-UFIDL  = no (λ ())
QF-UFNIA  ⊂-step? QF-UFLIA  = no (λ ())
QF-UFNIA  ⊂-step? QF-UFNIA  = no (λ ())
QF-UFNIA  ⊂-step? QF-UF     = no (λ ())
QF-UFNIA  ⊂-step? QF-UFLRA  = no (λ ())
QF-UFNIA  ⊂-step? UFLRA     = no (λ ())
QF-UFNIA  ⊂-step? QF-UFNRA  = no (λ ())
QF-UFNIA  ⊂-step? QF-UFBV   = no (λ ())
QF-UFNIA  ⊂-step? QF-AUFBV  = no (λ ())
QF-UFNIA  ⊂-step? QF-BV     = no (λ ())
QF-UFNIA  ⊂-step? QF-ABV    = no (λ ())
QF-UFNIA  ⊂-step? QF-RDL    = no (λ ())
QF-UFNIA  ⊂-step? QF-LRA    = no (λ ())
QF-UFNIA  ⊂-step? NRA       = no (λ ())
QF-UFNIA  ⊂-step? LRA       = no (λ ())
QF-UFNIA  ⊂-step? QF-NRA    = no (λ ())
QF-UF     ⊂-step? QF-AX     = no (λ ())
QF-UF     ⊂-step? QF-IDL    = no (λ ())
QF-UF     ⊂-step? QF-LIA    = no (λ ())
QF-UF     ⊂-step? QF-NIA    = no (λ ())
QF-UF     ⊂-step? NIA       = no (λ ())
QF-UF     ⊂-step? UFNIA     = no (λ ())
QF-UF     ⊂-step? AUFNIRA   = no (λ ())
QF-UF     ⊂-step? LIA       = no (λ ())
QF-UF     ⊂-step? AUFLIRA   = no (λ ())
QF-UF     ⊂-step? ALIA      = no (λ ())
QF-UF     ⊂-step? AUFLIA    = no (λ ())
QF-UF     ⊂-step? QF-ALIA   = no (λ ())
QF-UF     ⊂-step? QF-AUFLIA = no (λ ())
QF-UF     ⊂-step? QF-UFIDL  = yes QF-UF⊂-stepQF-UFIDL
QF-UF     ⊂-step? QF-UFLIA  = no (λ ())
QF-UF     ⊂-step? QF-UFNIA  = no (λ ())
QF-UF     ⊂-step? QF-UF     = no (λ ())
QF-UF     ⊂-step? QF-UFLRA  = yes QF-UF⊂-stepQF-UFLRA
QF-UF     ⊂-step? UFLRA     = no (λ ())
QF-UF     ⊂-step? QF-UFNRA  = no (λ ())
QF-UF     ⊂-step? QF-UFBV   = yes QF-UF⊂-stepQF-UFBV
QF-UF     ⊂-step? QF-AUFBV  = no (λ ())
QF-UF     ⊂-step? QF-BV     = no (λ ())
QF-UF     ⊂-step? QF-ABV    = no (λ ())
QF-UF     ⊂-step? QF-RDL    = no (λ ())
QF-UF     ⊂-step? QF-LRA    = no (λ ())
QF-UF     ⊂-step? NRA       = no (λ ())
QF-UF     ⊂-step? LRA       = no (λ ())
QF-UF     ⊂-step? QF-NRA    = no (λ ())
QF-UFLRA  ⊂-step? QF-AX     = no (λ ())
QF-UFLRA  ⊂-step? QF-IDL    = no (λ ())
QF-UFLRA  ⊂-step? QF-LIA    = no (λ ())
QF-UFLRA  ⊂-step? QF-NIA    = no (λ ())
QF-UFLRA  ⊂-step? NIA       = no (λ ())
QF-UFLRA  ⊂-step? UFNIA     = no (λ ())
QF-UFLRA  ⊂-step? AUFNIRA   = no (λ ())
QF-UFLRA  ⊂-step? LIA       = no (λ ())
QF-UFLRA  ⊂-step? AUFLIRA   = no (λ ())
QF-UFLRA  ⊂-step? ALIA      = no (λ ())
QF-UFLRA  ⊂-step? AUFLIA    = no (λ ())
QF-UFLRA  ⊂-step? QF-ALIA   = no (λ ())
QF-UFLRA  ⊂-step? QF-AUFLIA = no (λ ())
QF-UFLRA  ⊂-step? QF-UFIDL  = no (λ ())
QF-UFLRA  ⊂-step? QF-UFLIA  = no (λ ())
QF-UFLRA  ⊂-step? QF-UFNIA  = no (λ ())
QF-UFLRA  ⊂-step? QF-UF     = no (λ ())
QF-UFLRA  ⊂-step? QF-UFLRA  = no (λ ())
QF-UFLRA  ⊂-step? UFLRA     = yes QF-UFLRA⊂-stepUFLRA
QF-UFLRA  ⊂-step? QF-UFNRA  = yes QF-UFLRA⊂-stepQF-UFNRA
QF-UFLRA  ⊂-step? QF-UFBV   = no (λ ())
QF-UFLRA  ⊂-step? QF-AUFBV  = no (λ ())
QF-UFLRA  ⊂-step? QF-BV     = no (λ ())
QF-UFLRA  ⊂-step? QF-ABV    = no (λ ())
QF-UFLRA  ⊂-step? QF-RDL    = no (λ ())
QF-UFLRA  ⊂-step? QF-LRA    = no (λ ())
QF-UFLRA  ⊂-step? NRA       = no (λ ())
QF-UFLRA  ⊂-step? LRA       = no (λ ())
QF-UFLRA  ⊂-step? QF-NRA    = no (λ ())
UFLRA     ⊂-step? QF-AX     = no (λ ())
UFLRA     ⊂-step? QF-IDL    = no (λ ())
UFLRA     ⊂-step? QF-LIA    = no (λ ())
UFLRA     ⊂-step? QF-NIA    = no (λ ())
UFLRA     ⊂-step? NIA       = no (λ ())
UFLRA     ⊂-step? UFNIA     = no (λ ())
UFLRA     ⊂-step? AUFNIRA   = no (λ ())
UFLRA     ⊂-step? LIA       = no (λ ())
UFLRA     ⊂-step? AUFLIRA   = yes UFLRA⊂-stepAUFLIRA
UFLRA     ⊂-step? ALIA      = no (λ ())
UFLRA     ⊂-step? AUFLIA    = no (λ ())
UFLRA     ⊂-step? QF-ALIA   = no (λ ())
UFLRA     ⊂-step? QF-AUFLIA = no (λ ())
UFLRA     ⊂-step? QF-UFIDL  = no (λ ())
UFLRA     ⊂-step? QF-UFLIA  = no (λ ())
UFLRA     ⊂-step? QF-UFNIA  = no (λ ())
UFLRA     ⊂-step? QF-UF     = no (λ ())
UFLRA     ⊂-step? QF-UFLRA  = no (λ ())
UFLRA     ⊂-step? UFLRA     = no (λ ())
UFLRA     ⊂-step? QF-UFNRA  = no (λ ())
UFLRA     ⊂-step? QF-UFBV   = no (λ ())
UFLRA     ⊂-step? QF-AUFBV  = no (λ ())
UFLRA     ⊂-step? QF-BV     = no (λ ())
UFLRA     ⊂-step? QF-ABV    = no (λ ())
UFLRA     ⊂-step? QF-RDL    = no (λ ())
UFLRA     ⊂-step? QF-LRA    = no (λ ())
UFLRA     ⊂-step? NRA       = no (λ ())
UFLRA     ⊂-step? LRA       = no (λ ())
UFLRA     ⊂-step? QF-NRA    = no (λ ())
QF-UFNRA  ⊂-step? QF-AX     = no (λ ())
QF-UFNRA  ⊂-step? QF-IDL    = no (λ ())
QF-UFNRA  ⊂-step? QF-LIA    = no (λ ())
QF-UFNRA  ⊂-step? QF-NIA    = no (λ ())
QF-UFNRA  ⊂-step? NIA       = no (λ ())
QF-UFNRA  ⊂-step? UFNIA     = no (λ ())
QF-UFNRA  ⊂-step? AUFNIRA   = yes QF-UFNRA⊂-stepAUFNIRA
QF-UFNRA  ⊂-step? LIA       = no (λ ())
QF-UFNRA  ⊂-step? AUFLIRA   = no (λ ())
QF-UFNRA  ⊂-step? ALIA      = no (λ ())
QF-UFNRA  ⊂-step? AUFLIA    = no (λ ())
QF-UFNRA  ⊂-step? QF-ALIA   = no (λ ())
QF-UFNRA  ⊂-step? QF-AUFLIA = no (λ ())
QF-UFNRA  ⊂-step? QF-UFIDL  = no (λ ())
QF-UFNRA  ⊂-step? QF-UFLIA  = no (λ ())
QF-UFNRA  ⊂-step? QF-UFNIA  = no (λ ())
QF-UFNRA  ⊂-step? QF-UF     = no (λ ())
QF-UFNRA  ⊂-step? QF-UFLRA  = no (λ ())
QF-UFNRA  ⊂-step? UFLRA     = no (λ ())
QF-UFNRA  ⊂-step? QF-UFNRA  = no (λ ())
QF-UFNRA  ⊂-step? QF-UFBV   = no (λ ())
QF-UFNRA  ⊂-step? QF-AUFBV  = no (λ ())
QF-UFNRA  ⊂-step? QF-BV     = no (λ ())
QF-UFNRA  ⊂-step? QF-ABV    = no (λ ())
QF-UFNRA  ⊂-step? QF-RDL    = no (λ ())
QF-UFNRA  ⊂-step? QF-LRA    = no (λ ())
QF-UFNRA  ⊂-step? NRA       = no (λ ())
QF-UFNRA  ⊂-step? LRA       = no (λ ())
QF-UFNRA  ⊂-step? QF-NRA    = no (λ ())
QF-UFBV   ⊂-step? QF-AX     = no (λ ())
QF-UFBV   ⊂-step? QF-IDL    = no (λ ())
QF-UFBV   ⊂-step? QF-LIA    = no (λ ())
QF-UFBV   ⊂-step? QF-NIA    = no (λ ())
QF-UFBV   ⊂-step? NIA       = no (λ ())
QF-UFBV   ⊂-step? UFNIA     = no (λ ())
QF-UFBV   ⊂-step? AUFNIRA   = no (λ ())
QF-UFBV   ⊂-step? LIA       = no (λ ())
QF-UFBV   ⊂-step? AUFLIRA   = no (λ ())
QF-UFBV   ⊂-step? ALIA      = no (λ ())
QF-UFBV   ⊂-step? AUFLIA    = no (λ ())
QF-UFBV   ⊂-step? QF-ALIA   = no (λ ())
QF-UFBV   ⊂-step? QF-AUFLIA = no (λ ())
QF-UFBV   ⊂-step? QF-UFIDL  = no (λ ())
QF-UFBV   ⊂-step? QF-UFLIA  = no (λ ())
QF-UFBV   ⊂-step? QF-UFNIA  = no (λ ())
QF-UFBV   ⊂-step? QF-UF     = no (λ ())
QF-UFBV   ⊂-step? QF-UFLRA  = no (λ ())
QF-UFBV   ⊂-step? UFLRA     = no (λ ())
QF-UFBV   ⊂-step? QF-UFNRA  = no (λ ())
QF-UFBV   ⊂-step? QF-UFBV   = no (λ ())
QF-UFBV   ⊂-step? QF-AUFBV  = yes QF-UFBV⊂-stepQF-AUFBV
QF-UFBV   ⊂-step? QF-BV     = no (λ ())
QF-UFBV   ⊂-step? QF-ABV    = no (λ ())
QF-UFBV   ⊂-step? QF-RDL    = no (λ ())
QF-UFBV   ⊂-step? QF-LRA    = no (λ ())
QF-UFBV   ⊂-step? NRA       = no (λ ())
QF-UFBV   ⊂-step? LRA       = no (λ ())
QF-UFBV   ⊂-step? QF-NRA    = no (λ ())
QF-AUFBV  ⊂-step? QF-AX     = no (λ ())
QF-AUFBV  ⊂-step? QF-IDL    = no (λ ())
QF-AUFBV  ⊂-step? QF-LIA    = no (λ ())
QF-AUFBV  ⊂-step? QF-NIA    = no (λ ())
QF-AUFBV  ⊂-step? NIA       = no (λ ())
QF-AUFBV  ⊂-step? UFNIA     = no (λ ())
QF-AUFBV  ⊂-step? AUFNIRA   = no (λ ())
QF-AUFBV  ⊂-step? LIA       = no (λ ())
QF-AUFBV  ⊂-step? AUFLIRA   = no (λ ())
QF-AUFBV  ⊂-step? ALIA      = no (λ ())
QF-AUFBV  ⊂-step? AUFLIA    = no (λ ())
QF-AUFBV  ⊂-step? QF-ALIA   = no (λ ())
QF-AUFBV  ⊂-step? QF-AUFLIA = no (λ ())
QF-AUFBV  ⊂-step? QF-UFIDL  = no (λ ())
QF-AUFBV  ⊂-step? QF-UFLIA  = no (λ ())
QF-AUFBV  ⊂-step? QF-UFNIA  = no (λ ())
QF-AUFBV  ⊂-step? QF-UF     = no (λ ())
QF-AUFBV  ⊂-step? QF-UFLRA  = no (λ ())
QF-AUFBV  ⊂-step? UFLRA     = no (λ ())
QF-AUFBV  ⊂-step? QF-UFNRA  = no (λ ())
QF-AUFBV  ⊂-step? QF-UFBV   = no (λ ())
QF-AUFBV  ⊂-step? QF-AUFBV  = no (λ ())
QF-AUFBV  ⊂-step? QF-BV     = no (λ ())
QF-AUFBV  ⊂-step? QF-ABV    = no (λ ())
QF-AUFBV  ⊂-step? QF-RDL    = no (λ ())
QF-AUFBV  ⊂-step? QF-LRA    = no (λ ())
QF-AUFBV  ⊂-step? NRA       = no (λ ())
QF-AUFBV  ⊂-step? LRA       = no (λ ())
QF-AUFBV  ⊂-step? QF-NRA    = no (λ ())
QF-BV     ⊂-step? QF-AX     = no (λ ())
QF-BV     ⊂-step? QF-IDL    = no (λ ())
QF-BV     ⊂-step? QF-LIA    = no (λ ())
QF-BV     ⊂-step? QF-NIA    = no (λ ())
QF-BV     ⊂-step? NIA       = no (λ ())
QF-BV     ⊂-step? UFNIA     = no (λ ())
QF-BV     ⊂-step? AUFNIRA   = no (λ ())
QF-BV     ⊂-step? LIA       = no (λ ())
QF-BV     ⊂-step? AUFLIRA   = no (λ ())
QF-BV     ⊂-step? ALIA      = no (λ ())
QF-BV     ⊂-step? AUFLIA    = no (λ ())
QF-BV     ⊂-step? QF-ALIA   = no (λ ())
QF-BV     ⊂-step? QF-AUFLIA = no (λ ())
QF-BV     ⊂-step? QF-UFIDL  = no (λ ())
QF-BV     ⊂-step? QF-UFLIA  = no (λ ())
QF-BV     ⊂-step? QF-UFNIA  = no (λ ())
QF-BV     ⊂-step? QF-UF     = no (λ ())
QF-BV     ⊂-step? QF-UFLRA  = no (λ ())
QF-BV     ⊂-step? UFLRA     = no (λ ())
QF-BV     ⊂-step? QF-UFNRA  = no (λ ())
QF-BV     ⊂-step? QF-UFBV   = yes QF-BV⊂-stepQF-UFBV
QF-BV     ⊂-step? QF-AUFBV  = no (λ ())
QF-BV     ⊂-step? QF-BV     = no (λ ())
QF-BV     ⊂-step? QF-ABV    = yes QF-BV⊂-stepQF-ABV
QF-BV     ⊂-step? QF-RDL    = no (λ ())
QF-BV     ⊂-step? QF-LRA    = no (λ ())
QF-BV     ⊂-step? NRA       = no (λ ())
QF-BV     ⊂-step? LRA       = no (λ ())
QF-BV     ⊂-step? QF-NRA    = no (λ ())
QF-ABV    ⊂-step? QF-AX     = no (λ ())
QF-ABV    ⊂-step? QF-IDL    = no (λ ())
QF-ABV    ⊂-step? QF-LIA    = no (λ ())
QF-ABV    ⊂-step? QF-NIA    = no (λ ())
QF-ABV    ⊂-step? NIA       = no (λ ())
QF-ABV    ⊂-step? UFNIA     = no (λ ())
QF-ABV    ⊂-step? AUFNIRA   = no (λ ())
QF-ABV    ⊂-step? LIA       = no (λ ())
QF-ABV    ⊂-step? AUFLIRA   = no (λ ())
QF-ABV    ⊂-step? ALIA      = no (λ ())
QF-ABV    ⊂-step? AUFLIA    = no (λ ())
QF-ABV    ⊂-step? QF-ALIA   = no (λ ())
QF-ABV    ⊂-step? QF-AUFLIA = no (λ ())
QF-ABV    ⊂-step? QF-UFIDL  = no (λ ())
QF-ABV    ⊂-step? QF-UFLIA  = no (λ ())
QF-ABV    ⊂-step? QF-UFNIA  = no (λ ())
QF-ABV    ⊂-step? QF-UF     = no (λ ())
QF-ABV    ⊂-step? QF-UFLRA  = no (λ ())
QF-ABV    ⊂-step? UFLRA     = no (λ ())
QF-ABV    ⊂-step? QF-UFNRA  = no (λ ())
QF-ABV    ⊂-step? QF-UFBV   = no (λ ())
QF-ABV    ⊂-step? QF-AUFBV  = yes QF-ABV⊂-stepQF-AUFBV
QF-ABV    ⊂-step? QF-BV     = no (λ ())
QF-ABV    ⊂-step? QF-ABV    = no (λ ())
QF-ABV    ⊂-step? QF-RDL    = no (λ ())
QF-ABV    ⊂-step? QF-LRA    = no (λ ())
QF-ABV    ⊂-step? NRA       = no (λ ())
QF-ABV    ⊂-step? LRA       = no (λ ())
QF-ABV    ⊂-step? QF-NRA    = no (λ ())
QF-RDL    ⊂-step? QF-AX     = no (λ ())
QF-RDL    ⊂-step? QF-IDL    = no (λ ())
QF-RDL    ⊂-step? QF-LIA    = no (λ ())
QF-RDL    ⊂-step? QF-NIA    = no (λ ())
QF-RDL    ⊂-step? NIA       = no (λ ())
QF-RDL    ⊂-step? UFNIA     = no (λ ())
QF-RDL    ⊂-step? AUFNIRA   = no (λ ())
QF-RDL    ⊂-step? LIA       = no (λ ())
QF-RDL    ⊂-step? AUFLIRA   = no (λ ())
QF-RDL    ⊂-step? ALIA      = no (λ ())
QF-RDL    ⊂-step? AUFLIA    = no (λ ())
QF-RDL    ⊂-step? QF-ALIA   = no (λ ())
QF-RDL    ⊂-step? QF-AUFLIA = no (λ ())
QF-RDL    ⊂-step? QF-UFIDL  = no (λ ())
QF-RDL    ⊂-step? QF-UFLIA  = no (λ ())
QF-RDL    ⊂-step? QF-UFNIA  = no (λ ())
QF-RDL    ⊂-step? QF-UF     = no (λ ())
QF-RDL    ⊂-step? QF-UFLRA  = no (λ ())
QF-RDL    ⊂-step? UFLRA     = no (λ ())
QF-RDL    ⊂-step? QF-UFNRA  = no (λ ())
QF-RDL    ⊂-step? QF-UFBV   = no (λ ())
QF-RDL    ⊂-step? QF-AUFBV  = no (λ ())
QF-RDL    ⊂-step? QF-BV     = no (λ ())
QF-RDL    ⊂-step? QF-ABV    = no (λ ())
QF-RDL    ⊂-step? QF-RDL    = no (λ ())
QF-RDL    ⊂-step? QF-LRA    = yes QF-RDL⊂-stepQF-LRA
QF-RDL    ⊂-step? NRA       = no (λ ())
QF-RDL    ⊂-step? LRA       = no (λ ())
QF-RDL    ⊂-step? QF-NRA    = no (λ ())
QF-LRA    ⊂-step? QF-AX     = no (λ ())
QF-LRA    ⊂-step? QF-IDL    = no (λ ())
QF-LRA    ⊂-step? QF-LIA    = no (λ ())
QF-LRA    ⊂-step? QF-NIA    = no (λ ())
QF-LRA    ⊂-step? NIA       = no (λ ())
QF-LRA    ⊂-step? UFNIA     = no (λ ())
QF-LRA    ⊂-step? AUFNIRA   = no (λ ())
QF-LRA    ⊂-step? LIA       = no (λ ())
QF-LRA    ⊂-step? AUFLIRA   = no (λ ())
QF-LRA    ⊂-step? ALIA      = no (λ ())
QF-LRA    ⊂-step? AUFLIA    = no (λ ())
QF-LRA    ⊂-step? QF-ALIA   = no (λ ())
QF-LRA    ⊂-step? QF-AUFLIA = no (λ ())
QF-LRA    ⊂-step? QF-UFIDL  = no (λ ())
QF-LRA    ⊂-step? QF-UFLIA  = no (λ ())
QF-LRA    ⊂-step? QF-UFNIA  = no (λ ())
QF-LRA    ⊂-step? QF-UF     = no (λ ())
QF-LRA    ⊂-step? QF-UFLRA  = no (λ ())
QF-LRA    ⊂-step? UFLRA     = no (λ ())
QF-LRA    ⊂-step? QF-UFNRA  = yes QF-LRA⊂-stepQF-UFNRA
QF-LRA    ⊂-step? QF-UFBV   = no (λ ())
QF-LRA    ⊂-step? QF-AUFBV  = no (λ ())
QF-LRA    ⊂-step? QF-BV     = no (λ ())
QF-LRA    ⊂-step? QF-ABV    = no (λ ())
QF-LRA    ⊂-step? QF-RDL    = no (λ ())
QF-LRA    ⊂-step? QF-LRA    = no (λ ())
QF-LRA    ⊂-step? NRA       = no (λ ())
QF-LRA    ⊂-step? LRA       = yes QF-LRA⊂-stepLRA
QF-LRA    ⊂-step? QF-NRA    = yes QF-LRA⊂-stepQF-NRA
NRA       ⊂-step? QF-AX     = no (λ ())
NRA       ⊂-step? QF-IDL    = no (λ ())
NRA       ⊂-step? QF-LIA    = no (λ ())
NRA       ⊂-step? QF-NIA    = no (λ ())
NRA       ⊂-step? NIA       = no (λ ())
NRA       ⊂-step? UFNIA     = no (λ ())
NRA       ⊂-step? AUFNIRA   = yes NRA⊂-stepAUFNIRA
NRA       ⊂-step? LIA       = no (λ ())
NRA       ⊂-step? AUFLIRA   = no (λ ())
NRA       ⊂-step? ALIA      = no (λ ())
NRA       ⊂-step? AUFLIA    = no (λ ())
NRA       ⊂-step? QF-ALIA   = no (λ ())
NRA       ⊂-step? QF-AUFLIA = no (λ ())
NRA       ⊂-step? QF-UFIDL  = no (λ ())
NRA       ⊂-step? QF-UFLIA  = no (λ ())
NRA       ⊂-step? QF-UFNIA  = no (λ ())
NRA       ⊂-step? QF-UF     = no (λ ())
NRA       ⊂-step? QF-UFLRA  = no (λ ())
NRA       ⊂-step? UFLRA     = no (λ ())
NRA       ⊂-step? QF-UFNRA  = no (λ ())
NRA       ⊂-step? QF-UFBV   = no (λ ())
NRA       ⊂-step? QF-AUFBV  = no (λ ())
NRA       ⊂-step? QF-BV     = no (λ ())
NRA       ⊂-step? QF-ABV    = no (λ ())
NRA       ⊂-step? QF-RDL    = no (λ ())
NRA       ⊂-step? QF-LRA    = no (λ ())
NRA       ⊂-step? NRA       = no (λ ())
NRA       ⊂-step? LRA       = no (λ ())
NRA       ⊂-step? QF-NRA    = no (λ ())
LRA       ⊂-step? QF-AX     = no (λ ())
LRA       ⊂-step? QF-IDL    = no (λ ())
LRA       ⊂-step? QF-LIA    = no (λ ())
LRA       ⊂-step? QF-NIA    = no (λ ())
LRA       ⊂-step? NIA       = no (λ ())
LRA       ⊂-step? UFNIA     = no (λ ())
LRA       ⊂-step? AUFNIRA   = no (λ ())
LRA       ⊂-step? LIA       = no (λ ())
LRA       ⊂-step? AUFLIRA   = no (λ ())
LRA       ⊂-step? ALIA      = no (λ ())
LRA       ⊂-step? AUFLIA    = no (λ ())
LRA       ⊂-step? QF-ALIA   = no (λ ())
LRA       ⊂-step? QF-AUFLIA = no (λ ())
LRA       ⊂-step? QF-UFIDL  = no (λ ())
LRA       ⊂-step? QF-UFLIA  = no (λ ())
LRA       ⊂-step? QF-UFNIA  = no (λ ())
LRA       ⊂-step? QF-UF     = no (λ ())
LRA       ⊂-step? QF-UFLRA  = no (λ ())
LRA       ⊂-step? UFLRA     = yes LRA⊂-stepUFLRA
LRA       ⊂-step? QF-UFNRA  = no (λ ())
LRA       ⊂-step? QF-UFBV   = no (λ ())
LRA       ⊂-step? QF-AUFBV  = no (λ ())
LRA       ⊂-step? QF-BV     = no (λ ())
LRA       ⊂-step? QF-ABV    = no (λ ())
LRA       ⊂-step? QF-RDL    = no (λ ())
LRA       ⊂-step? QF-LRA    = no (λ ())
LRA       ⊂-step? NRA       = yes LRA⊂-stepNRA
LRA       ⊂-step? LRA       = no (λ ())
LRA       ⊂-step? QF-NRA    = no (λ ())
QF-NRA    ⊂-step? QF-AX     = no (λ ())
QF-NRA    ⊂-step? QF-IDL    = no (λ ())
QF-NRA    ⊂-step? QF-LIA    = no (λ ())
QF-NRA    ⊂-step? QF-NIA    = no (λ ())
QF-NRA    ⊂-step? NIA       = no (λ ())
QF-NRA    ⊂-step? UFNIA     = no (λ ())
QF-NRA    ⊂-step? AUFNIRA   = no (λ ())
QF-NRA    ⊂-step? LIA       = no (λ ())
QF-NRA    ⊂-step? AUFLIRA   = no (λ ())
QF-NRA    ⊂-step? ALIA      = no (λ ())
QF-NRA    ⊂-step? AUFLIA    = no (λ ())
QF-NRA    ⊂-step? QF-ALIA   = no (λ ())
QF-NRA    ⊂-step? QF-AUFLIA = no (λ ())
QF-NRA    ⊂-step? QF-UFIDL  = no (λ ())
QF-NRA    ⊂-step? QF-UFLIA  = no (λ ())
QF-NRA    ⊂-step? QF-UFNIA  = no (λ ())
QF-NRA    ⊂-step? QF-UF     = no (λ ())
QF-NRA    ⊂-step? QF-UFLRA  = no (λ ())
QF-NRA    ⊂-step? UFLRA     = no (λ ())
QF-NRA    ⊂-step? QF-UFNRA  = no (λ ())
QF-NRA    ⊂-step? QF-UFBV   = no (λ ())
QF-NRA    ⊂-step? QF-AUFBV  = no (λ ())
QF-NRA    ⊂-step? QF-BV     = no (λ ())
QF-NRA    ⊂-step? QF-ABV    = no (λ ())
QF-NRA    ⊂-step? QF-RDL    = no (λ ())
QF-NRA    ⊂-step? QF-LRA    = no (λ ())
QF-NRA    ⊂-step? NRA       = yes QF-NRA⊂-stepNRA
QF-NRA    ⊂-step? LRA       = no (λ ())
QF-NRA    ⊂-step? QF-NRA    = no (λ ())
