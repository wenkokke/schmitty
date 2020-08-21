{-# OPTIONS --without-K --safe #-}

module SMT.Logics where

open import Data.String using (String)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import Relation.Binary.Construct.Closure.Transitive as Plus

-- |Logics supported by SMT-LIB 2.
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


infix 4 _⇾_

-- |The ⇾-relation encodes the edges of the inclusion graph for SMT-LIB 2.
data _⇾_ : (l₁ l₂ : Logic) → Set where
  QF-IDL⇾QF-LIA      : QF-IDL     ⇾ QF-LIA
  QF-LIA⇾QF-NIA      : QF-LIA     ⇾ QF-NIA
  QF-NIA⇾NIA         : QF-NIA     ⇾ NIA
  NIA⇾UFNIA          : NIA        ⇾ UFNIA
  UFNIA⇾AUFNIRA      : UFNIA      ⇾ AUFNIRA
  QF-LIA⇾LIA         : QF-LIA     ⇾ LIA
  LIA⇾NIA            : LIA        ⇾ NIA
  LIA⇾AUFLIRA        : LIA        ⇾ AUFLIRA
  AUFLIRA⇾AUFNIRA    : AUFLIRA    ⇾ AUFNIRA
  LIA⇾ALIA           : LIA        ⇾ ALIA
  ALIA⇾AUFLIA        : ALIA       ⇾ AUFLIA
  QF-LIA⇾QF-ALIA     : QF-LIA     ⇾ QF-ALIA
  QF-ALIA⇾ALIA       : QF-ALIA    ⇾ ALIA
  QF-ALIA⇾QF-AUFLIA  : QF-ALIA    ⇾ QF-AUFLIA
  QF-AUFLIA⇾AUFLIA   : QF-AUFLIA  ⇾ AUFLIA
  QF-LIA⇾QF-UFLIA    : QF-LIA     ⇾ QF-UFLIA
  QF-UFLIA⇾QF-AUFLIA : QF-UFLIA   ⇾ QF-AUFLIA
  QF-UFLIA⇾QF-UFNIA  : QF-UFLIA   ⇾ QF-UFNIA
  QF-UFNIA⇾UFNIA     : QF-UFNIA   ⇾ UFNIA
  QF-IDL⇾QF-UFIDL    : QF-IDL     ⇾ QF-UFIDL
  QF-UFIDL⇾QF-UFLIA  : QF-UFIDL   ⇾ QF-UFLIA
  QF-UF⇾QF-UFIDL     : QF-UF      ⇾ QF-UFIDL
  QF-UF⇾QF-UFLRA     : QF-UF      ⇾ QF-UFLRA
  QF-UFLRA⇾UFLRA     : QF-UFLRA   ⇾ UFLRA
  UFLRA⇾AUFLIRA      : UFLRA      ⇾ AUFLIRA
  QF-UFLRA⇾QF-UFNRA  : QF-UFLRA   ⇾ QF-UFNRA
  QF-UFNRA⇾AUFNIRA   : QF-UFNRA   ⇾ AUFNIRA
  QF-UF⇾QF-UFBV      : QF-UF      ⇾ QF-UFBV
  QF-UFBV⇾QF-AUFBV   : QF-UFBV    ⇾ QF-AUFBV
  QF-BV⇾QF-UFBV      : QF-BV      ⇾ QF-UFBV
  QF-BV⇾QF-ABV       : QF-BV      ⇾ QF-ABV
  QF-ABV⇾QF-AUFBV    : QF-ABV     ⇾ QF-AUFBV
  QF-RDL⇾QF-LRA      : QF-RDL     ⇾ QF-LRA
  QF-LRA⇾QF-UFNRA    : QF-LRA     ⇾ QF-UFNRA
  QF-LRA⇾LRA         : QF-LRA     ⇾ LRA
  LRA⇾UFLRA          : LRA        ⇾ UFLRA
  LRA⇾NRA            : LRA        ⇾ NRA
  NRA⇾AUFNIRA        : NRA        ⇾ AUFNIRA
  QF-LRA⇾QF-NRA      : QF-LRA     ⇾ QF-NRA
  QF-NRA⇾QF-UFNRA    : QF-NRA     ⇾ QF-UFNRA
  QF-NRA⇾NRA         : QF-NRA     ⇾ NRA

-- |The transitive closure of the ⇾-relation.
_⇾⁺_ : Rel Logic _
_⇾⁺_ = Plus.Plus′ _⇾_

open Plus public using ([_]; _∷_)


-- |Printing logics.
showLogic : Logic → String
showLogic QF-AX     = "QF_AX"
showLogic QF-IDL    = "QF_IDL"
showLogic QF-LIA    = "QF_LIA"
showLogic QF-NIA    = "QF_NIA"
showLogic NIA       = "NIA"
showLogic UFNIA     = "UFNIA"
showLogic AUFNIRA   = "AUFNIRA"
showLogic LIA       = "LIA"
showLogic AUFLIRA   = "AUFLIRA"
showLogic ALIA      = "ALIA"
showLogic AUFLIA    = "AUFLIA"
showLogic QF-ALIA   = "QF_ALIA"
showLogic QF-AUFLIA = "QF_AUFLIA"
showLogic QF-UFIDL  = "QF_UFIDL"
showLogic QF-UFLIA  = "QF_UFLIA"
showLogic QF-UFNIA  = "QF_UFNIA"
showLogic QF-UF     = "QF_UF"
showLogic QF-UFLRA  = "QF_UFLRA"
showLogic UFLRA     = "UFLRA"
showLogic QF-UFNRA  = "QF_UFNRA"
showLogic QF-UFBV   = "QF_UFBV"
showLogic QF-AUFBV  = "QF_AUFBV"
showLogic QF-BV     = "QF_BV"
showLogic QF-ABV    = "QF_ABV"
showLogic QF-RDL    = "QF_RDL"
showLogic QF-LRA    = "QF_LRA"
showLogic NRA       = "NRA"
showLogic LRA       = "LRA"
showLogic QF-NRA    = "QF_NRA"
