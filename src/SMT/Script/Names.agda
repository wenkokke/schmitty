open import SMT.Theory.Base

module SMT.Script.Names (baseTheory : BaseTheory) where

open BaseTheory baseTheory

open import Category.Monad
open import Category.Monad.State as StateCat using (RawIMonadState; IStateT)
open import Codata.Musical.Stream as Stream using (Stream)
open import Data.Char as Char using (Char)
open import Data.Environment as Env using (Env; _∷_; [])
open import Data.Fin as Fin using (Fin)
open import Data.List as List using (List; _∷_; []; _++_)
open import Data.List.Relation.Unary.All as All using (All; _∷_; [])
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_; _++⁺_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product as Prod using (∃; ∃-syntax; _×_; _,_; -,_; proj₁; proj₂)
open import Data.String as String using (String)
open import Data.Unit as Unit using (⊤)
open import Data.Vec as Vec using (Vec)
open import Function using (const; id; _∘_; _$_)
import Function.Identity.Categorical as Identity
open import Text.Parser.String as P hiding (_>>=_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Reflection using (con; vArg)
open import SMT.Script.Base baseTheory

private
  variable
    σ σ′ : Sort
    Γ Γ′ : Ctxt

-- |Names.
Name : Set
Name = List⁺ Char

-- |Show names.
showName : Name → String
showName = String.fromList ∘ List⁺.toList

-- |Name environments, i.e., lists where the types of the elements
--  are determined by a type-level list.
NameEnv : Ctxt → Set
NameEnv = Env (λ _ _ → Name)

-- |Name states, i.e., an environment of names, one for every
--  variable in the context Γ, and a supply  of fresh names.
--
--  NOTE: the current implementation does not guarantee that
--        each name in the supply is distinct. If we need this
--        in the future, there is `Data.List.Fresh`.
--
record Names (Γ : Ctxt) : Set where
  field
    nameEnv    : NameEnv Γ
    nameSupply : Stream Name

open Names -- bring `nameEnv` and `nameSupply` in scope

-- |Add a fresh name to the front of the name environment.
freshName : (n : String) (σ : Sort) → Names Γ → Name × Names (σ ∷ Γ)
freshName {Γ} n σ ns = n′ , ns′
  where
    n′ = String.toList n ++⁺ Stream.head (nameSupply ns)
    ns′ : Names (σ ∷ Γ)
    nameEnv    ns′ = n′ ∷ nameEnv ns
    nameSupply ns′ = Stream.tail (nameSupply ns)

-- |Remove first name from the name environment.
dropName : Names (σ ∷ Γ) → Names Γ
nameEnv    (dropName names) = Env.tail (nameEnv names)
nameSupply (dropName names) = nameSupply names

-- |A name state for the empty context, which supplies the names x0, x1, x2, ...
x′es : Names []
nameEnv    x′es = []
nameSupply x′es = Stream.map (λ n → '_' ∷ String.toList (showℕ n)) (Stream.iterate ℕ.suc 0)
