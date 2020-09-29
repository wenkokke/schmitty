
module Reflection.Annotated where

open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.Nat
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; _∷_; [])
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit
open import Function
open import Reflection
open import Reflection.Argument.Visibility
open import Category.Applicative
open import Algebra.Bundles

open import Reflection.Universe

private
  variable
    k   : Univ
    t   : ⟦ k ⟧
    Ann Ann₁ Ann₂ : ∀ {k} → ⟦ k ⟧ → Set

Typeₐ : Set → Set₁
Typeₐ A = (∀ {k} → ⟦ k ⟧ → Set) → A → Set

infixr 30 ⟨_⟩_
data ⟪_⟫ {k} (AnnTy : Typeₐ ⟦ k ⟧) : Typeₐ ⟦ k ⟧ where
  ⟨_⟩_ : ∀ {t} → Ann t → AnnTy Ann t → ⟪ AnnTy ⟫ Ann t

ann : {AnnTy : Typeₐ ⟦ k ⟧} → ⟪ AnnTy ⟫ Ann t → Ann t
ann (⟨ α ⟩ _) = α

Listₐ : Typeₐ ⟦ k ⟧ → Typeₐ (List ⟦ k ⟧)
Listₐ ElAnn Ann = All (ElAnn Ann)

data Absₐ′ (TyAnn : Typeₐ ⟦ k ⟧) : Typeₐ (Abs ⟦ k ⟧) where
  abs : ∀ x → TyAnn Ann t → Absₐ′ TyAnn Ann (abs x t)

data Argₐ′ (TyAnn : Typeₐ ⟦ k ⟧) : Typeₐ (Arg ⟦ k ⟧) where
  arg : ∀ i → TyAnn Ann t → Argₐ′ TyAnn Ann (arg i t)

data Namedₐ′ (TyAnn : Typeₐ ⟦ k ⟧) : Typeₐ (String × ⟦ k ⟧) where
  _,_ : ∀ x → TyAnn Ann t → Namedₐ′ TyAnn Ann (x , t)

Absₐ : Typeₐ ⟦ k ⟧ → Typeₐ (Abs ⟦ k ⟧)
Absₐ = ⟪_⟫ ∘ Absₐ′

Argₐ : Typeₐ ⟦ k ⟧ → Typeₐ (Arg ⟦ k ⟧)
Argₐ = ⟪_⟫ ∘ Argₐ′

Namedₐ : Typeₐ ⟦ k ⟧ → Typeₐ (String × ⟦ k ⟧)
Namedₐ = ⟪_⟫ ∘ Namedₐ′

Argsₐ′ : Typeₐ ⟦ k ⟧ → Typeₐ (Args ⟦ k ⟧)
Argsₐ′ = Listₐ ∘ Argₐ

Argsₐ : Typeₐ ⟦ k ⟧ → Typeₐ (Args ⟦ k ⟧)
Argsₐ = ⟪_⟫ ∘ Argsₐ′

mutual
  Termₐ : Typeₐ Term
  Termₐ = ⟪ Termₐ′ ⟫

  Patternₐ : Typeₐ Pattern
  Patternₐ = ⟪ Patternₐ′ ⟫

  Sortₐ : Typeₐ Sort
  Sortₐ = ⟪ Sortₐ′ ⟫

  Clauseₐ : Typeₐ Clause
  Clauseₐ = ⟪ Clauseₐ′ ⟫

  Clausesₐ : Typeₐ (List Clause)
  Clausesₐ = ⟪ Listₐ Clauseₐ ⟫

  Telₐ′ : Typeₐ (List (String × Arg Term))
  Telₐ′ = Listₐ (Namedₐ (Argₐ Termₐ))

  Telₐ : Typeₐ (List (String × Arg Term))
  Telₐ = ⟪ Telₐ′ ⟫

  data Termₐ′ : Typeₐ Term where
    var       : ∀ x {args} → Argsₐ Termₐ Ann args → Termₐ′ Ann (var x args)
    con       : ∀ c {args} → Argsₐ Termₐ Ann args → Termₐ′ Ann (con c args)
    def       : ∀ f {args} → Argsₐ Termₐ Ann args → Termₐ′ Ann (def f args)
    lam       : ∀ v {b}    → Absₐ  Termₐ Ann b    → Termₐ′ Ann (lam v b)
    pat-lam   : ∀ {cs args} →
                  Clausesₐ Ann cs → Argsₐ Termₐ Ann args →
                  Termₐ′ Ann (pat-lam cs args)
    pi        : ∀ {a b} →
                  Argₐ Termₐ Ann a → Absₐ Termₐ Ann b →
                  Termₐ′ Ann (pi a b)
    agda-sort : ∀ {s} → Sortₐ Ann s → Termₐ′ Ann (agda-sort s)
    lit       : ∀ l → Termₐ′ Ann (lit l)
    meta      : ∀ x {args} → Argsₐ Termₐ Ann args → Termₐ′ Ann (meta x args)
    unknown   : Termₐ′ Ann unknown

  data Clauseₐ′ (Ann : ∀ {k} → ⟦ k ⟧ → Set) : Clause → Set where
    clause        : ∀ {tel ps t} →
                      Telₐ Ann tel →
                      Argsₐ Patternₐ Ann ps →
                      Termₐ Ann t →
                      Clauseₐ′ Ann (Clause.clause tel ps t)
    absurd-clause : ∀ {tel ps} →
                      Telₐ Ann tel →
                      Argsₐ Patternₐ Ann ps →
                      Clauseₐ′ Ann (Clause.absurd-clause tel ps)

  data Sortₐ′ (Ann : ∀ {k} → ⟦ k ⟧ → Set) : Sort → Set where
    set     : ∀ {t} → Termₐ Ann t → Sortₐ′ Ann (Sort.set t)
    lit     : ∀ n → Sortₐ′ Ann (Sort.lit n)
    unknown : Sortₐ′ Ann Sort.unknown

  data Patternₐ′ (Ann : ∀ {k} → ⟦ k ⟧ → Set) : Pattern → Set where
    con    : ∀ c {ps} → Argsₐ Patternₐ Ann ps → Patternₐ′ Ann (Pattern.con c ps)
    dot    : ∀ {t} → Termₐ Ann t → Patternₐ′ Ann (Pattern.dot t)
    var    : ∀ x → Patternₐ′ Ann (Pattern.var x)
    lit    : ∀ l → Patternₐ′ Ann (Pattern.lit l)
    proj   : ∀ f → Patternₐ′ Ann (Pattern.proj f)
    absurd : Patternₐ′ Ann Pattern.absurd

mutual
  Annotated′ : ∀ {k} → Typeₐ ⟦ k ⟧
  Annotated′ {⟨term⟩}    = Termₐ′
  Annotated′ {⟨pat⟩}     = Patternₐ′
  Annotated′ {⟨sort⟩}    = Sortₐ′
  Annotated′ {⟨clause⟩}  = Clauseₐ′
  Annotated′ {⟨list⟩ k}  = Listₐ Annotated
  Annotated′ {⟨arg⟩ k}   = Argₐ′ Annotated
  Annotated′ {⟨abs⟩ k}   = Absₐ′ Annotated
  Annotated′ {⟨named⟩ k} = Namedₐ′ Annotated

  Annotated : Typeₐ ⟦ k ⟧
  Annotated = ⟪ Annotated′ ⟫

-- Mapping over annotations

mutual

  map′ : ∀ k → (∀ {k} {t : ⟦ k ⟧} → Ann₁ t → Ann₂ t) → {t : ⟦ k ⟧} → Annotated′ Ann₁ t → Annotated′ Ann₂ t
  map′ ⟨term⟩      f (var x args)         = var x (map f args)
  map′ ⟨term⟩      f (con c args)         = con c (map f args)
  map′ ⟨term⟩      f (def h args)         = def h (map f args)
  map′ ⟨term⟩      f (lam v b)            = lam v (map f b)
  map′ ⟨term⟩      f (pat-lam cs args)    = pat-lam (map f cs) (map f args)
  map′ ⟨term⟩      f (pi a b)             = pi (map f a) (map f b)
  map′ ⟨term⟩      f (agda-sort s)        = agda-sort (map f s)
  map′ ⟨term⟩      f (lit l)              = lit l
  map′ ⟨term⟩      f (meta x args)        = meta x (map f args)
  map′ ⟨term⟩      f unknown              = unknown
  map′ ⟨pat⟩       f (con c ps)           = con c (map f ps)
  map′ ⟨pat⟩       f (dot t)              = dot (map f t)
  map′ ⟨pat⟩       f (var x)              = var x
  map′ ⟨pat⟩       f (lit l)              = lit l
  map′ ⟨pat⟩       f (proj g)             = proj g
  map′ ⟨pat⟩       f absurd               = absurd
  map′ ⟨sort⟩      f (set t)              = set (map f t)
  map′ ⟨sort⟩      f (lit n)              = lit n
  map′ ⟨sort⟩      f unknown              = unknown
  map′ ⟨clause⟩    f (clause Γ ps args)   = clause (map f Γ) (map f ps) (map f args)
  map′ ⟨clause⟩    f (absurd-clause Γ ps) = absurd-clause (map f Γ) (map f ps)
  map′ (⟨list⟩ k)  f []                   = []
  map′ (⟨list⟩ k)  f (x ∷ xs)             = map f x ∷ map′ _ f xs
  map′ (⟨arg⟩ k)   f (arg i x)            = arg i (map f x)
  map′ (⟨abs⟩ k)   f (abs x t)            = abs x (map f t)
  map′ (⟨named⟩ k) f (x , t)              = x , map f t

  map : ∀ {k} → (∀ {k} {t : ⟦ k ⟧} → Ann₁ t → Ann₂ t) → {t : ⟦ k ⟧} → Annotated Ann₁ t → Annotated Ann₂ t
  map {k = k} f (⟨ α ⟩ t) = ⟨ f α ⟩ map′ k f t

AnnotationFun : (∀ {k} → ⟦ k ⟧ → Set) → Set
AnnotationFun Ann = ∀ k {t : ⟦ k ⟧} → Annotated′ Ann t → Ann t

module _ {Ann : ∀ {k} → ⟦ k ⟧ → Set} (buildAnn : AnnotationFun Ann) where

  private
    annotated : {t : ⟦ k ⟧} → Annotated′ Ann t → Annotated Ann t
    annotated ps = ⟨ buildAnn _ ps ⟩ ps

  mutual
    annotate′ : (t : ⟦ k ⟧) → Annotated′ Ann t
    annotate′ {⟨term⟩}   (var x args)                  = var x (annotate args)
    annotate′ {⟨term⟩}   (con c args)                  = con c (annotate args)
    annotate′ {⟨term⟩}   (def f args)                  = def f (annotate args)
    annotate′ {⟨term⟩}   (lam v t)                     = lam v (annotate t)
    annotate′ {⟨term⟩}   (pat-lam cs args)             = pat-lam (annotate cs) (annotate args)
    annotate′ {⟨term⟩}   (pi a b)                      = pi (annotate a) (annotate b)
    annotate′ {⟨term⟩}   (agda-sort s)                 = agda-sort (annotate s)
    annotate′ {⟨term⟩}   (lit l)                       = lit l
    annotate′ {⟨term⟩}   (meta x args)                 = meta x (annotate args)
    annotate′ {⟨term⟩}   unknown                       = unknown
    annotate′ {⟨pat⟩}    (Pattern.con c ps)            = con c (annotate ps)
    annotate′ {⟨pat⟩}    (Pattern.dot t)               = dot (annotate t)
    annotate′ {⟨pat⟩}    (Pattern.var x)               = var x
    annotate′ {⟨pat⟩}    (Pattern.lit l)               = lit l
    annotate′ {⟨pat⟩}    (Pattern.proj f)              = proj f
    annotate′ {⟨pat⟩}    Pattern.absurd                = absurd
    annotate′ {⟨sort⟩}   (Sort.set t)                  = set (annotate t)
    annotate′ {⟨sort⟩}   (Sort.lit n)                  = lit n
    annotate′ {⟨sort⟩}   Sort.unknown                  = unknown
    annotate′ {⟨clause⟩} (Clause.clause tel ps t)      = clause (annotate tel) (annotate ps) (annotate t)
    annotate′ {⟨clause⟩} (Clause.absurd-clause tel ps) = absurd-clause (annotate tel) (annotate ps)
    annotate′ {⟨abs⟩ k}  (abs x t)                     = abs x (annotate t)
    annotate′ {⟨arg⟩ k}  (arg i t)                     = arg i (annotate t)
    annotate′ {⟨list⟩ k} []                            = []
    annotate′ {⟨list⟩ k} (x ∷ xs)                      = annotate x ∷ annotate′ xs
    annotate′ {⟨named⟩ k} (x , t)                      = x , annotate t

    annotate : (t : ⟦ k ⟧) → Annotated Ann t
    annotate t = annotated (annotate′ t)

----------------------------------
-- Annotation function combinators

open import Level renaming (zero to lzero)

module _ {W : Set} (ε : W) (_∪_ : W → W → W) where

  -- This annotation function does nothing except combine ε's with _∪_.
  -- Can be combined with more interesting functions.
  defaultAnn : AnnotationFun (λ _ → W)
  defaultAnn ⟨term⟩      (var x args)         = ann args
  defaultAnn ⟨term⟩      (con c args)         = ann args
  defaultAnn ⟨term⟩      (def f args)         = ann args
  defaultAnn ⟨term⟩      (lam v b)            = ann b
  defaultAnn ⟨term⟩      (pat-lam cs args)    = ann cs ∪ ann args
  defaultAnn ⟨term⟩      (pi a b)             = ann a ∪ ann b
  defaultAnn ⟨term⟩      (agda-sort s)        = ann s
  defaultAnn ⟨term⟩      (lit l)              = ε
  defaultAnn ⟨term⟩      (meta x args)        = ann args
  defaultAnn ⟨term⟩      unknown              = ε
  defaultAnn ⟨pat⟩       (con c args)         = ann args
  defaultAnn ⟨pat⟩       (dot t)              = ann t
  defaultAnn ⟨pat⟩       (var x)              = ε
  defaultAnn ⟨pat⟩       (lit l)              = ε
  defaultAnn ⟨pat⟩       (proj f)             = ε
  defaultAnn ⟨pat⟩       absurd               = ε
  defaultAnn ⟨sort⟩      (set t)              = ann t
  defaultAnn ⟨sort⟩      (lit n)              = ε
  defaultAnn ⟨sort⟩      unknown              = ε
  defaultAnn ⟨clause⟩    (clause Γ ps t)      = ann Γ ∪ (ann ps ∪ ann t)
  defaultAnn ⟨clause⟩    (absurd-clause Γ ps) = ann Γ ∪ ann ps
  defaultAnn (⟨list⟩ k)  []                   = ε
  defaultAnn (⟨list⟩ k)  (x ∷ xs)             = ann x ∪ defaultAnn _ xs
  defaultAnn (⟨arg⟩ k)   (arg i x)            = ann x
  defaultAnn (⟨abs⟩ k)   (abs x t)            = ann t
  defaultAnn (⟨named⟩ k) (x , t)              = ann t

infixr 4 _⊗_
_⊗_ : AnnotationFun Ann₁ → AnnotationFun Ann₂ → AnnotationFun (λ t → Ann₁ t × Ann₂ t)
(f ⊗ g) k t = f k (map′ k proj₁ t) , g k (map′ k proj₂ t)

------------------------------
-- Annotation-driven traversal

module Traverse {M : Set → Set} (appl : RawApplicative M) where

  open RawApplicative appl renaming (_⊛_ to _<*>_)

  module _ (apply? : ∀ {k} {t : ⟦ k ⟧} → Ann t → Bool)
           (action : ∀ {k} {t : ⟦ k ⟧} → Annotated Ann t → M ⟦ k ⟧) where

    mutual
      traverse′ : ∀ {k} {t : ⟦ k ⟧} → Annotated′ Ann t → M ⟦ k ⟧
      traverse′ {⟨term⟩}    (var x args)         = var x <$> traverse args
      traverse′ {⟨term⟩}    (con c args)         = con c <$> traverse args
      traverse′ {⟨term⟩}    (def f args)         = def f <$> traverse args
      traverse′ {⟨term⟩}    (lam v b)            = lam v <$> traverse b
      traverse′ {⟨term⟩}    (pat-lam cs args)    = pat-lam <$> traverse cs <*> traverse args
      traverse′ {⟨term⟩}    (pi a b)             = pi <$> traverse a <*> traverse b
      traverse′ {⟨term⟩}    (agda-sort s)        = agda-sort <$> traverse s
      traverse′ {⟨term⟩}    (lit l)              = pure (lit l)
      traverse′ {⟨term⟩}    (meta x args)        = meta x <$> traverse args
      traverse′ {⟨term⟩}    unknown              = pure unknown
      traverse′ {⟨pat⟩}     (con c args)         = Pattern.con c <$> traverse args
      traverse′ {⟨pat⟩}     (dot t)              = Pattern.dot <$> traverse t
      traverse′ {⟨pat⟩}     (var x)              = pure (Pattern.var x)
      traverse′ {⟨pat⟩}     (lit l)              = pure (Pattern.lit l)
      traverse′ {⟨pat⟩}     (proj f)             = pure (Pattern.proj f)
      traverse′ {⟨pat⟩}     absurd               = pure Pattern.absurd
      traverse′ {⟨sort⟩}    (set t)              = Sort.set <$> traverse t
      traverse′ {⟨sort⟩}    (lit n)              = pure (Sort.lit n)
      traverse′ {⟨sort⟩}    unknown              = pure Sort.unknown
      traverse′ {⟨clause⟩}  (clause Γ ps t)      = Clause.clause <$> traverse Γ <*> traverse ps <*> traverse t
      traverse′ {⟨clause⟩}  (absurd-clause Γ ps) = Clause.absurd-clause <$> traverse Γ <*> traverse ps
      traverse′ {⟨list⟩ k}  []                   = pure []
      traverse′ {⟨list⟩ k}  (x ∷ xs)             = _∷_ <$> traverse x <*> traverse′ xs
      traverse′ {⟨arg⟩ k}   (arg i x)            = arg i <$> traverse x
      traverse′ {⟨abs⟩ k}   (abs x t)            = abs x <$> traverse t
      traverse′ {⟨named⟩ k} (x , t)              = x ,_ <$> traverse t

      traverse : ∀ {k} {t : ⟦ k ⟧} → Annotated Ann t → M ⟦ k ⟧
      traverse t@(⟨ α ⟩ tₐ) = if apply? α then action t else traverse′ tₐ
