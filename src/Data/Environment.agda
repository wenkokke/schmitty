module Data.Environment where

open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.List as List using (List; _∷_; [])
open import Data.Product as Prod using (_×_; _,_; uncurry)
open import Function using (const)
open import Reflection

private
  variable
    A    : Set
    x    : A
    xs   : List A
    T T′ : A → List A → Set

data Env (T : A → List A → Set) : List A → Set where
  []  : Env T []
  _∷_ : T x xs → Env T xs → Env T (x ∷ xs)

map : (f : ∀ {x xs} → T x xs → T′ x xs) → Env T xs → Env T′ xs
map _f []        = []
map  f (e ∷ env) = f e ∷ map f env

head : Env T (x ∷ xs) → T x xs
head (e ∷ _env) = e

tail : Env T (x ∷ xs) → Env T xs
tail (_e ∷ env) = env

lookupRest : (xs : List A) (i : Fin (List.length xs)) → A × List A
lookupRest (x ∷ xs) zero    = x , xs
lookupRest (x ∷ xs) (suc i) = lookupRest xs i

lookup : (env : Env T xs) (i : Fin (List.length xs)) → uncurry T (lookupRest xs i)
lookup []          ()
lookup ( e ∷ _env) zero    = e
lookup (_e ∷  env) (suc i) = lookup env i
