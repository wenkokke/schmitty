module Kanso.Boolean.TPTP where

open import Data.Bool using ()
open import Data.Nat using ()
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Kanso.Boolean.Formula

tptpformat : PL-Formula → String
tptpformat ¥true    = "$true"
tptpformat ¥false   = "$false"
tptpformat (¥ vid)  = "'" ++ (show vid)  ++ "'"
tptpformat (φ && ψ) = "(" ++ tptpformat φ ++ " & "  ++ tptpformat ψ ++ ")"
tptpformat (φ || ψ) = "(" ++ tptpformat φ ++ " | "  ++ tptpformat ψ ++ ")"
tptpformat (φ => ψ) = "(" ++ tptpformat φ ++ " => " ++ tptpformat ψ ++ ")"

tptp : PL-Formula → String
tptp φ = "fof(ax1,axiom," ++ tptpformat (~ φ) ++ ")."
