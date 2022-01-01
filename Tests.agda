{-# OPTIONS -vBlast.done:12 #-}
module Tests where
open import Blast
open import Tactics
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Data.Vec.Base
open import Data.Product

test : Nat × List Nat -> Vec Nat 3 × Set -> Nat × Set
test u v = by! ♯ (local destruct×) >==> ♯ split× >==> ♮ assumption
-- This produces the term
-- λ u v → proj₁ u , proj₂ v

