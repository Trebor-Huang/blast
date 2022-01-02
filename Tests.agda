{-# OPTIONS -vBlast.done:12 #-}
module Tests where
open import Blast
open import Tactics
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Data.Vec.Base
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Base

test1 : Nat × List Nat -> Vec Nat 3 × Set1 -> Set1 ⊎ (List Nat × Set)
test1 u v =
    by!  destruct×
    >==> split⊎  -- Here a backtracking is introduced.
    >==> perhaps split×
    >==> assumption

test2 : Nat ⊎ (Set × Nat) -> Nat ⊎ Set
test2 u =
    by!  ♯ (onContext destruct⊎′)
    >==> destruct×
    >==> split⊎
    >==> assumption

test' : Set
test' = sorry!
