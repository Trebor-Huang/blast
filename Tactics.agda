{-# OPTIONS --safe --postfix-projections #-}
module Tactics where

open import Blast
open import Reflection
open import Data.List.Base
open import Data.Vec.Base using (Vec; _∷_; [])
open import Agda.Builtin.Nat
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Maybe
private
    -- we need these non-dependent versions to make them easier to quote
    -- but marking this as private makes C-c C-m useless
    fst : ∀ {a b} {A : Set a} {B : Set b} -> A × B -> A
    fst = proj₁
    snd : ∀ {a b} {A : Set a} {B : Set b} -> A × B -> B
    snd = proj₂
    _ʻ_ : ∀ {a b} {A : Set a} {B : Set b} -> A -> B -> A × B
    _ʻ_ = _,_

split×′ : Tactic
split×′ record
    { goal = def (quote _×_)
        (h₁ ∷ h₂ ∷ vArg ty₁ ∷ vArg ty₂ ∷ [])
    ; context = context } = [ record
    { #goal = 2
    ; goals = record { goal = ty₁ ; context = context }
            ∷ record { goal = ty₂ ; context = context }
            ∷ []
    ; thunk = \ { (t₁ ∷ t₂ ∷ []) ->
        def (quote _ʻ_) (h₁ ∷ h₂ ∷ hArg ty₁ ∷ hArg ty₂ ∷ vArg t₁ ∷ vArg t₂ ∷ [])} } ]
split×′ = fail

split× : Strategy
split× = ♮ split×′

split⊎₁′ : Tactic
split⊎₁′ record
    { goal = def (quote _⊎_)
        (h₁ ∷ h₂ ∷ vArg ty₁ ∷ vArg ty₂ ∷ [])
    ; context = context } = [ record
        { #goal = 1
        ; goals = record { goal = ty₁ ; context = context } ∷ []
        ; thunk = \ { (tm ∷ []) -> con (quote inj₁)
                (h₁ ∷ h₂ ∷ hArg ty₁ ∷ hArg ty₂ ∷ vArg tm ∷ [])} } ]
split⊎₁′ = fail

split⊎₂′ : Tactic
split⊎₂′ record
    { goal = def (quote _⊎_)
        (h₁ ∷ h₂ ∷ vArg ty₁ ∷ vArg ty₂ ∷ [])
    ; context = context } = [ record
        { #goal = 1
        ; goals = record { goal = ty₂ ; context = context } ∷ []
        ; thunk = \ { (tm ∷ []) -> con (quote inj₂)
                (h₁ ∷ h₂ ∷ hArg ty₁ ∷ hArg ty₂ ∷ vArg tm ∷ [])} } ]
split⊎₂′ = fail

split⊎ : Strategy
split⊎ = ♮ split⊎₁′ <~> ♮ split⊎₂′

private
    cartPower : ∀ {ℓ} {A : Set ℓ}
        -> List A -> (n : Nat) -> List (Vec A n)
    cartPower l zero = [] ∷ []
    cartPower l (suc n) = cartesianProductWith _∷_ l (cartPower l n)

-- Acts on local context to generate new terms
local′ : ∀ {n : Nat}
    -> (Vec (Type × Term) n -> List (Type × Term))
    -> Tactic
local′ {n = n} F record { goal = goal ; context = context } =
    [ simply record { goal = goal ; context = concatMap F (cartPower context n) } ]

local : ∀ {n : Nat}
    -> (Vec (Type × Term) n -> List (Type × Term))
    -> Strategy
local F = ♮ (local′ F)

-- Directly adds new term to context
pose′ : List (Type × Term) -> Tactic
pose′ ps record { goal = goal ; context = context }
    = [ simply record { goal = goal ; context = ps ++ context } ]

pose : List (Type × Term) -> Strategy
pose ps = ♮ (pose′ ps)

destruct× : Vec (Type × Term) 1 -> List (Type × Term)
destruct× ((def (quote _×_)
    (h₁ ∷ h₂ ∷ vArg ty₁ ∷ vArg ty₂ ∷ []) , tm) ∷ [])
    = (ty₁ , def (quote fst) (h₁ ∷ h₂ ∷ hArg ty₁ ∷ hArg ty₂ ∷ vArg tm ∷ []))
    ∷ (ty₂ , def (quote snd) (h₁ ∷ h₂ ∷ hArg ty₁ ∷ hArg ty₂ ∷ vArg tm ∷ []))
    ∷ []
destruct× (u ∷ []) = [ u ]
