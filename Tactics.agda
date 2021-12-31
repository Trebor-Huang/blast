module Tactics where

open import Blast
open import Reflection
open import Data.List
open import Data.Vec
open import Data.Product using (_×_; _,_; proj₁; proj₂)
private
    -- we need these non-dependent versions to make them easier to quote
    fst : ∀ {a b} {A : Set a} {B : Set b} -> A × B -> A
    fst = proj₁
    snd : ∀ {a b} {A : Set a} {B : Set b} -> A × B -> B
    snd = proj₂
    _ʻ_ : ∀ {a b} {A : Set a} {B : Set b} -> A -> B -> A × B
    _ʻ_ = _,_

split×? : Tactic?
split×? record
    { goal = def (quote _×_)
        (h₁ ∷ h₂ ∷ vArg ty₁ ∷ vArg ty₂ ∷ [])
    ; context = context } = record
    { #goal = 2
    ; goals = record { goal = ty₁ ; context = context }
            ∷ record { goal = ty₂ ; context = context }
            ∷ []
    ; thunk = \ { (t₁ ∷ t₂ ∷ []) ->
        def (quote _ʻ_) (h₁ ∷ h₂ ∷ hArg ty₁ ∷ hArg ty₂ ∷ vArg t₁ ∷ vArg t₂ ∷ [])} }
split×? = idtac?

split× : Tactic
split× = ¿ split×?
