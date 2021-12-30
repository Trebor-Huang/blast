{-# OPTIONS --safe --postfix-projections #-}

module Blast where

open import Reflection hiding (_≟_)
open import Reflection.Term using (_≟_)
open import Reflection.Meta using () renaming (_≟_ to _≟ₘ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Vec.Base using (Vec; []; _∷_; _++_; head; take; drop; map; foldl)
open import Data.Bool.Base using (Bool; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function.Base
open import Relation.Nullary using (does)
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Maybe

-- A few things that should be in stdlib, but I couldn't locate.
Context = List (String × Arg Term)  -- Abbreviates some of the type signatures.

private
    lookup : ∀ {a b} {A : Set a} {B : Set b}
        -> List (A × B) -> (A -> Bool) -> Maybe B
    lookup [] _ = nothing
    lookup ((a , b) ∷ xs) f = if f a then just b else lookup xs f

    -- we need these non-dependent versions to make them easier to quote
    fst : ∀ {a b} {A : Set a} {B : Set b} -> A × B -> A
    fst = proj₁
    snd : ∀ {a b} {A : Set a} {B : Set b} -> A × B -> B
    snd = proj₂
    _ʻ_ : ∀ {a b} {A : Set a} {B : Set b} -> A -> B -> A × B
    _ʻ_ = _,_

    -- A finite sum. Could be defined via folds, but I'm lazy.
    ∑̬ : {m : Nat} -> Vec Nat m -> Nat
    ∑̬ [] = zero
    ∑̬ (n ∷ v) = n + ∑̬ v

record Goal : Set where
    -- A Goal contains a goal type and a list of available terms.
    field
        goal : Type
        context : List (Type × Term)

currentCtx : TC (List (Type × Term))
currentCtx = do
    ctx <- getContext
    return (zipCtx 0 ctx)
    where
        zipCtx : Nat -> List (Arg Type) -> List (Type × Term)
        zipCtx _ [] = []
        zipCtx n (arg i t ∷ a) = (t , var n []) ∷ zipCtx (suc n) a

record Environment : Set where
    -- An environment is a list of goals, and how to build
    -- the solution when all the goals are solved.
    field
        #goal : Nat
        goals : Vec Goal #goal
        thunk : Vec Term #goal -> Term

open Goal
open Environment

-- Fetch the current Context, and pack it up into an Environment.
currentEnv : Term -> TC Environment
currentEnv hole = do
    ctx <- currentCtx
    g <- inferType hole
    return (record
        { #goal = 1
        ; goals = record { goal = g
                ; context = ctx } ∷ []
        ; thunk = head })

-- Tactics are just goal transformers.
Tactic = Goal -> Environment
-- Convention: If a tactic ends in ?, it may result in an inconsistent state.

idtac : Tactic
idtac g .#goal = 1
idtac g .goals = g ∷ []
idtac g .thunk (tm ∷ _) = tm

-- Strategies are "global" tactics that act on the whole environment.
Strategy = Environment -> Environment

-- Apply tactic at top goal.
♯ : Tactic -> Strategy
♯ tac e @ record { #goal = zero } = e
♯ tac record { #goal = suc n ; goals = g ∷ gs ; thunk = thunk }
    with tac g
... | record { #goal = m ; goals = gs' ; thunk = thunk' }
    = record {
        #goal = m + n ;
        goals = gs' ++ gs ;
        thunk = (\ v -> thunk (thunk' (take _ v) ∷ drop _ v)) }

-- Sort of like operads.
⋀ : {n : Nat} -> (Vec Term n -> Term) -> Vec Environment n -> Environment
⋀ f envs .#goal = ∑̬ (map #goal envs)
⋀ f envs .goals = conc envs
    where
        conc : {n : Nat} (envs : Vec Environment n) -> Vec Goal (∑̬ (map #goal envs))
        conc [] = []
        conc (env ∷ envs) = env .goals ++ conc envs
⋀ f envs .thunk res = f (swath envs res)
    where
        swath : ∀ {n} (envs : Vec Environment n)
          (res : Vec Term (∑̬ (map #goal envs))) -> Vec Term n
        swath [] [] = []
        swath (env ∷ envs) res = (env .thunk (take _ res) ∷ swath envs (drop _ res))

-- Apply tactic to all goals.
𝄪 : Tactic -> Strategy
𝄪 tac record { goals = gs ; thunk = thunk }
    = ⋀ thunk (map tac gs)

private
    done : (#goal : Nat)
        (goals : Vec Goal #goal)
        (thunk : Vec Term #goal -> Term) -> Term -> TC ⊤
    done zero [] thunk hole = do
        qth <- quoteTC (thunk [])
        nqth <- normalise qth
        debugPrint "Blast.done" 8
            ( strErr "Done tactic: 🎉\nResult:\n"
            ∷ termErr nqth
            ∷ [] )
        unify (thunk []) hole
    done (suc n) (g ∷ gs) thunk hole
        = do
            newMeta <- checkType unknown (g .goal)
            qm <- quoteTC newMeta
            qg <- quoteTC (g .goal)
            qn <- quoteTC n
            debugPrint "Blast.done" 10
                ( strErr "Done tactic: n = "
                ∷ termErr qn
                ∷ strErr "\nGoal:\n  "
                ∷ termErr qg
                ∷ strErr "\nMeta:\n  "
                ∷ termErr qm
                ∷ [] )
            done n gs (thunk ∘ (newMeta ∷_)) hole

macro
    by! : Strategy -> Term -> TC ⊤
    by! st hole = do
        env <- currentEnv hole
        let env' = st env
        done (env' .#goal) (env' .goals) (env' .thunk) hole

assump : Tactic
assump goal @ record { goal = g ; context = ctx }
    with lookup ctx (does ∘ (_≟ g))
... | just t = record
    { #goal = 0
    ; goals = []
    ; thunk = const t }
... | nothing = idtac goal

split× : Tactic
split× record
    { goal = def (quote _×_)
        (h₁ ∷ h₂ ∷ vArg ty₁ ∷ vArg ty₂ ∷ [])
    ; context = context } = record
    { #goal = 2
    ; goals = record { goal = ty₁ ; context = context }
            ∷ record { goal = ty₂ ; context = context }
            ∷ []
    ; thunk = \ { (t₁ ∷ t₂ ∷ []) ->
        def (quote _ʻ_) (h₁ ∷ h₂ ∷ hArg ty₁ ∷ hArg ty₂ ∷ vArg t₁ ∷ vArg t₂ ∷ [])} }
split× = idtac
