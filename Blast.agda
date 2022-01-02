{-# OPTIONS --safe --postfix-projections #-}

module Blast where

open import Reflection hiding (_≟_)
open import Reflection.Term using (_≟_)
open import Reflection.DeBruijn
open import Reflection.TypeChecking.Monad.Syntax
open import Data.List.Base using (List; []; _∷_; [_]; cartesianProductWith; concatMap; length; _─_) renaming (map to mapₗ; _++_ to _+++_)
open import Data.Vec.Base using (Vec; []; _∷_; _++_; head; take; drop; map; foldl)
open import Data.Bool.Base using (Bool; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂) renaming (map to mapₚ)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Maybe using (Maybe; nothing; just) renaming (map to mapₘ)
open import Function.Base
open import Relation.Nullary using (does)
open import Agda.Builtin.Nat
open import Data.Nat.Show using (show)
open import Agda.Builtin.Unit
open import Agda.Builtin.String

-- Constant parameters
private
    DONE_VERBOSITY = 10
    {-# INLINE DONE_VERBOSITY #-}

-- A few things that should be in stdlib, but I couldn't locate.
Context = List (String × Arg Term)  -- Abbreviates some of the type signatures.

private
    lookup : ∀ {a b} {A : Set a} {B : Set b}
        -> List (A × B) -> (A -> Bool) -> Maybe B
    lookup [] _ = nothing
    lookup ((a , b) ∷ xs) f = if f a then just b else lookup xs f

    -- A finite sum. Could be defined via folds, but I'm lazy.
    ∑̬ : {m : Nat} -> Vec Nat m -> Nat
    ∑̬ [] = zero
    ∑̬ (n ∷ v) = n + ∑̬ v

    Vec-List : ∀ {a} {m : Nat} {A : Set a} -> Vec (List A) m -> List (Vec A m)
    Vec-List [] = [] ∷ []
    Vec-List (xs ∷ vec) = cartesianProductWith _∷_ xs (Vec-List vec)

    inFin : (m n : Nat) -> Maybe (Fin m)
    inFin zero n = nothing
    inFin (suc m) zero = just fz
    inFin (suc m) (suc n) = mapₘ fs (inFin m n)

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

simply : Goal -> Environment
simply G = record
    { #goal = 1
    ; goals = G ∷ []
    ; thunk = head }

-- Fetch the current Context, and pack it up into an Environment.
currentEnv : Term -> TC Environment
currentEnv hole = do
    ctx <- currentCtx
    g <- inferType hole
    return (simply record { goal = g ; context = ctx })

Backtracking = List
-- Tactics are just goal transformers.
Tactic = Goal -> Backtracking Environment

fail : Tactic
fail = const []

idtac : Tactic
idtac env = [ simply env ]

-- Strategies are "global" tactics that act on the whole environment.
Strategy = Environment -> Backtracking Environment

-- Apply tactic at top goal.
♯ : Tactic -> Strategy
♯ tac e @ record { #goal = zero } = [ e ]
♯ tac record { #goal = suc n ; goals = g ∷ gs ; thunk = thunk }
    = mapₗ helper (tac g)
    where
        helper : Environment -> Environment
        helper record { #goal = m ; goals = gs' ; thunk = thunk' } = record
            { #goal = m + n
            ; goals = gs' ++ gs
            ; thunk = \ v -> thunk (thunk' (take _ v) ∷ drop _ v) }

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
♮ : Tactic -> Strategy
♮ tac record { goals = gs ; thunk = thunk }
    = mapₗ (⋀ thunk) (Vec-List (map tac gs))

idle = ♮ idtac

private
    done : (#goal : Nat)
        (goals : Vec Goal #goal)
        (thunk : Vec Term #goal -> Term) -> Term -> TC ⊤
    done zero [] thunk hole = do
        qth <- quoteTC (thunk [])
        nqth <- normalise qth
        debugPrint "Blast.by!" DONE_VERBOSITY
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
            debugPrint "Blast.by!" DONE_VERBOSITY
                ( strErr "Done tactic: n = "
                ∷ termErr qn
                ∷ strErr "\nGoal:\n  "
                ∷ termErr qg
                ∷ strErr "\nMeta:\n  "
                ∷ termErr qm
                ∷ [] )
            done n gs (thunk ∘ (newMeta ∷_)) hole

    solved : (Term -> TC ⊤) -> (Term -> TC ⊤)
    solved sol hole = do
        sol hole

    try : Backtracking Environment -> Term -> TC ⊤
    try [] hole = typeError (strErr "Blast.try: All attempts failed." ∷ [])
    try (env ∷ envs) hole = solved (done (env .#goal) (env .goals) (env .thunk)) hole
        <|> try envs hole

macro
    by!_ : Strategy -> Term -> TC ⊤
    by!_ st hole = do
        env <- currentEnv hole
        let envs = st env
        debugPrint "Blast.by!" DONE_VERBOSITY
            ( strErr "By! tactic encountered "
            ∷ strErr (show (length envs))
            ∷ strErr " backtrack routes."
            ∷ [] )
        try envs hole

infix 0 by!_

assumption′ : Tactic
assumption′ goal @ record { goal = g ; context = ctx }
    with lookup ctx (does ∘ (_≟ g))
... | just t = [ record
    { #goal = 0
    ; goals = []
    ; thunk = const t } ]
... | nothing = []

assumption : Strategy
assumption = ♮ assumption′

_>==>_ : Strategy -> Strategy -> Strategy
s₁ >==> s₂ = concatMap s₂ ∘ s₁

_<~>_ : Tactic -> Tactic -> Tactic
(t₁ <~> t₂) g = t₁ g +++ t₂ g

-- Apply strategy to top goal.
♭ : Strategy -> Tactic
♭ st g = st (simply g)

⟦_⟧ : Strategy -> Strategy
⟦_⟧ = ♯ ∘ ♭

_>==>′_ : Tactic -> Tactic -> Tactic
t₁ >==>′ t₂ = ♭ (♯ t₁ >==> ♯ t₂)

infixl 5 _>==>_
infixl 6 _<~>_
infixl 6 _>==>′_

-- Snucks in one more argument, and shifts the de Bruijn indices.
_↑_ : Goal -> Type -> Goal
record { goal = goal ; context = context } ↑ ty = record
    { goal = weaken 1 goal
    ; context = (ty , var 0 []) ∷ mapₗ (mapₚ (weaken 1) (weaken 1)) context }
infixl 6 _↑_

-- Knocks out something in the context
_↓_ : Nat -> Goal -> Goal
n ↓ g with inFin (length (g .context)) n
... | just i = record g { context = g .context ─ i }
... | nothing = g
infixr 6 _↓_

macro
    sorry! : Term -> TC ⊤
    sorry! hole = do
        ty <- inferType hole
        n <- freshName "sorry"
        declarePostulate (vArg n) ty
        unify hole (def n [])
