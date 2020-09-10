{-# OPTIONS --omega-in-omega #-}

open import Categories

module CwF-Structure.Variables {C : Category} where

open import Data.Fin
open import Data.Vec using (Vec; []; _∷_; foldr; lookup)
open import Data.Nat using (ℕ; zero; suc)
open import Level renaming (suc to lsuc)

open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension

private
  variable
    ℓ ℓ' ℓc : Level
    Γ : Ctx C ℓ
    n : ℕ
    ℓs : Vec Level n


level-fold : ∀ {n} → Vec Level n → Level
level-fold = foldr _ _⊔_ 0ℓ

data TypeSequence (Γ : Ctx C ℓc) : (n : ℕ) → Vec Level n →  Setω
_,,,_ : (Γ : Ctx C ℓc) {n : ℕ} {ℓs : Vec Level n} → TypeSequence Γ n ℓs → Ctx C (ℓc ⊔ level-fold ℓs)


data TypeSequence Γ where
  []  : TypeSequence Γ 0 []
  _∷_ : ∀ {ℓt n ℓs} (Ts : TypeSequence Γ n ℓs) → Ty (Γ ,,, Ts) ℓt → TypeSequence Γ (suc n) (ℓt ∷ ℓs)

Γ ,,, []       = Γ
Γ ,,, (Ts ∷ T) = (Γ ,,, Ts) ,, T

get-type : (Ts : TypeSequence Γ n ℓs) (x : Fin n) → Ty (Γ ,,, Ts) (lookup ℓs x)
get-type (Ts ∷ T) zero    = T [ π ]
get-type (Ts ∷ T) (suc x) = (get-type Ts x) [ π ]

prim-var : (Ts : TypeSequence Γ n ℓs) (x : Fin n) → Tm (Γ ,,, Ts) (get-type Ts x)
prim-var (Ts ∷ T) zero    = ξ
prim-var (Ts ∷ T) (suc x) = prim-var Ts x [ π ]'


open import Data.List hiding ([_]; map)
open import Data.Maybe hiding (_>>=_)
open import Data.Unit
open import Reflection hiding (var; lam)
open import Reflection.Argument hiding (map)

get-ctx : Type → Maybe Term
get-ctx (def (quote Tm) args) = go args
  where
    go : List (Arg Term) → Maybe Term
    go [] = nothing
    go (ctx ⟨∷⟩ ty ⟨∷⟩ xs) = just ctx
    go (_ ∷ xs) = go xs
get-ctx _ = nothing

ctx-to-tyseq : Term → Maybe Term
ctx-to-tyseq (def (quote _,,_) xs) = go xs
  where
    go : List (Arg Term) → Maybe Term
    go [] = nothing
    go (ctx ⟨∷⟩ ty ⟨∷⟩ xs) = map (λ tyseq → con (quote TypeSequence._∷_) (vArg tyseq ∷ vArg ty ∷ []))
                                 (ctx-to-tyseq ctx)
    go (_ ∷ xs) = go xs
ctx-to-tyseq ctx = just (con (quote TypeSequence.[]) [])

macro
  var : Term → Term → TC ⊤
  var x hole = do
    agda-type ← inferType hole
    just ctx ← return (get-ctx agda-type)
      where nothing → typeError (strErr "no term requested" ∷ termErr agda-type ∷ [])
    just tyseq ← return (ctx-to-tyseq ctx)
      where nothing → typeError (strErr "something went wrong" ∷ [])
    let solution = def (quote prim-var) (vArg tyseq ∷ vArg (def (quote #_) (vArg x ∷ [])) ∷ [])
    unify hole solution

private
  open import Types.Discrete
  open import Types.Functions {C = C}

  test : Tm {C = C} (◇ ,, Bool') (Bool' [ π ])
  test = var 0

  test2 : Tm {C = C} (◇ ,, Bool' ,, Nat') (Nat' [ π ])
  test2 = var 0

  test3 : Tm {C = C} (◇ ,, Bool' ,, Nat') ((Bool' [ π ]) [ π ])
  test3 = var 1

  id : {Γ : Ctx C ℓ} {T : Ty Γ ℓ'} → Tm Γ (T ⇛ T)
  id {Γ = Γ}{T = T} = lam T {!var 0!}
