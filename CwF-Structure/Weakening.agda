{-# OPTIONS --omega-in-omega #-}

module CwF-Structure.Weakening where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Level renaming (zero to lzero; suc to lsuc)
open import Reflection
open import Reflection.Argument using (_⟨∷⟩_)
open import Reflection.TypeChecking.Monad.Syntax using (_<$>_)

open import Categories
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension
open import CwF-Structure.Variables


private
  variable
    ℓc ℓt : Level


module _ {C : Category} where
  weaken-type : {Γ : Ctx C ℓc} {n : ℕ} {ℓs : _} (Ts : TypeSequence Γ n ℓs) →
                Ty Γ ℓt → Ty (Γ ,,, Ts) ℓt
  weaken-type []       S = S
  weaken-type (Ts ∷ T) S = (weaken-type Ts S) [ π ]

  weaken-term : {Γ : Ctx C ℓc} {n : ℕ} {ℓs : _} (Ts : TypeSequence Γ n ℓs) {S : Ty Γ ℓt} →
                Tm Γ S → Tm (Γ ,,, Ts) (weaken-type Ts S)
  weaken-term []       s = s
  weaken-term (Ts ∷ T) s = (weaken-term Ts s) [ π ]'

bounded-ctx-to-tyseq : ℕ → Term → TC Term
bounded-ctx-to-tyseq 0 _ = return (con (quote TypeSequence.[]) [])
bounded-ctx-to-tyseq (suc n) (def (quote _,,_) xs) = go xs
  where
    go : List (Arg Term) → TC Term
    go [] = typeError (strErr "Invalid use of context extension." ∷ [])
    go (ctx ⟨∷⟩ ty ⟨∷⟩ xs) = (λ tyseq → con (quote TypeSequence._∷_) (vArg tyseq ∷ vArg ty ∷ [])) <$>
                             (bounded-ctx-to-tyseq n ctx)
    go (_ ∷ xs) = go xs
bounded-ctx-to-tyseq (suc n) (meta m args) = debugPrint "vtac" 5 (strErr "Blocking on meta" ∷ termErr (meta m args) ∷ strErr "in ctx-to-tyseq." ∷ []) >>
                                             blockOnMeta m
bounded-ctx-to-tyseq (suc n) _ = typeError (strErr "Weakening this far is not possible in the current context." ∷ [])

weaken-macro : ℕ → Term → Term → TC ⊤
weaken-macro n term hole = do
  extended-ctx ← inferType hole >>= get-ctx
  ty-seq ← bounded-ctx-to-tyseq n extended-ctx
  let solution = def (quote weaken-term) (ty-seq ⟨∷⟩ term ⟨∷⟩ [])
  unify hole solution

macro
  ↑⟨_⟩_ : ℕ → Term → Term → TC ⊤
  ↑⟨ n ⟩ term = weaken-macro n term

