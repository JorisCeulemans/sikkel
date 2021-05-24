--------------------------------------------------
-- Löb induction with automatic reduction of type
--------------------------------------------------

module Reflection.Tactic.NewSolver.LobInduction where

open import Data.List hiding ([_])
open import Data.Product
open import Data.String
open import Data.Unit
open import Reflection

open import Categories
open import CwF-Structure
open import GuardedRecursion.Modalities.Later
open import Reflection.Naturality.NewSolver renaming (reduce to nat-reduce) hiding (⊤)
open import Reflection.Tactic.NewSolver.ConstructExpression

infixr 4 löbι[_∈▻'_]_


löb-tactic : {Γ : Ctx ω} → Ty Γ → Term → TC ⊤
löb-tactic {Γ = Γ} T hole = do
  t-wantedBodyType ← quoteTC (T [ π {T = ▻' T} ])
  expr-wantedBodyType ← construct-expr t-wantedBodyType
  let expr-reducedBodyType = def (quote nat-reduce) (vArg expr-wantedBodyType ∷ [])
  ctx-expr ← quoteTC (Γ ,, ▻' T)
  let t-reducedBodyType = def (quote interp-expr) (vArg expr-reducedBodyType ∷ vArg ctx-expr ∷ [])
  let proof = def (quote reduce-sound) (vArg expr-wantedBodyType ∷ [])
  unify hole (con (quote _,_) (vArg t-reducedBodyType ∷ vArg proof ∷ []))

löbι : {Γ : Ctx ω} (T : Ty Γ)
       {@(tactic löb-tactic T) body-type : Σ[ S ∈ Ty (Γ ,, ▻' T) ] (T [ π ] ≅ᵗʸ S)} →
       Tm (Γ ,, ▻' T) (proj₁ body-type) → Tm Γ T
löbι T {body-type = S , T=S} b = löb' T (ι[ T=S ] b)

löbι[_∈▻'_]_ : {Γ : Ctx ω} (v : String) (T : Ty Γ)
                {@(tactic löb-tactic T) body-type : Σ[ S ∈ Ty (Γ ,, ▻' T) ] (T [ π ] ≅ᵗʸ S)} →
                Tm (Γ ,, v ∈ ▻' T) (proj₁ body-type) → Tm Γ T
löbι[_∈▻'_]_ v = löbι
