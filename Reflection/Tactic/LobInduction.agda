--------------------------------------------------
-- Löb induction with automatic reduction of type
--------------------------------------------------

module Reflection.Tactic.LobInduction where

open import Data.List hiding ([_])
open import Data.Product
open import Data.String
open import Data.Unit
open import Reflection

open import Categories
open import CwF-Structure
open import GuardedRecursion.Modalities.Later
open import Reflection.Naturality renaming (reduce to nat-reduce)
open import Reflection.Tactic.ConstructExpression

infixr 4 löbι[_∈▻'_]_


löb-tactic : ∀ {ℓc ℓt} {Γ : Ctx ω ℓc} → Ty Γ ℓt → Term → TC ⊤
löb-tactic T hole = do
  t-wantedBodyType ← quoteTC (T [ π {T = ▻' T} ])
  expr-wantedBodyType ← construct-expr t-wantedBodyType
  let expr-reducedBodyType = def (quote nat-reduce) (vArg expr-wantedBodyType ∷ [])
  let t-reducedBodyType = def (quote ⟦_⟧exp) (vArg expr-reducedBodyType ∷ [])
  let proof = def (quote reduce-sound) (vArg expr-wantedBodyType ∷ [])
  unify hole (con (quote _,_) (vArg t-reducedBodyType ∷ vArg proof ∷ []))

löbι : ∀ {ℓc ℓt ℓs} {Γ : Ctx ω ℓc} (T : Ty Γ ℓt)
      {@(tactic löb-tactic T) body-type : Σ[ S ∈ Ty (Γ ,, ▻' T) ℓs ] (T [ π ] ≅ᵗʸ S)} →
      Tm (Γ ,, ▻' T) (proj₁ body-type) → Tm Γ T
löbι T {body-type = S , T=S} b = löb' T (ι[ T=S ] b)

löbι[_∈▻'_]_ : ∀ {ℓc ℓt ℓs} {Γ : Ctx ω ℓc} (v : String) (T : Ty Γ ℓt)
              {@(tactic löb-tactic T) body-type : Σ[ S ∈ Ty (Γ ,, ▻' T) ℓs ] (T [ π ] ≅ᵗʸ S)} →
              Tm (Γ ,, v ∈ ▻' T) (proj₁ body-type) → Tm Γ T
löbι[_∈▻'_]_ v = löbι
