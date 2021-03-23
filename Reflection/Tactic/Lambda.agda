--------------------------------------------------
-- Definition of a lambda that automatically performs
-- naturality reduction on its body type
--------------------------------------------------

module Reflection.Tactic.Lambda where

open import Data.List hiding ([_])
open import Data.Product
open import Data.String
open import Data.Unit
open import Reflection hiding (lam)

open import CwF-Structure
open import Types.Functions
open import Reflection.Naturality.Solver renaming (reduce to nat-reduce)
open import Reflection.Tactic.ConstructExpression

infixr 4 lamι[_∈_]_


lam-tactic : ∀ {C ℓc ℓt ℓs} {Γ : Ctx C ℓc} → Ty Γ ℓt → Ty Γ ℓs → Term → TC ⊤
lam-tactic T S hole = do
  t-wantedBodyType ← quoteTC (S [ π {T = T} ])
  debugPrint "vtac" 5 (strErr "lam-tactic called with type" ∷ termErr t-wantedBodyType ∷ [])
  expr-wantedBodyType ← construct-expr t-wantedBodyType
  let expr-reducedBodyType = def (quote nat-reduce) (vArg expr-wantedBodyType ∷ [])
  debugPrint "vtac" 5 (strErr "lam-tactic constructed expression" ∷ termErr expr-reducedBodyType ∷ [])
  let t-reducedBodyType = def (quote ⟦_⟧exp) (vArg expr-reducedBodyType ∷ [])
  let proof = def (quote reduce-sound) (vArg expr-wantedBodyType ∷ [])
  unify hole (con (quote _,_) (vArg t-reducedBodyType ∷ vArg proof ∷ []))

lamι : ∀ {C ℓc ℓt ℓs ℓs'} {Γ : Ctx C ℓc} (T : Ty Γ ℓt) {S : Ty Γ ℓs}
       {@(tactic lam-tactic T S) body-type : Σ[ S' ∈ Ty (Γ ,, T) ℓs' ] (S [ π ] ≅ᵗʸ S')} →
       Tm (Γ ,, T) (proj₁ body-type) → Tm Γ (T ⇛ S)
lamι T {body-type = S' , Sπ=S'} b = lam T (ι[ Sπ=S' ] b)

lamι[_∈_]_ : ∀ {C ℓc ℓt ℓs ℓs'} {Γ : Ctx C ℓc} (v : String) (T : Ty Γ ℓt) {S : Ty Γ ℓs}
             {@(tactic lam-tactic T S) body-type : Σ[ S' ∈ Ty (Γ ,, T) ℓs' ] (S [ π ] ≅ᵗʸ S')} →
             Tm (Γ ,, v ∈ T) (proj₁ body-type) → Tm Γ (T ⇛ S)
lamι[_∈_]_ v = lamι
