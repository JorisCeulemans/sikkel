module Experimental.ClosedTypes.Identity where

open import Data.Product renaming (_,_ to [_,_])
import Relation.Binary.PropositionalEquality as A

open import Model.BaseCategory
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.Type
open import Model.CwF-Structure.Term

open import Experimental.ClosedTypes
open import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm

private variable
  C : BaseCategory
  Δ Γ : Ctx C
  A : ClosedTy C


ssubst' : {a b : SimpleTm Γ A} (T : Ty (Γ ,,ₛ A)) (σ : Δ ⇒ Γ) →
          Tm Δ ((Id a b) [ σ ]) →
          Tm Δ (T [ σ ,ₛ (a [ σ ]s) ]) →
          Tm Δ (T [ σ ,ₛ (b [ σ ]s) ])
ssubst' {A = A} T σ e t ⟨ x , δ ⟩' = ty-ctx-subst T (A.cong (λ c → [ _ , A ⟪ _ , _ ⟫ (A ⟪ _ , _ ⟫ c) ]) (e ⟨ x , δ ⟩')) (t ⟨ x , δ ⟩')
naturality (ssubst' {C} T σ e t) f eδ = A.trans (ty-cong-2-2 T (A.trans hom-idˡ (A.sym hom-idʳ))) (A.cong (T ⟪ _ , _ ⟫_) (naturality t _ eδ))
  where open BaseCategory C
