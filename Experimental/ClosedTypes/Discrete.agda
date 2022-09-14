module Experimental.ClosedTypes.Discrete where

open import Data.Product renaming (_,_ to [_,_])
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.Helpers
open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Type.Function
open import Model.Type.Discrete

open import Experimental.ClosedTypes
open import Experimental.ClosedTypes.Pi
open import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm

private variable
  C : BaseCategory
  Δ Γ : Ctx C


strue≠sfalse : Tm Γ (Id strue sfalse ⇛ Empty')
strue≠sfalse {Γ = Γ} = lam _ body
  where
    body : Tm (Γ ,, Id strue sfalse) (Empty' [ π ])
    body ⟨ x , () ⟩'
    naturality body {γx = ()} f eγ

ssuc-inj : Tm Γ (sPi Nat' (sPi Nat' (Id (ssuc ∙ₛ (sξ [ π ]s)) (ssuc ∙ₛ sξ) ⇛ Id (sξ [ π ]s) sξ)))
ssuc-inj = sdλ[ Nat' ] (sdλ[ Nat' ] body)
  where
    body : Tm (_ ,,ₛ Nat' ,,ₛ Nat') (Id (ssuc ∙ₛ (sξ [ π ]s)) (ssuc ∙ₛ sξ) ⇛ Id (sξ [ π ]s) sξ)
    body ⟨ x , [ [ γ , m ] , .m ] ⟩' $⟨ ρ , refl ⟩ refl = refl
    naturality (body ⟨ x , γ ⟩') = uip _ _
    naturality body f eγ = to-pshfun-eq (λ _ _ _ → uip _ _)

szero≠ssucn : Tm Γ (sPi Nat' (Id szero (ssuc ∙ₛ sξ) ⇛ Empty'))
szero≠ssucn = sdλ[ Nat' ] body
  where
    body : Tm (_ ,,ₛ Nat') (Id szero (ssuc ∙ₛ sξ) ⇛ Empty')
    body ⟨ x , γ ⟩' $⟨ ρ , eγ ⟩ ()
    naturality (body ⟨ x , γ ⟩') {t = ()}
    naturality body f eγ = to-pshfun-eq (λ _ _ ())
