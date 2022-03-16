open import Model.BaseCategory

module Experimental.DependentTypes.Model.IdentityType.AlternativeVar {C : BaseCategory} where

open import Data.Product renaming (_,_ to [_,_])
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.Helpers
open import Model.CwF-Structure
open import Model.Type.Function

open BaseCategory C

private
  variable
    Δ Γ : Ctx C
    A B : Ty Γ


Id : Ty (Γ ,, A ,, A [ π ])
Id ⟨ x , [ [ γ , a ] , b ] ⟩ = a ≡ b
(Id {_}{A}) ⟪ f , refl ⟫ e = cong (A ⟪ f , _ ⟫_) e
ty-cong Id refl = uip _ _
ty-id Id = uip _ _
ty-comp Id = uip _ _

refl' : Γ ,, A ⇒ Γ ,, A ,, A [ π ] ,, Id
func refl' [ γ , a ] = [ [ [ γ , a ] , a ] , refl ]
_⇒_.naturality refl' = refl

J : (T : Ty (Γ ,, A ,, A [ π ] ,, Id)) → Tm (Γ ,, A) (T [ refl' ]) → Tm (Γ ,, A ,, A [ π ] ,, Id) T
J T t ⟨ x , [ [ [ γ , a ] , .a ] , refl ] ⟩' = t ⟨ x , [ γ , a ] ⟩'
Tm.naturality (J T t) {γy = [ [ [ γy , ay ] , .ay ] , refl ]} {γx = [ [ [ γx , ax ] , .ax ] , refl ]} f e =
  trans (ty-cong T refl) (Tm.naturality t f (cong (proj₁ ∘ proj₁) e))

J-β : {T : Ty (Γ ,, A ,, A [ π ] ,, Id)} (t : Tm (Γ ,, A) (T [ refl' ])) → J T t [ refl' ]' ≅ᵗᵐ t
eq (J-β t) _ = refl

contraction : Γ ,, A ⇒ Γ ,, A ,, A [ π ]
func contraction [ γ , a ] = [ [ γ , a ] , a ]
_⇒_.naturality contraction = refl

π∘refl : {A : Ty Γ} → π ⊚ refl' {A = A} ≅ˢ contraction
eq π∘refl _ = refl

exchange : Γ ,, A ,, A [ π ] ⇒ Γ ,, A ,, A [ π ]
func exchange [ [ γ , a ] , b ] = [ [ γ , b ] , a ]
_⇒_.naturality exchange = refl

sym' : Tm (Γ ,, A ,, A [ π ] ,, Id) (Id [ exchange ⊚ π ])
sym' = J (Id [ exchange ⊚ π ]) (ι[ proof2 ] (ξ [ refl' ]'))
  where
    proof : exchange ⊚ π ⊚ refl' ≅ˢ π ⊚ refl'
    eq proof _ = refl

    proof2 : (Id [ exchange ⊚ π ]) [ refl' ] ≅ᵗʸ (Id [ π ]) [ refl' ]
    proof2 = ≅ᵗʸ-trans (ty-subst-comp Id (exchange ⊚ π) refl') (≅ᵗʸ-trans (ty-subst-cong-subst proof Id) (≅ᵗʸ-sym (ty-subst-comp Id π refl')))
