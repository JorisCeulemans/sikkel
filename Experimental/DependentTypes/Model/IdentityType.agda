open import Model.BaseCategory

module Experimental.DependentTypes.Model.IdentityType {C : BaseCategory} where

open import Data.Product renaming (_,_ to [_,_])
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.Helpers
open import Model.CwF-Structure

open BaseCategory C

private
  variable
    Δ Γ : Ctx C
    A : Ty Γ


module Alternative1 where
  Id : Tm Γ A → Tm Γ A → Ty Γ
  Id a b ⟨ x , γ ⟩ = a ⟨ x , γ ⟩' ≡ b ⟨ x , γ ⟩'
  _⟪_,_⟫_ (Id {A = A} a b) {x} {y} f {γy} {γx} eγ ea =
    begin
      a ⟨ x , γx ⟩'
    ≡˘⟨ Tm.naturality a f eγ ⟩
      A ⟪ f , eγ ⟫ a ⟨ y , γy ⟩'
    ≡⟨ cong (A ⟪ f , eγ ⟫_) ea ⟩
      A ⟪ f , eγ ⟫ b ⟨ y , γy ⟩'
    ≡⟨ Tm.naturality b f eγ ⟩
      b ⟨ x , γx ⟩' ∎
    where open ≡-Reasoning
  ty-cong (Id a b) _ = uip _ _
  ty-id (Id a b) = uip _ _
  ty-comp (Id a b) = uip _ _

  refl' : (a : Tm Γ A) → Tm Γ (Id a a)
  refl' a ⟨ x , γ ⟩' = refl
  Tm.naturality (refl' a) f eγ = uip _ _ -- also provable without uip

  subst' : {A : Ty Γ} (T : Ty (Γ ,, "x" ∈ A))
           {a b : Tm Γ A} → Tm Γ (Id a b) →
           Tm Γ (T [ ⟨ id-subst Γ , a [ id-subst _ ]' ∈ A ⟩ ]) →
           Tm Γ (T [ ⟨ id-subst Γ , b [ id-subst _ ]' ∈ A ⟩ ])
  subst' T a=b t ⟨ x , γ ⟩' = ty-ctx-subst T (cong [ γ ,_] (a=b ⟨ x , γ ⟩')) (t ⟨ x , γ ⟩')
  Tm.naturality (subst' T a=b t) f eγ = trans (ty-cong-2-2 T (trans hom-idˡ (sym hom-idʳ)))
                                              (cong (ty-ctx-subst T (cong _ _)) (Tm.naturality t f eγ))

  Id-natural : (σ : Δ ⇒ Γ) {a b : Tm Γ A} → (Id a b) [ σ ] ≅ᵗʸ Id (a [ σ ]') (b [ σ ]')
  func (from (Id-natural σ {a = a} {b = b})) e = e
  _↣_.naturality (from (Id-natural σ {a = a} {b = b})) = refl
  func (to (Id-natural σ {a = a} {b = b})) e = e
  _↣_.naturality (to (Id-natural σ {a = a} {b = b})) = refl
  eq (isoˡ (Id-natural σ {a = a} {b = b})) _ = refl
  eq (isoʳ (Id-natural σ {a = a} {b = b})) _ = refl

  Id-cong : {A B : Ty Γ} {a a' : Tm Γ A} {b b' : Tm Γ B} →
            (A=B : A ≅ᵗʸ B) → a ≅ᵗᵐ ι[ A=B ] b → a' ≅ᵗᵐ ι[ A=B ] b' →
            Id a a' ≅ᵗʸ Id b b'
  func (from (Id-cong A=B a=b a=b')) {γ = γ} e = trans (sym (eq (isoʳ A=B) _)) (trans (cong (func (from A=B)) (trans (sym (eq a=b γ)) (trans e (eq a=b' γ)))) (eq (isoʳ A=B) _))
  _↣_.naturality (from (Id-cong A=B a=b a=b')) = uip _ _
  func (to (Id-cong A=B a=b a=b')) {γ = γ} e = trans (eq a=b γ) (trans (cong (func (to A=B)) e) (sym (eq a=b' γ)))
  _↣_.naturality (to (Id-cong A=B a=b a=b')) = uip _ _
  eq (isoˡ (Id-cong A=B a=b a=b')) _ = uip _ _
  eq (isoʳ (Id-cong A=B a=b a=b')) _ = uip _ _

  eq-reflect : {a b : Tm Γ A} → Tm Γ (Id a b) → a ≅ᵗᵐ b
  eq (eq-reflect e) {x = x} γ = e ⟨ x , γ ⟩'

  sym' : {a b : Tm Γ A} → Tm Γ (Id a b) → Tm Γ (Id b a)
  sym' {Γ = Γ} {A = A} {a = a} {b = b} e =
    ι⁻¹[ proof b ] (
    subst' (Id ξ (a [ π ]'))
           e
           (ι[ proof a ] refl' a))
    where
      proof : (t : Tm Γ A) → (Id ξ (a [ π ]')) [ ⟨ id-subst Γ , t [ id-subst Γ ]' ∈ A ⟩ ] ≅ᵗʸ Id t a
      proof t = ≅ᵗʸ-trans (Id-natural _)
                          (≅ᵗʸ-trans (Id-cong (≅ᵗʸ-trans (ty-subst-comp A _ _)
                                                         (ty-subst-cong-subst (ctx-ext-subst-proj₁ _ _) A))
                                              (ctx-ext-subst-β₂ _ _)
                                              (≅ᵗᵐ-trans (tm-subst-comp a _ _)
                                                         (≅ᵗᵐ-trans (ι-cong (ty-subst-comp _ _ _) (tm-subst-cong-subst a (ctx-ext-subst-proj₁ _ _)))
                                                                    (≅ᵗᵐ-sym (ι-trans (ty-subst-comp _ _ _) (ty-subst-cong-subst _ _) (a [ id-subst _ ]'))))))
                                     (Id-cong (ty-subst-id _) (tm-subst-id t) (tm-subst-id a)))


module Alternative2 {A : Ty Γ} where
  Id : Ty (Γ ,, A ,, A [ π ])
  Id ⟨ x , [ [ γ , a ] , b ] ⟩ = a ≡ b
  Id ⟪ f , refl ⟫ e = cong (A ⟪ f , _ ⟫_) e
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

  π∘refl : π ⊚ refl' ≅ˢ contraction
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
