open import Categories

module Types.Identity {C : Category} where

open import Data.Product renaming (_,_ to [_,_])
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Helpers
open import CwF-Structure

open Category C

private
  variable
    Δ Γ : Ctx C
    A : Ty Γ



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
         Tm Γ (T [ ⟨ id-subst Γ , ι[ ty-subst-id A ] a ∈ A ⟩ ]) →
         Tm Γ (T [ ⟨ id-subst Γ , ι[ ty-subst-id A ] b ∈ A ⟩ ])
subst' T a=b t ⟨ x , γ ⟩' = ctx-element-subst T (cong [ γ ,_] (a=b ⟨ x , γ ⟩')) (t ⟨ x , γ ⟩')
Tm.naturality (subst' T a=b t) f eγ = trans (ty-cong-2-2 T (trans hom-idˡ (sym hom-idʳ)))
                                            (cong (ctx-element-subst T (cong _ _)) (Tm.naturality t f eγ))

Id-natural : (σ : Δ ⇒ Γ) {a b : Tm Γ A} → (Id a b) [ σ ] ≅ᵗʸ Id (a [ σ ]') (b [ σ ]')
func (from (Id-natural σ {a = a} {b = b})) e = e
CwF-Structure.naturality (from (Id-natural σ {a = a} {b = b})) = refl
func (to (Id-natural σ {a = a} {b = b})) e = e
CwF-Structure.naturality (to (Id-natural σ {a = a} {b = b})) = refl
eq (isoˡ (Id-natural σ {a = a} {b = b})) _ = refl
eq (isoʳ (Id-natural σ {a = a} {b = b})) _ = refl

Id-cong : {A B : Ty Γ} {a a' : Tm Γ A} {b b' : Tm Γ B} →
          (A=B : A ≅ᵗʸ B) → a ≅ᵗᵐ ι[ A=B ] b → a' ≅ᵗᵐ ι[ A=B ] b' →
          Id a a' ≅ᵗʸ Id b b'
func (from (Id-cong A=B a=b a=b')) {γ = γ} e = trans (sym (eq (isoʳ A=B) _)) (trans (cong (func (from A=B)) (trans (sym (eq a=b γ)) (trans e (eq a=b' γ)))) (eq (isoʳ A=B) _))
CwF-Structure.naturality (from (Id-cong A=B a=b a=b')) = uip _ _
func (to (Id-cong A=B a=b a=b')) {γ = γ} e = trans (eq a=b γ) (trans (cong (func (to A=B)) e) (sym (eq a=b' γ)))
CwF-Structure.naturality (to (Id-cong A=B a=b a=b')) = uip _ _
eq (isoˡ (Id-cong A=B a=b a=b')) _ = uip _ _
eq (isoʳ (Id-cong A=B a=b a=b')) _ = uip _ _

sym' : {a b : Tm Γ A} → Tm Γ (Id a b) → Tm Γ (Id b a)
sym' {a = a} {b = b} e = ι⁻¹[ ≅ᵗʸ-trans (Id-natural _) {!!} ] (subst' (Id ξ (a [ π ]')) e (ι[ Id-natural _ ] (ι[ ≅ᵗʸ-trans (Id-cong (π-ext-comp-ty-subst _ _ _)  {!!} {!!}) (Id-cong (ty-subst-id _) (tm-subst-id a) (tm-subst-id a)) ] refl' a)))
