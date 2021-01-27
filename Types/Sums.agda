--------------------------------------------------
-- Sum types
--------------------------------------------------

open import Categories

module Types.Sums {C : Category} where

open import Data.Sum using (_⊎_; inj₁; inj₂; map)
open import Data.Sum.Relation.Binary.Pointwise
open import Function using (id)
open import Level
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Helpers
open import CwF-Structure
open import Types.Functions

private
  variable
    ℓ'' r r' r'' : Level
    Γ Δ : Ctx C ℓ r
    T T' S S' : Ty Γ ℓ r


_⊞_ : Ty Γ ℓ r → Ty Γ ℓ' r' → Ty Γ (ℓ ⊔ ℓ') _
type (T ⊞ S) x γ = type T x γ ⊎ₛ type S x γ
morph (T ⊞ S) f eγ = map (morph T f eγ) (morph S f eγ)
morph-cong (T ⊞ S) f eγ (inj₁ et) = inj₁ (morph-cong T f eγ et)
morph-cong (T ⊞ S) f eγ (inj₂ es) = inj₂ (morph-cong S f eγ es)
morph-hom-cong (T ⊞ S) e {t = inj₁ t} = inj₁ (morph-hom-cong T e)
morph-hom-cong (T ⊞ S) e {t = inj₂ s} = inj₂ (morph-hom-cong S e)
morph-id (T ⊞ S) (inj₁ t) = inj₁ (morph-id T t)
morph-id (T ⊞ S) (inj₂ s) = inj₂ (morph-id S s)
morph-comp (T ⊞ S) f g eq-zy eq-yx (inj₁ t) = inj₁ (morph-comp T f g eq-zy eq-yx t)
morph-comp (T ⊞ S) f g eq-zy eq-yx (inj₂ s) = inj₂ (morph-comp S f g eq-zy eq-yx s)

⊞-bimap : (T ↣ T') → (S ↣ S') → (T ⊞ S ↣ T' ⊞ S')
func (⊞-bimap η φ) = map (func η) (func φ)
func-cong (⊞-bimap η φ) (inj₁ et) = inj₁ (func-cong η et)
func-cong (⊞-bimap η φ) (inj₂ es) = inj₂ (func-cong φ es)
naturality (⊞-bimap η φ) (inj₁ t) = inj₁ (naturality η t)
naturality (⊞-bimap η φ) (inj₂ s) = inj₂ (naturality φ s)

⊞-cong : T ≅ᵗʸ T' → S ≅ᵗʸ S' → T ⊞ S ≅ᵗʸ T' ⊞ S'
from (⊞-cong T=T' S=S') = ⊞-bimap (from T=T') (from S=S')
to (⊞-cong T=T' S=S') = ⊞-bimap (to T=T') (to S=S')
eq (isoˡ (⊞-cong T=T' S=S')) (inj₁ t) = inj₁ (eq (isoˡ T=T') t)
eq (isoˡ (⊞-cong T=T' S=S')) (inj₂ s) = inj₂ (eq (isoˡ S=S') s)
eq (isoʳ (⊞-cong T=T' S=S')) (inj₁ t) = inj₁ (eq (isoʳ T=T') t)
eq (isoʳ (⊞-cong T=T' S=S')) (inj₂ s) = inj₂ (eq (isoʳ S=S') s)

inl : Tm Γ T → Tm Γ (T ⊞ S)
term (inl t) x γ = inj₁ (t ⟨ x , γ ⟩')
naturality (inl t) f eγ = inj₁ (naturality t f eγ)

inr : Tm Γ S → Tm Γ (T ⊞ S)
term (inr s) x γ = inj₂ (s ⟨ x , γ ⟩')
naturality (inr s) f eγ = inj₂ (naturality s f eγ)

inl⟨_⟩_ : (S : Ty Γ ℓ r) (t : Tm Γ T) → Tm Γ (T ⊞ S)
inl⟨ S ⟩ t = inl {S = S} t

inr⟨_⟩_ : (T : Ty Γ ℓ r) (s : Tm Γ S) → Tm Γ (T ⊞ S)
inr⟨ T ⟩ s = inr {T = T} s

module _ {T : Ty Γ ℓ r} {S : Ty Γ ℓ' r'} where
  inl-cong : {t t' : Tm Γ T} → t ≅ᵗᵐ t' → inl⟨ S ⟩ t ≅ᵗᵐ inl t'
  eq (inl-cong t=t') γ = inj₁ (eq t=t' γ)

  inr-cong : {s s' : Tm Γ S} → s ≅ᵗᵐ s' → inr⟨ T ⟩ s ≅ᵗᵐ inr s'
  eq (inr-cong s=s') γ = inj₂ (eq s=s' γ)

module _ {ℓt ℓt' ℓs ℓs' rt rt' rs rs'}
  {T : Ty Γ ℓt rt} {T' : Ty Γ ℓt' rt'} {S : Ty Γ ℓs rs} {S' : Ty Γ ℓs' rs'}
  (T=T' : T ≅ᵗʸ T') (S=S' : S ≅ᵗʸ S')
  where

  inl-ι : (t : Tm Γ T') → ι[ ⊞-cong T=T' S=S' ] inl t ≅ᵗᵐ inl (ι[ T=T' ] t)
  eq (inl-ι t) _ = ty≈-refl (T ⊞ S)

  inr-ι : (s : Tm Γ S') → ι[ ⊞-cong T=T' S=S' ] inr s ≅ᵗᵐ inr (ι[ S=S' ] s)
  eq (inr-ι s) _ = ty≈-refl (T ⊞ S)

module _ {T : Ty Γ ℓ r} {S : Ty Γ ℓ' r'} (σ : Δ ⇒ Γ) where
  ⊞-natural : (T ⊞ S) [ σ ] ≅ᵗʸ (T [ σ ]) ⊞ (S [ σ ])
  func (from ⊞-natural) = id
  func-cong (from ⊞-natural) = id
  naturality (from ⊞-natural) (inj₁ t) = inj₁ (ty≈-refl T)
  naturality (from ⊞-natural) (inj₂ s) = inj₂ (ty≈-refl S)
  func (to ⊞-natural) = id
  func-cong (to ⊞-natural) = id
  naturality (to ⊞-natural) (inj₁ t) = inj₁ (ty≈-refl T)
  naturality (to ⊞-natural) (inj₂ s) = inj₂ (ty≈-refl S)
  eq (isoˡ ⊞-natural) _ = ty≈-refl ((T ⊞ S) [ σ ])
  eq (isoʳ ⊞-natural) _ = ty≈-refl ((T [ σ ]) ⊞ (S [ σ ]))

  inl-natural : (t : Tm Γ T) → (inl t) [ σ ]' ≅ᵗᵐ ι[ ⊞-natural ] (inl (t [ σ ]'))
  eq (inl-natural t) _ = inj₁ (ty≈-refl T)

  inr-natural : (s : Tm Γ S) → (inr s) [ σ ]' ≅ᵗᵐ ι[ ⊞-natural ] (inr (s [ σ ]'))
  eq (inr-natural s) _ = inj₂ (ty≈-refl S)

inl-func : Tm Γ (T ⇛ T ⊞ S)
inl-func {T = T} = lam T (ι[ ⊞-natural π ] inl (var 0))

inr-func : Tm Γ (S ⇛ T ⊞ S)
inr-func {S = S} = lam S (ι[ ⊞-natural π ] inr (var 0))

module _ {A : Ty Γ ℓ r} {B : Ty Γ ℓ' r'} (C : Ty Γ ℓ'' r'') where
  ⊞-elim : Tm Γ (A ⇛ C) → Tm Γ (B ⇛ C) → Tm Γ (A ⊞ B ⇛ C)
  term (⊞-elim f g) _ _ $⟨ _ , _ ⟩ inj₁ a = f €⟨ _ , _ ⟩ a
  term (⊞-elim f g) _ _ $⟨ _ , _ ⟩ inj₂ b = g €⟨ _ , _ ⟩ b
  $-cong (term (⊞-elim f g) _ _) _ _ (inj₁ ea) = €-congʳ f ea
  $-cong (term (⊞-elim f g) _ _) _ _ (inj₂ eb) = €-congʳ g eb
  $-hom-cong (term (⊞-elim f g) _ _) _ {t = inj₁ _} = ty≈-refl C
  $-hom-cong (term (⊞-elim f g) _ _) _ {t = inj₂ _} = ty≈-refl C
  naturality (term (⊞-elim f g) _ _) eq-zy eq-yx (inj₁ a) = ty≈-sym C (€-natural f _ eq-yx a)
  naturality (term (⊞-elim f g) _ _) eq-zy eq-yx (inj₂ b) = ty≈-sym C (€-natural g _ eq-yx b)
  naturality (⊞-elim f g) _ _ _ _ (inj₁ a) = ty≈-refl C
  naturality (⊞-elim f g) _ _ _ _ (inj₂ b) = ty≈-refl C

  β-⊞-inl : (f : Tm Γ (A ⇛ C)) (g : Tm Γ (B ⇛ C)) (a : Tm Γ A) →
            app (⊞-elim f g) (inl a) ≅ᵗᵐ app f a
  eq (β-⊞-inl f g a) _ = ty≈-refl C

  β-⊞-inr : (f : Tm Γ (A ⇛ C)) (g : Tm Γ (B ⇛ C)) (b : Tm Γ B) →
            app (⊞-elim f g) (inr b) ≅ᵗᵐ app g b
  eq (β-⊞-inr f g b) _ = ty≈-refl C

η-⊞ : {A : Ty Γ ℓ} {B : Ty Γ ℓ'} (t : Tm Γ (A ⊞ B)) →
      t ≅ᵗᵐ app (⊞-elim (A ⊞ B) inl-func inr-func) t
eq (η-⊞ t) γ with t ⟨ _ , γ ⟩'
eq (η-⊞ t) γ | inj₁ a = refl
eq (η-⊞ t) γ | inj₂ b = refl
