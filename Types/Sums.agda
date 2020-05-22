open import Categories

module Types.Sums {C : Category} where

-- open import Data.Nat hiding (_⊔_)
-- open import Data.Nat.Properties
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Function using (id)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types {C = C}
open import CwF-Structure.Terms {C = C}

--------------------------------------------------
-- Sum types
--------------------------------------------------

_⊞_ : {Γ : Ctx C ℓ} → Ty Γ → Ty Γ → Ty Γ
type (T ⊞ S) x γ = T ⟨ x , γ ⟩ ⊎ S ⟨ x , γ ⟩
morph (T ⊞ S) f eγ (inl t) = inl (T ⟪ f , eγ ⟫ t)
morph (T ⊞ S) f eγ (inr s) = inr (S ⟪ f , eγ ⟫ s)
morph-id (T ⊞ S) (inl t) = cong inl (morph-id T t)
morph-id (T ⊞ S) (inr s) = cong inr (morph-id S s)
morph-comp (T ⊞ S) f g eq-nm eq-mk (inl t) = cong inl (morph-comp T f g eq-nm eq-mk t)
morph-comp (T ⊞ S) f g eq-nm eq-mk (inr s) = cong inr (morph-comp S f g eq-nm eq-mk s)

⊞-bimap : {Γ : Ctx C ℓ} {T T' S S' : Ty Γ} → (T ↣ T') → (S ↣ S') → (T ⊞ S ↣ T' ⊞ S')
func (⊞-bimap η φ) (inl t) = inl (func η t)
func (⊞-bimap η φ) (inr s) = inr (func φ s)
naturality (⊞-bimap η φ) (inl t) = cong inl (naturality η t)
naturality (⊞-bimap η φ) (inr s) = cong inr (naturality φ s)

⊞-cong : {Γ : Ctx C ℓ} {T T' S S' : Ty Γ} → T ≅ᵗʸ T' → S ≅ᵗʸ S' → T ⊞ S ≅ᵗʸ T' ⊞ S'
from (⊞-cong T=T' S=S') = ⊞-bimap (from T=T') (from S=S')
to (⊞-cong T=T' S=S') = ⊞-bimap (to T=T') (to S=S')
eq (isoˡ (⊞-cong T=T' S=S')) (inl t) = cong inl (eq (isoˡ T=T') t)
eq (isoˡ (⊞-cong T=T' S=S')) (inr s) = cong inr (eq (isoˡ S=S') s)
eq (isoʳ (⊞-cong T=T' S=S')) (inl t) = cong inl (eq (isoʳ T=T') t)
eq (isoʳ (⊞-cong T=T' S=S')) (inr s) = cong inr (eq (isoʳ S=S') s)

module _ {Γ : Ctx C ℓ} {T S : Ty Γ} where
  inl' : Tm Γ T → Tm Γ (T ⊞ S)
  term (inl' t) x γ = inl (t ⟨ x , γ ⟩')
  naturality (inl' t) f eγ = cong inl (naturality t f eγ)

  inr' : Tm Γ S → Tm Γ (T ⊞ S)
  term (inr' s) x γ = inr (s ⟨ x , γ ⟩')
  naturality (inr' s) f eγ = cong inr (naturality s f eγ)

  inl'-cong : {t t' : Tm Γ T} → t ≅ᵗᵐ t' → inl' t ≅ᵗᵐ inl' t'
  eq (inl'-cong t=t') γ = cong inl (eq t=t' γ)

  inr'-cong : {s s' : Tm Γ S} → s ≅ᵗᵐ s' → inr' s ≅ᵗᵐ inr' s'
  eq (inr'-cong s=s') γ = cong inr (eq s=s' γ)

inl'⟨_⟩_ : {Γ : Ctx C ℓ} {T : Ty Γ} (S : Ty Γ) (t : Tm Γ T) → Tm Γ (T ⊞ S)
inl'⟨ S ⟩ t = inl' {S = S} t

inr'⟨_⟩_ : {Γ : Ctx C ℓ} (T : Ty Γ) {S : Ty Γ} (s : Tm Γ S) → Tm Γ (T ⊞ S)
inr'⟨ T ⟩ s = inr' {T = T} s

module _ {Γ : Ctx C ℓ} {T T' S S' : Ty Γ} (T=T' : T ≅ᵗʸ T') (S=S' : S ≅ᵗʸ S') where
  inl'-ι : (t : Tm Γ T') → ι[ ⊞-cong T=T' S=S' ] inl' t ≅ᵗᵐ inl' (ι[ T=T' ] t)
  eq (inl'-ι t) _ = refl

  inr'-ι : (s : Tm Γ S') → ι[ ⊞-cong T=T' S=S' ] inr' s ≅ᵗᵐ inr' (ι[ S=S' ] s)
  eq (inr'-ι s) _ = refl

module _ {Δ Γ : Ctx C ℓ} {T S : Ty Γ} (σ : Δ ⇒ Γ) where
  ⊞-natural : (T ⊞ S) [ σ ] ≅ᵗʸ (T [ σ ]) ⊞ (S [ σ ])
  from ⊞-natural = record { func = id ; naturality = λ { (inl t) → refl ; (inr s) → refl } }
  to ⊞-natural = record { func = id ; naturality = λ { (inl t) → refl ; (inr s) → refl } }
  eq (isoˡ ⊞-natural) _ = refl
  eq (isoʳ ⊞-natural) _ = refl

  inl'-natural : (t : Tm Γ T) → (inl' t) [ σ ]' ≅ᵗᵐ ι[ ⊞-natural ] (inl' (t [ σ ]'))
  eq (inl'-natural t) _ = refl

  inr'-natural : (s : Tm Γ S) → (inr' s) [ σ ]' ≅ᵗᵐ ι[ ⊞-natural ] (inr' (s [ σ ]'))
  eq (inr'-natural s) _ = refl
