--------------------------------------------------
-- (Non-dependent) product types
--------------------------------------------------

open import Categories

module Types.Products {C : Category} where

open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_; map) renaming (_,_ to [_,_])
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Function using (id)
open import Level
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms

private
  variable
    ℓc ℓt ℓt' : Level
    Γ Δ : Ctx C ℓ
    T T' S S' : Ty Γ ℓ


_⊠_ : Ty Γ ℓ → Ty Γ ℓ' → Ty Γ (ℓ ⊔ ℓ')
type (T ⊠ S) x γ = type T x γ ×ₛ type S x γ
morph (T ⊠ S) f eγ [ t , s ] = [ T ⟪ f , eγ ⟫ t , S ⟪ f , eγ ⟫ s ]
morph-cong (T ⊠ S) f eγ [ t=t' , s=s' ] = [ morph-cong T f eγ t=t' , morph-cong S f eγ s=s' ]
morph-hom-cong (T ⊠ S) e = [ morph-hom-cong T e , morph-hom-cong S e ]
morph-id (T ⊠ S) [ t , s ] = [ morph-id T t , morph-id S s ]
morph-comp (T ⊠ S) f g eq-zy eq-yx [ t , s ] = [ morph-comp T f g eq-zy eq-yx t , morph-comp S f g eq-zy eq-yx s ]

⊠-bimap : (T ↣ T') → (S ↣ S') → (T ⊠ S ↣ T' ⊠ S')
func (⊠-bimap η φ) = map (func η) (func φ)
func-cong (⊠-bimap η φ) = map (func-cong η) (func-cong φ)
naturality (⊠-bimap η φ) [ t , s ] = [ naturality η t , naturality φ s ]

⊠-cong : T ≅ᵗʸ T' → S ≅ᵗʸ S' → T ⊠ S ≅ᵗʸ T' ⊠ S'
from (⊠-cong T=T' S=S') = ⊠-bimap (from T=T') (from S=S')
to (⊠-cong T=T' S=S') = ⊠-bimap (to T=T') (to S=S')
eq (isoˡ (⊠-cong T=T' S=S')) [ t , s ] = [ eq (isoˡ T=T') t , eq (isoˡ S=S') s ]
eq (isoʳ (⊠-cong T=T' S=S')) [ t , s ] = [ eq (isoʳ T=T') t , eq (isoʳ S=S') s ]

pair : Tm Γ T → Tm Γ S → Tm Γ (T ⊠ S)
term (pair t s) x γ = [ t ⟨ x , γ ⟩' , s ⟨ x , γ ⟩' ]
naturality (pair t s) f eγ = [ naturality t f eγ , naturality s f eγ ]

fst : Tm Γ (T ⊠ S) → Tm Γ T
term (fst p) x γ = proj₁ (p ⟨ x , γ ⟩')
naturality (fst p) f eγ = proj₁ (naturality p f eγ)

snd : Tm Γ (T ⊠ S) → Tm Γ S
term (snd p) x γ = proj₂ (p ⟨ x , γ ⟩')
naturality (snd p) f eγ = proj₂ (naturality p f eγ)

pair-cong : {t t' : Tm Γ T} {s s' : Tm Γ S} → t ≅ᵗᵐ t' → s ≅ᵗᵐ s' → pair t s ≅ᵗᵐ pair t' s'
eq (pair-cong t=t' s=s') γ = [ eq t=t' γ , eq s=s' γ ]

fst-cong : {p p' : Tm Γ (T ⊠ S)} → p ≅ᵗᵐ p' → fst p ≅ᵗᵐ fst p'
eq (fst-cong p=p') γ = proj₁ (eq p=p' γ)

snd-cong : {p p' : Tm Γ (T ⊠ S)} → p ≅ᵗᵐ p' → snd p ≅ᵗᵐ snd p'
eq (snd-cong p=p') γ = proj₂ (eq p=p' γ)

module _ {ℓt ℓt' ℓs ℓs'}
  {T : Ty Γ ℓt} {T' : Ty Γ ℓt'} {S : Ty Γ ℓs} {S' : Ty Γ ℓs'}
  (T=T' : T ≅ᵗʸ T') (S=S' : S ≅ᵗʸ S')
  where
  pair-ι : (t : Tm Γ T') (s : Tm Γ S') → ι[ ⊠-cong T=T' S=S' ] pair t s ≅ᵗᵐ pair (ι[ T=T' ] t) (ι[ S=S' ] s)
  eq (pair-ι t s) _ = ty≈-refl (T ⊠ S)

  fst-ι : (p : Tm Γ (T' ⊠ S')) → ι[ T=T' ] fst p ≅ᵗᵐ fst (ι[ ⊠-cong T=T' S=S' ] p)
  eq (fst-ι p) _ = ty≈-refl T

  snd-ι : (p : Tm Γ (T' ⊠ S')) → ι[ S=S' ] snd p ≅ᵗᵐ snd (ι[ ⊠-cong T=T' S=S' ] p)
  eq (snd-ι p) _ = ty≈-refl S

module _ {T : Ty Γ ℓ} {S : Ty Γ ℓ'} (σ : Δ ⇒ Γ) where
  ⊠-natural : (T ⊠ S) [ σ ] ≅ᵗʸ (T [ σ ]) ⊠ (S [ σ ])
  func (from ⊠-natural) = id
  func-cong (from ⊠-natural) = id
  naturality (from ⊠-natural) _ = ty≈-refl ((T [ σ ]) ⊠ (S [ σ ]))
  func (to ⊠-natural) = id
  func-cong (to ⊠-natural) = id
  naturality (to ⊠-natural) _ = ty≈-refl ((T ⊠ S) [ σ ])
  eq (isoˡ ⊠-natural) _ = ty≈-refl ((T ⊠ S) [ σ ])
  eq (isoʳ ⊠-natural) _ = ty≈-refl ((T [ σ ]) ⊠ (S [ σ ]))

  pair-natural : (t : Tm Γ T) (s : Tm Γ S) → (pair t s) [ σ ]' ≅ᵗᵐ ι[ ⊠-natural ] (pair (t [ σ ]') (s [ σ ]'))
  eq (pair-natural t s) _ = ty≈-refl ((T ⊠ S) [ σ ])

  fst-natural : (p : Tm Γ (T ⊠ S)) → (fst p) [ σ ]' ≅ᵗᵐ fst (ι⁻¹[ ⊠-natural ] (p [ σ ]'))
  eq (fst-natural p) _ = ty≈-refl (T [ σ ])

  snd-natural : (p : Tm Γ (T ⊠ S)) → (snd p) [ σ ]' ≅ᵗᵐ snd (ι⁻¹[ ⊠-natural ] (p [ σ ]'))
  eq (snd-natural p) _ = ty≈-refl (S [ σ ])

module _ {T : Ty Γ ℓ} {S : Ty Γ ℓ'} (t : Tm Γ T) (s : Tm Γ S) where
  β-⊠-fst : fst (pair t s) ≅ᵗᵐ t
  eq β-⊠-fst _ = ty≈-refl T

  β-⊠-snd : snd (pair t s) ≅ᵗᵐ s
  eq β-⊠-snd _ = ty≈-refl S

η-⊠ : (p : Tm Γ (T ⊠ S)) →
      p ≅ᵗᵐ pair (fst p) (snd p)
eq (η-⊠ {T = T}{S = S} p) _ = ty≈-refl (T ⊠ S)
