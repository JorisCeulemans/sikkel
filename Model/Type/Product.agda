--------------------------------------------------
-- (Non-dependent) product types
--------------------------------------------------

open import Model.BaseCategory

module Model.Type.Product {C : Category} where

open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Function using (id)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.CwF-Structure
open import Model.Type.Function

private
  variable
    Γ Δ : Ctx C
    T T' S S' : Ty Γ


_⊠_ : Ty Γ → Ty Γ → Ty Γ
T ⊠ S ⟨ x , γ ⟩ = T ⟨ x , γ ⟩ × S ⟨ x , γ ⟩
T ⊠ S ⟪ f , eγ ⟫ [ t , s ] = [ T ⟪ f , eγ ⟫ t , S ⟪ f , eγ ⟫ s ]
ty-cong (T ⊠ S) e = cong₂ [_,_] (ty-cong T e) (ty-cong S e)
ty-id (T ⊠ S) = cong₂ [_,_] (ty-id T) (ty-id S)
ty-comp (T ⊠ S) = cong₂ [_,_] (ty-comp T) (ty-comp S)

⊠-bimap : (T ↣ T') → (S ↣ S') → (T ⊠ S ↣ T' ⊠ S')
func (⊠-bimap η φ) [ t , s ] = [ func η t , func φ s ]
naturality (⊠-bimap η φ) = cong₂ [_,_] (naturality η) (naturality φ)

⊠-cong : T ≅ᵗʸ T' → S ≅ᵗʸ S' → T ⊠ S ≅ᵗʸ T' ⊠ S'
from (⊠-cong T=T' S=S') = ⊠-bimap (from T=T') (from S=S')
to (⊠-cong T=T' S=S') = ⊠-bimap (to T=T') (to S=S')
eq (isoˡ (⊠-cong T=T' S=S')) [ t , s ] = cong₂ [_,_] (eq (isoˡ T=T') t) (eq (isoˡ S=S') s)
eq (isoʳ (⊠-cong T=T' S=S')) [ t , s ] = cong₂ [_,_] (eq (isoʳ T=T') t) (eq (isoʳ S=S') s)

-- The term constructors prim-pair, prim-fst and prim-snd take one or more Sikkel terms
--   to produce a new Sikkel term. These operations are also available as Sikkel functions
--   (i.e. terms of Sikkel's function type) named pair, fst and snd defined below.
prim-pair : Tm Γ T → Tm Γ S → Tm Γ (T ⊠ S)
prim-pair t s ⟨ x , γ ⟩' = [ t ⟨ x , γ ⟩' , s ⟨ x , γ ⟩' ]
naturality (prim-pair t s) f eγ = cong₂ [_,_] (naturality t f eγ) (naturality s f eγ)

prim-fst : Tm Γ (T ⊠ S) → Tm Γ T
prim-fst p ⟨ x , γ ⟩' = proj₁ (p ⟨ x , γ ⟩')
naturality (prim-fst p) f eγ = cong proj₁ (naturality p f eγ)

prim-snd : Tm Γ (T ⊠ S) → Tm Γ S
prim-snd p ⟨ x , γ ⟩' = proj₂ (p ⟨ x , γ ⟩')
naturality (prim-snd p) f eγ = cong proj₂ (naturality p f eγ)

prim-pair-cong : {t t' : Tm Γ T} {s s' : Tm Γ S} → t ≅ᵗᵐ t' → s ≅ᵗᵐ s' → prim-pair t s ≅ᵗᵐ prim-pair t' s'
eq (prim-pair-cong t=t' s=s') γ = cong₂ [_,_] (eq t=t' γ) (eq s=s' γ)

prim-fst-cong : {p p' : Tm Γ (T ⊠ S)} → p ≅ᵗᵐ p' → prim-fst p ≅ᵗᵐ prim-fst p'
eq (prim-fst-cong p=p') γ = cong proj₁ (eq p=p' γ)

prim-snd-cong : {p p' : Tm Γ (T ⊠ S)} → p ≅ᵗᵐ p' → prim-snd p ≅ᵗᵐ prim-snd p'
eq (prim-snd-cong p=p') γ = cong proj₂ (eq p=p' γ)

module _
  {T : Ty Γ} {T' : Ty Γ} {S : Ty Γ} {S' : Ty Γ}
  (T=T' : T ≅ᵗʸ T') (S=S' : S ≅ᵗʸ S')
  where
  prim-pair-ι : (t : Tm Γ T') (s : Tm Γ S') → ι[ ⊠-cong T=T' S=S' ] prim-pair t s ≅ᵗᵐ prim-pair (ι[ T=T' ] t) (ι[ S=S' ] s)
  eq (prim-pair-ι t s) _ = refl

  prim-fst-ι : (p : Tm Γ (T' ⊠ S')) → ι[ T=T' ] prim-fst p ≅ᵗᵐ prim-fst (ι[ ⊠-cong T=T' S=S' ] p)
  eq (prim-fst-ι p) _ = refl

  prim-snd-ι : (p : Tm Γ (T' ⊠ S')) → ι[ S=S' ] prim-snd p ≅ᵗᵐ prim-snd (ι[ ⊠-cong T=T' S=S' ] p)
  eq (prim-snd-ι p) _ = refl

module _ {T : Ty Γ} {S : Ty Γ} (σ : Δ ⇒ Γ) where
  ⊠-natural : (T ⊠ S) [ σ ] ≅ᵗʸ (T [ σ ]) ⊠ (S [ σ ])
  func (from ⊠-natural) = id
  naturality (from ⊠-natural) = refl
  func (to ⊠-natural) = id
  naturality (to ⊠-natural) = refl
  eq (isoˡ ⊠-natural) _ = refl
  eq (isoʳ ⊠-natural) _ = refl

  prim-pair-natural : (t : Tm Γ T) (s : Tm Γ S) → (prim-pair t s) [ σ ]' ≅ᵗᵐ ι[ ⊠-natural ] (prim-pair (t [ σ ]') (s [ σ ]'))
  eq (prim-pair-natural t s) _ = refl

  prim-fst-natural : (p : Tm Γ (T ⊠ S)) → (prim-fst p) [ σ ]' ≅ᵗᵐ prim-fst (ι⁻¹[ ⊠-natural ] (p [ σ ]'))
  eq (prim-fst-natural p) _ = refl

  prim-snd-natural : (p : Tm Γ (T ⊠ S)) → (prim-snd p) [ σ ]' ≅ᵗᵐ prim-snd (ι⁻¹[ ⊠-natural ] (p [ σ ]'))
  eq (prim-snd-natural p) _ = refl

module _ (t : Tm Γ T) (s : Tm Γ S) where
  β-⊠-prim-fst : prim-fst (prim-pair t s) ≅ᵗᵐ t
  eq β-⊠-prim-fst _ = refl

  β-⊠-prim-snd : prim-snd (prim-pair t s) ≅ᵗᵐ s
  eq β-⊠-prim-snd _ = refl

η-⊠ : (p : Tm Γ (T ⊠ S)) →
      p ≅ᵗᵐ prim-pair (prim-fst p) (prim-snd p)
eq (η-⊠ p) _ = refl

pair : Tm Γ (T ⇛ S ⇛ T ⊠ S)
pair {T = T}{S = S} =
  lam T (ι[ ⇛-natural π ]
    lam (S [ π ]) (ι[ ≅ᵗʸ-trans (ty-subst-cong-ty π (⊠-natural π)) (⊠-natural π) ]
      prim-pair (ξ [ π ]') ξ))

fst : Tm Γ (T ⊠ S ⇛ T)
fst {T = T}{S = S} = lam (T ⊠ S) (prim-fst (ι⁻¹[ ⊠-natural π ] ξ))

snd : Tm Γ (T ⊠ S ⇛ S)
snd {T = T}{S = S} = lam (T ⊠ S) (prim-snd (ι⁻¹[ ⊠-natural π ] ξ))

instance
  prod-closed : {A B : ClosedType C} {{_ : IsClosedNatural A}} {{_ : IsClosedNatural B}} →
                IsClosedNatural (A ⊠ B)
  closed-natural {{prod-closed}} σ = ≅ᵗʸ-trans (⊠-natural σ) (⊠-cong (closed-natural σ) (closed-natural σ))
