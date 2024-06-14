--------------------------------------------------
-- Sum types
--------------------------------------------------

open import Model.BaseCategory

module Model.Type.Sum {C : BaseCategory} where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.CwF-Structure
open import Model.Type.Function

private
  variable
    Γ Δ : Ctx C
    T T' S S' : Ty Γ


_⊞_ : Ty Γ → Ty Γ → Ty Γ
T ⊞ S ⟨ x , γ ⟩ = T ⟨ x , γ ⟩ ⊎ S ⟨ x , γ ⟩
T ⊞ S ⟪ f , eγ ⟫ inj₁ t = inj₁ (T ⟪ f , eγ ⟫ t)
T ⊞ S ⟪ f , eγ ⟫ inj₂ s = inj₂ (S ⟪ f , eγ ⟫ s)
ty-cong (T ⊞ S) e {t = inj₁ t} = cong inj₁ (ty-cong T e)
ty-cong (T ⊞ S) e {t = inj₂ s} = cong inj₂ (ty-cong S e)
ty-id (T ⊞ S) {t = inj₁ t} = cong inj₁ (ty-id T)
ty-id (T ⊞ S) {t = inj₂ s} = cong inj₂ (ty-id S)
ty-comp (T ⊞ S) {t = inj₁ t} = cong inj₁ (ty-comp T)
ty-comp (T ⊞ S) {t = inj₂ s} = cong inj₂ (ty-comp S)

⊞-bimap : (T ↣ T') → (S ↣ S') → (T ⊞ S ↣ T' ⊞ S')
func (⊞-bimap η φ) (inj₁ t) = inj₁ (func η t)
func (⊞-bimap η φ) (inj₂ s) = inj₂ (func φ s)
naturality (⊞-bimap η φ) {t = inj₁ t} = cong inj₁ (naturality η)
naturality (⊞-bimap η φ) {t = inj₂ s} = cong inj₂ (naturality φ)

⊞-cong : T ≅ᵗʸ T' → S ≅ᵗʸ S' → T ⊞ S ≅ᵗʸ T' ⊞ S'
from (⊞-cong T=T' S=S') = ⊞-bimap (from T=T') (from S=S')
to (⊞-cong T=T' S=S') = ⊞-bimap (to T=T') (to S=S')
eq (isoˡ (⊞-cong T=T' S=S')) (inj₁ t) = cong inj₁ (eq (isoˡ T=T') t)
eq (isoˡ (⊞-cong T=T' S=S')) (inj₂ s) = cong inj₂ (eq (isoˡ S=S') s)
eq (isoʳ (⊞-cong T=T' S=S')) (inj₁ t) = cong inj₁ (eq (isoʳ T=T') t)
eq (isoʳ (⊞-cong T=T' S=S')) (inj₂ s) = cong inj₂ (eq (isoʳ S=S') s)

⊞-cong-trans : {T T' T'' S S' S'' : Ty Γ}
               {T=T' : T ≅ᵗʸ T'} {T'=T'' : T' ≅ᵗʸ T''} {S=S' : S ≅ᵗʸ S'} {S'=S'' : S' ≅ᵗʸ S''} →
               ⊞-cong (transᵗʸ T=T' T'=T'') (transᵗʸ S=S' S'=S'') ≅ᵉ transᵗʸ (⊞-cong T=T' S=S') (⊞-cong T'=T'' S'=S'')
eq (from-eq ⊞-cong-trans) (inj₁ t) = refl
eq (from-eq ⊞-cong-trans) (inj₂ s) = refl

⊞-cong-cong : {T1 T2 S1 S2 : Ty Γ} {eT eT' : T1 ≅ᵗʸ T2} {eS eS' : S1 ≅ᵗʸ S2} →
              eT ≅ᵉ eT' → eS ≅ᵉ eS' → ⊞-cong eT eS ≅ᵉ ⊞-cong eT' eS'
eq (from-eq (⊞-cong-cong 𝑒T 𝑒S)) (inj₁ t) = cong inj₁ (eq (from-eq 𝑒T) t)
eq (from-eq (⊞-cong-cong 𝑒T 𝑒S)) (inj₂ s) = cong inj₂ (eq (from-eq 𝑒S) s)


inl : Tm Γ T → Tm Γ (T ⊞ S)
inl t ⟨ x , γ ⟩' = inj₁ (t ⟨ x , γ ⟩')
naturality (inl t) f eγ = cong inj₁ (naturality t f eγ)

inr : Tm Γ S → Tm Γ (T ⊞ S)
inr s ⟨ x , γ ⟩' = inj₂ (s ⟨ x , γ ⟩')
naturality (inr s) f eγ = cong inj₂ (naturality s f eγ)

inl⟨_⟩_ : (S : Ty Γ) (t : Tm Γ T) → Tm Γ (T ⊞ S)
inl⟨ S ⟩ t = inl {S = S} t

inr⟨_⟩_ : (T : Ty Γ) (s : Tm Γ S) → Tm Γ (T ⊞ S)
inr⟨ T ⟩ s = inr {T = T} s

module _ {T S : Ty Γ} where
  inl-cong : {t t' : Tm Γ T} → t ≅ᵗᵐ t' → inl⟨ S ⟩ t ≅ᵗᵐ inl t'
  eq (inl-cong t=t') γ = cong inj₁ (eq t=t' γ)

  inr-cong : {s s' : Tm Γ S} → s ≅ᵗᵐ s' → inr⟨ T ⟩ s ≅ᵗᵐ inr s'
  eq (inr-cong s=s') γ = cong inj₂ (eq s=s' γ)

module _
  {T : Ty Γ} {T' : Ty Γ} {S : Ty Γ} {S' : Ty Γ}
  {T=T' : T ≅ᵗʸ T'} {S=S' : S ≅ᵗʸ S'}
  where

  inl-ι : (t : Tm Γ T') → ι[ ⊞-cong T=T' S=S' ] inl t ≅ᵗᵐ inl (ι[ T=T' ] t)
  eq (inl-ι t) _ = refl

  inl-ι⁻¹ : (t : Tm Γ T) → ι⁻¹[ ⊞-cong T=T' S=S' ] inl t ≅ᵗᵐ inl (ι⁻¹[ T=T' ] t)
  eq (inl-ι⁻¹ t) _ = refl

  inr-ι : (s : Tm Γ S') → ι[ ⊞-cong T=T' S=S' ] inr s ≅ᵗᵐ inr (ι[ S=S' ] s)
  eq (inr-ι s) _ = refl

  inr-ι⁻¹ : (s : Tm Γ S) → ι⁻¹[ ⊞-cong T=T' S=S' ] inr s ≅ᵗᵐ inr (ι⁻¹[ S=S' ] s)
  eq (inr-ι⁻¹ s) _ = refl

module _ {T : Ty Γ} {S : Ty Γ} (σ : Δ ⇒ Γ) where
  ⊞-natural : (T ⊞ S) [ σ ] ≅ᵗʸ (T [ σ ]) ⊞ (S [ σ ])
  func (from ⊞-natural) = id
  naturality (from ⊞-natural) {t = inj₁ t} = refl
  naturality (from ⊞-natural) {t = inj₂ s} = refl
  func (to ⊞-natural) = id
  naturality (to ⊞-natural) {t = inj₁ t} = refl
  naturality (to ⊞-natural) {t = inj₂ s} = refl
  eq (isoˡ ⊞-natural) _ = refl
  eq (isoʳ ⊞-natural) _ = refl

  inl-natural : (t : Tm Γ T) → (inl t) [ σ ]' ≅ᵗᵐ ι[ ⊞-natural ] (inl (t [ σ ]'))
  eq (inl-natural t) _ = refl

  inr-natural : (s : Tm Γ S) → (inr s) [ σ ]' ≅ᵗᵐ ι[ ⊞-natural ] (inr (s [ σ ]'))
  eq (inr-natural s) _ = refl

⊞-natural-cong : {T T' S S' : Ty Δ} {σ : Γ ⇒ Δ} {T=T' : T ≅ᵗʸ T'} {S=S' : S ≅ᵗʸ S'} →
                 transᵗʸ (ty-subst-cong-ty σ (⊞-cong T=T' S=S')) (⊞-natural σ)
                   ≅ᵉ
                 transᵗʸ (⊞-natural σ) (⊞-cong (ty-subst-cong-ty σ T=T') (ty-subst-cong-ty σ S=S'))
eq (from-eq ⊞-natural-cong) (inj₁ t) = refl
eq (from-eq ⊞-natural-cong) (inj₂ s) = refl

inl-func : Tm Γ (T ⇛ T ⊞ S)
inl-func {T = T} = lam T (ι[ ⊞-natural π ] inl ξ)

inr-func : Tm Γ (S ⇛ T ⊞ S)
inr-func {S = S} = lam S (ι[ ⊞-natural π ] inr ξ)

module _ {A : Ty Γ} {B : Ty Γ} (C : Ty Γ) where
  ⊞-elim : Tm Γ (A ⇛ C) → Tm Γ (B ⇛ C) → Tm Γ (A ⊞ B ⇛ C)
  (⊞-elim f g ⟨ _ , _ ⟩') $⟨ _ , _ ⟩ inj₁ a = f €⟨ _ , _ ⟩ a
  (⊞-elim f g ⟨ _ , _ ⟩') $⟨ _ , _ ⟩ inj₂ b = g €⟨ _ , _ ⟩ b
  naturality (⊞-elim f g ⟨ _ , _ ⟩') {t = inj₁ a} = sym (€-natural f)
  naturality (⊞-elim f g ⟨ _ , _ ⟩') {t = inj₂ b} = sym (€-natural g)
  naturality (⊞-elim f g) _ _ = to-pshfun-eq λ { _ _ (inj₁ a) → refl ; _ _ (inj₂ b) → refl }

  ⊞-β-inl : (f : Tm Γ (A ⇛ C)) (g : Tm Γ (B ⇛ C)) (a : Tm Γ A) →
            app (⊞-elim f g) (inl a) ≅ᵗᵐ app f a
  eq (⊞-β-inl f g a) _ = refl

  ⊞-β-inr : (f : Tm Γ (A ⇛ C)) (g : Tm Γ (B ⇛ C)) (b : Tm Γ B) →
            app (⊞-elim f g) (inr b) ≅ᵗᵐ app g b
  eq (⊞-β-inr f g b) _ = refl

⊞-η : {A : Ty Γ} {B : Ty Γ} (t : Tm Γ (A ⊞ B)) →
      t ≅ᵗᵐ app (⊞-elim (A ⊞ B) inl-func inr-func) t
eq (⊞-η t) γ with t ⟨ _ , γ ⟩'
eq (⊞-η t) γ | inj₁ a = refl
eq (⊞-η t) γ | inj₂ b = refl

module _ {A B : ClosedTy C} (clA : IsClosedNatural A) (clB : IsClosedNatural B) where
  sum-closed : IsClosedNatural (A ⊞ B)
  closed-natural sum-closed σ = transᵗʸ (⊞-natural σ) (⊞-cong (closed-natural clA σ) (closed-natural clB σ))
  eq (from-eq (closed-id sum-closed)) (inj₁ a) = cong inj₁ (eq (from-eq (closed-id clA)) a)
  eq (from-eq (closed-id sum-closed)) (inj₂ b) = cong inj₂ (eq (from-eq (closed-id clB)) b)
  eq (from-eq (closed-⊚ sum-closed σ τ)) (inj₁ a) = cong inj₁ (eq (from-eq (closed-⊚ clA σ τ)) a)
  eq (from-eq (closed-⊚ sum-closed σ τ)) (inj₂ b) = cong inj₂ (eq (from-eq (closed-⊚ clB σ τ)) b)
  eq (from-eq (closed-subst-eq sum-closed ε)) (inj₁ a) = cong inj₁ (eq (from-eq (closed-subst-eq clA ε)) a)
  eq (from-eq (closed-subst-eq sum-closed ε)) (inj₂ b) = cong inj₂ (eq (from-eq (closed-subst-eq clB ε)) b)

  inl-cl-natural : {σ : Γ ⇒ Δ} {a : Tm Δ A} → (inl a) [ sum-closed ∣ σ ]cl ≅ᵗᵐ inl (a [ clA ∣ σ ]cl)
  inl-cl-natural = transᵗᵐ (ι⁻¹-cong (inl-natural _ _)) (transᵗᵐ ι⁻¹-trans (transᵗᵐ (ι⁻¹-cong ι-symˡ) (inl-ι⁻¹ _)))

  inr-cl-natural : {σ : Γ ⇒ Δ} {b : Tm Δ B} → (inr b) [ sum-closed ∣ σ ]cl ≅ᵗᵐ inr (b [ clB ∣ σ ]cl)
  inr-cl-natural = transᵗᵐ (ι⁻¹-cong (inr-natural _ _)) (transᵗᵐ ι⁻¹-trans (transᵗᵐ (ι⁻¹-cong ι-symˡ) (inr-ι⁻¹ _)))

⊞-closed-cong : {A A' B B' : ClosedTy C}
                {clA : IsClosedNatural A} {clA' : IsClosedNatural A'} {clB : IsClosedNatural B} {clB' : IsClosedNatural B'} →
                clA ≅ᶜᵗʸ clA' → clB ≅ᶜᵗʸ clB' → sum-closed clA clB ≅ᶜᵗʸ sum-closed clA' clB'
closed-ty-eq (⊞-closed-cong eA eB) = ⊞-cong (closed-ty-eq eA) (closed-ty-eq eB)
closed-ty-eq-natural (⊞-closed-cong eA eB) σ =
  transᵉ (symᵉ transᵗʸ-assoc) (
  transᵉ (transᵗʸ-congˡ ⊞-natural-cong) (
  transᵉ transᵗʸ-assoc (
  transᵉ (transᵗʸ-congʳ (transᵉ (symᵉ ⊞-cong-trans) (
                         transᵉ (⊞-cong-cong (closed-ty-eq-natural eA _) (closed-ty-eq-natural eB _))
                         ⊞-cong-trans))) (
  symᵉ transᵗʸ-assoc))))
