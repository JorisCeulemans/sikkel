--------------------------------------------------
-- (Non-dependent) product types
--------------------------------------------------

open import Model.BaseCategory

module Model.Type.Product {C : BaseCategory} where

open BaseCategory C

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

⊠-cong-trans : {T T' T'' S S' S'' : Ty Γ}
               {T=T' : T ≅ᵗʸ T'} {T'=T'' : T' ≅ᵗʸ T''} {S=S' : S ≅ᵗʸ S'} {S'=S'' : S' ≅ᵗʸ S''} →
               ⊠-cong (transᵗʸ T=T' T'=T'') (transᵗʸ S=S' S'=S'') ≅ᵉ transᵗʸ (⊠-cong T=T' S=S') (⊠-cong T'=T'' S'=S'')
eq (from-eq ⊠-cong-trans) _ = refl

⊠-cong-cong : {T1 T2 S1 S2 : Ty Γ} {eT eT' : T1 ≅ᵗʸ T2} {eS eS' : S1 ≅ᵗʸ S2} →
              eT ≅ᵉ eT' → eS ≅ᵉ eS' → ⊠-cong eT eS ≅ᵉ ⊠-cong eT' eS'
eq (from-eq (⊠-cong-cong 𝑒T 𝑒S)) [ t , s ] = cong₂ [_,_] (eq (from-eq 𝑒T) t) (eq (from-eq 𝑒S) s)


pair : Tm Γ T → Tm Γ S → Tm Γ (T ⊠ S)
pair t s ⟨ x , γ ⟩' = [ t ⟨ x , γ ⟩' , s ⟨ x , γ ⟩' ]
naturality (pair t s) f eγ = cong₂ [_,_] (naturality t f eγ) (naturality s f eγ)

fst : Tm Γ (T ⊠ S) → Tm Γ T
fst p ⟨ x , γ ⟩' = proj₁ (p ⟨ x , γ ⟩')
naturality (fst p) f eγ = cong proj₁ (naturality p f eγ)

snd : Tm Γ (T ⊠ S) → Tm Γ S
snd p ⟨ x , γ ⟩' = proj₂ (p ⟨ x , γ ⟩')
naturality (snd p) f eγ = cong proj₂ (naturality p f eγ)

pair-cong : {t t' : Tm Γ T} {s s' : Tm Γ S} → t ≅ᵗᵐ t' → s ≅ᵗᵐ s' → pair t s ≅ᵗᵐ pair t' s'
eq (pair-cong t=t' s=s') γ = cong₂ [_,_] (eq t=t' γ) (eq s=s' γ)

fst-cong : {p p' : Tm Γ (T ⊠ S)} → p ≅ᵗᵐ p' → fst p ≅ᵗᵐ fst p'
eq (fst-cong p=p') γ = cong proj₁ (eq p=p' γ)

snd-cong : {p p' : Tm Γ (T ⊠ S)} → p ≅ᵗᵐ p' → snd p ≅ᵗᵐ snd p'
eq (snd-cong p=p') γ = cong proj₂ (eq p=p' γ)

module _
  {T : Ty Γ} {T' : Ty Γ} {S : Ty Γ} {S' : Ty Γ}
  {T=T' : T ≅ᵗʸ T'} {S=S' : S ≅ᵗʸ S'}
  where
  pair-ι : (t : Tm Γ T') (s : Tm Γ S') → ι[ ⊠-cong T=T' S=S' ] pair t s ≅ᵗᵐ pair (ι[ T=T' ] t) (ι[ S=S' ] s)
  eq (pair-ι t s) _ = refl

  pair-ι⁻¹ : (t : Tm Γ T) (s : Tm Γ S) → ι⁻¹[ ⊠-cong T=T' S=S' ] pair t s ≅ᵗᵐ pair (ι⁻¹[ T=T' ] t) (ι⁻¹[ S=S' ] s)
  eq (pair-ι⁻¹ t s) _ = refl

  fst-ι : (p : Tm Γ (T' ⊠ S')) → ι[ T=T' ] fst p ≅ᵗᵐ fst (ι[ ⊠-cong T=T' S=S' ] p)
  eq (fst-ι p) _ = refl

  fst-ι⁻¹ : (p : Tm Γ (T ⊠ S)) → ι⁻¹[ T=T' ] fst p ≅ᵗᵐ fst (ι⁻¹[ ⊠-cong T=T' S=S' ] p)
  eq (fst-ι⁻¹ p) _ = refl

  snd-ι : (p : Tm Γ (T' ⊠ S')) → ι[ S=S' ] snd p ≅ᵗᵐ snd (ι[ ⊠-cong T=T' S=S' ] p)
  eq (snd-ι p) _ = refl

  snd-ι⁻¹ : (p : Tm Γ (T ⊠ S)) → ι⁻¹[ S=S' ] snd p ≅ᵗᵐ snd (ι⁻¹[ ⊠-cong T=T' S=S' ] p)
  eq (snd-ι⁻¹ p) _ = refl

module _ {T : Ty Γ} {S : Ty Γ} (σ : Δ ⇒ Γ) where
  ⊠-natural : (T ⊠ S) [ σ ] ≅ᵗʸ (T [ σ ]) ⊠ (S [ σ ])
  func (from ⊠-natural) = id
  naturality (from ⊠-natural) = refl
  func (to ⊠-natural) = id
  naturality (to ⊠-natural) = refl
  eq (isoˡ ⊠-natural) _ = refl
  eq (isoʳ ⊠-natural) _ = refl

  pair-natural : (t : Tm Γ T) (s : Tm Γ S) → (pair t s) [ σ ]' ≅ᵗᵐ ι[ ⊠-natural ] (pair (t [ σ ]') (s [ σ ]'))
  eq (pair-natural t s) _ = refl

  fst-natural : (p : Tm Γ (T ⊠ S)) → (fst p) [ σ ]' ≅ᵗᵐ fst (ι⁻¹[ ⊠-natural ] (p [ σ ]'))
  eq (fst-natural p) _ = refl

  snd-natural : (p : Tm Γ (T ⊠ S)) → (snd p) [ σ ]' ≅ᵗᵐ snd (ι⁻¹[ ⊠-natural ] (p [ σ ]'))
  eq (snd-natural p) _ = refl

⊠-natural-cong : {T T' S S' : Ty Δ} {σ : Γ ⇒ Δ} {T=T' : T ≅ᵗʸ T'} {S=S' : S ≅ᵗʸ S'} →
                 transᵗʸ (ty-subst-cong-ty σ (⊠-cong T=T' S=S')) (⊠-natural σ)
                   ≅ᵉ
                 transᵗʸ (⊠-natural σ) (⊠-cong (ty-subst-cong-ty σ T=T') (ty-subst-cong-ty σ S=S'))
eq (from-eq ⊠-natural-cong) _ = refl

module _ (t : Tm Γ T) (s : Tm Γ S) where
  ⊠-β-fst : fst (pair t s) ≅ᵗᵐ t
  eq ⊠-β-fst _ = refl

  ⊠-β-snd : snd (pair t s) ≅ᵗᵐ s
  eq ⊠-β-snd _ = refl

⊠-η : (p : Tm Γ (T ⊠ S)) →
      p ≅ᵗᵐ pair (fst p) (snd p)
eq (⊠-η p) _ = refl

-- Versions of the term constructors pair, fst and snd as Sikkel
--   functions (i.e. terms of Sikkel's function type) instead of
--   operations that take one or more Sikkel terms to produce a new
--   Sikkel term.

pairᶠ : Tm Γ (T ⇛ S ⇛ T ⊠ S)
pairᶠ {T = T}{S = S} =
  lam T (ι[ ⇛-natural π ]
    lam (S [ π ]) (ι[ transᵗʸ (ty-subst-cong-ty π (⊠-natural π)) (⊠-natural π) ]
      pair (ξ [ π ]') ξ))

fstᶠ : Tm Γ (T ⊠ S ⇛ T)
fstᶠ {T = T}{S = S} = lam (T ⊠ S) (fst (ι⁻¹[ ⊠-natural π ] ξ))

sndᶠ : Tm Γ (T ⊠ S ⇛ S)
sndᶠ {T = T}{S = S} = lam (T ⊠ S) (snd (ι⁻¹[ ⊠-natural π ] ξ))

module _ (t : Tm Γ T) (s : Tm Γ S) where
  ⊠-β-fstᶠ : (app fstᶠ (app (app pairᶠ t) s)) ≅ᵗᵐ t
  eq ⊠-β-fstᶠ γ = trans (ty-cong-2-1 T hom-idʳ) (ty-id T)

  ⊠-β-sndᶠ : (app sndᶠ (app (app pairᶠ t) s)) ≅ᵗᵐ s
  eq ⊠-β-sndᶠ γ = trans (ty-cong-2-1 S hom-idʳ) (ty-id S)

⊠-ηᶠ : (p : Tm Γ (T ⊠ S)) → p ≅ᵗᵐ app (app pairᶠ (app fstᶠ p)) (app sndᶠ p)
eq (⊠-ηᶠ {T = T} {S = S} p) γ = sym (cong₂ [_,_] (trans (ty-cong-2-1 T hom-idʳ) (ty-id T))
                                                 (trans (ty-cong-2-1 S hom-idʳ) (ty-id S)))

module _ {A B : ClosedTy C} (clA : IsClosedNatural A) (clB : IsClosedNatural B) where
  prod-closed : IsClosedNatural (A ⊠ B)
  closed-natural prod-closed σ = transᵗʸ (⊠-natural σ) (⊠-cong (closed-natural clA σ) (closed-natural clB σ))
  eq (from-eq (closed-id prod-closed)) [ a , b ] = cong₂ [_,_] (eq (from-eq (closed-id clA)) a) (eq (from-eq (closed-id clB)) b)
  eq (from-eq (closed-⊚ prod-closed σ τ)) [ a , b ] = cong₂ [_,_] (eq (from-eq (closed-⊚ clA σ τ)) a) (eq (from-eq (closed-⊚ clB σ τ)) b)
  eq (from-eq (closed-subst-eq prod-closed ε)) [ a , b ] = cong₂ [_,_] (eq (from-eq (closed-subst-eq clA ε)) a) (eq (from-eq (closed-subst-eq clB ε)) b)

  pair-cl-natural : {σ : Γ ⇒ Δ} {a : Tm Δ A} {b : Tm Δ B} →
                    (pair a b) [ prod-closed ∣ σ ]cl ≅ᵗᵐ pair (a [ clA ∣ σ ]cl) (b [ clB ∣ σ ]cl)
  pair-cl-natural = transᵗᵐ (ι⁻¹-cong (pair-natural _ _ _)) (transᵗᵐ ι⁻¹-trans (transᵗᵐ (ι⁻¹-cong ι-symˡ) (pair-ι⁻¹ _ _)))

  fst-cl-natural : {σ : Γ ⇒ Δ} {p : Tm Δ (A ⊠ B)} →
                   (fst p) [ clA ∣ σ ]cl ≅ᵗᵐ fst (p [ prod-closed ∣ σ ]cl)
  fst-cl-natural = transᵗᵐ (ι⁻¹-cong (fst-natural _ _)) (transᵗᵐ (fst-ι⁻¹ _) (fst-cong (symᵗᵐ ι⁻¹-trans)))

  snd-cl-natural : {σ : Γ ⇒ Δ} {p : Tm Δ (A ⊠ B)} →
                   (snd p) [ clB ∣ σ ]cl ≅ᵗᵐ snd (p [ prod-closed ∣ σ ]cl)
  snd-cl-natural = transᵗᵐ (ι⁻¹-cong (snd-natural _ _)) (transᵗᵐ (snd-ι⁻¹ _) (snd-cong (symᵗᵐ ι⁻¹-trans)))

⊠-closed-cong : {A A' B B' : ClosedTy C}
                {clA : IsClosedNatural A} {clA' : IsClosedNatural A'} {clB : IsClosedNatural B} {clB' : IsClosedNatural B'} →
                clA ≅ᶜᵗʸ clA' → clB ≅ᶜᵗʸ clB' → prod-closed clA clB ≅ᶜᵗʸ prod-closed clA' clB'
closed-ty-eq (⊠-closed-cong eA eB) = ⊠-cong (closed-ty-eq eA) (closed-ty-eq eB)
closed-ty-eq-natural (⊠-closed-cong eA eB) σ =
  transᵉ (symᵉ transᵗʸ-assoc) (
  transᵉ (transᵗʸ-congˡ ⊠-natural-cong) (
  transᵉ transᵗʸ-assoc (
  transᵉ (transᵗʸ-congʳ (transᵉ (symᵉ ⊠-cong-trans) (
                         transᵉ (⊠-cong-cong (closed-ty-eq-natural eA _) (closed-ty-eq-natural eB _))
                         ⊠-cong-trans))) (
  symᵉ transᵗʸ-assoc))))
