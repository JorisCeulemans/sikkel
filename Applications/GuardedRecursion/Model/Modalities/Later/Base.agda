--------------------------------------------------
-- The earlier-later dependent adjunction
--------------------------------------------------

module Applications.GuardedRecursion.Model.Modalities.Later.Base where

open import Data.Nat hiding (_⊔_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.DRA.Basics

private
  variable
    m n : ℕ
    Γ Δ Θ : Ctx ω


--------------------------------------------------
-- The "earlier" context functor

◄ : Ctx ω → Ctx ω
◄ Γ ⟨ n ⟩ = Γ ⟨ suc n ⟩
◄ Γ ⟪ m≤n ⟫ γ = Γ ⟪ s≤s m≤n ⟫ γ
ctx-id (◄ Γ) = ctx-id Γ
ctx-comp (◄ Γ) = ctx-comp Γ

◄-subst : (σ : Δ ⇒ Γ) → ◄ Δ ⇒ ◄ Γ
func (◄-subst σ) {n} = func σ {suc n}
naturality (◄-subst σ) {f = m≤n} = naturality σ {f = s≤s m≤n}

◄-subst-cong : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → ◄-subst σ ≅ˢ ◄-subst τ
eq (◄-subst-cong σ=τ) δ = eq σ=τ δ

◄-subst-id : ◄-subst (id-subst Γ) ≅ˢ id-subst (◄ Γ)
eq ◄-subst-id _ = refl

◄-subst-⊚ : (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → ◄-subst (τ ⊚ σ) ≅ˢ ◄-subst τ ⊚ ◄-subst σ
eq (◄-subst-⊚ τ σ) _ = refl


--------------------------------------------------
-- The later type constructor and corresponding term formers

▻ : Ty (◄ Γ) → Ty Γ
▻ T ⟨ zero  , _ ⟩ = ⊤
▻ T ⟨ suc n , γ ⟩ = T ⟨ n , γ ⟩
▻ T ⟪ z≤n , _ ⟫ _ = tt
▻ T ⟪ s≤s m≤n , eγ ⟫ t = T ⟪ m≤n , eγ ⟫ t
ty-cong (▻ T) {f = z≤n} {f' = z≤n} e = refl
ty-cong (▻ T) {f = s≤s m≤n} {f' = s≤s .m≤n} refl = ty-cong T refl
ty-id (▻ T) {zero} = refl
ty-id (▻ T) {suc n} = ty-id T
ty-comp (▻ T) {f = z≤n} {g = m≤n} = refl
ty-comp (▻ T) {f = s≤s k≤m} {g = s≤s m≤n} = ty-comp T

module _ {T : Ty (◄ Γ)} where
  next : Tm (◄ Γ) T → Tm Γ (▻ T)
  next t ⟨ zero ,  _ ⟩' = tt
  next t ⟨ suc n , γ ⟩' = t ⟨ n , γ ⟩'
  naturality (next t) z≤n _ = refl
  naturality (next t) (s≤s m≤n) _ = naturality t m≤n _

  prev : Tm Γ (▻ T) → Tm (◄ Γ) T
  prev t ⟨ n , γ ⟩' = t ⟨ suc n , γ ⟩'
  naturality (prev t) m≤n eγ = naturality t (s≤s m≤n) eγ

  prev-next : (t : Tm (◄ Γ) T) → prev (next t) ≅ᵗᵐ t
  eq (prev-next t) _ = refl

  next-prev : (t : Tm Γ (▻ T)) → next (prev t) ≅ᵗᵐ t
  eq (next-prev t) {zero} γ = refl
  eq (next-prev t) {suc n} γ = refl


--------------------------------------------------
-- Functoriality for the later type constructor and associated term formers

▻-map : {T : Ty (◄ Γ)} {T' : Ty (◄ Γ)} → (T ↣ T') → (▻ T ↣ ▻ T')
func (▻-map η) {zero} _ = tt
func (▻-map η) {suc n} t = func η t
naturality (▻-map η) {f = z≤n} = refl
naturality (▻-map η) {f = s≤s m≤n} = naturality η

▻-map-cong : {T : Ty (◄ Γ)} {T' : Ty (◄ Γ)} {η φ : T ↣ T'} →
              η ≅ⁿ φ → ▻-map η ≅ⁿ ▻-map φ
eq (▻-map-cong 𝔢) {x = zero} _ = refl
eq (▻-map-cong 𝔢) {x = suc _} = eq 𝔢

▻-map-id : {T : Ty (◄ Γ)} → ▻-map (id-trans T) ≅ⁿ id-trans (▻ T)
eq ▻-map-id {x = zero} _ = refl
eq ▻-map-id {x = suc _} _ = refl

▻-map-⊙ : {R : Ty (◄ Γ)} {S : Ty (◄ Γ)} {T : Ty (◄ Γ)}
          {η : S ↣ T} {φ : R ↣ S} →
          ▻-map (η ⊙ φ) ≅ⁿ ▻-map η ⊙ ▻-map φ
eq ▻-map-⊙ {x = zero} _ = refl
eq ▻-map-⊙ {x = suc _} _ = refl


next-cong : {T : Ty (◄ Γ)} {t t' : Tm (◄ Γ) T} → t ≅ᵗᵐ t' → next t ≅ᵗᵐ next t'
eq (next-cong t=t') {zero} _ = refl
eq (next-cong t=t') {suc n} = eq t=t'

prev-cong : {T : Ty (◄ Γ)} {t t' : Tm Γ (▻ T)} → t ≅ᵗᵐ t' → prev t ≅ᵗᵐ prev t'
eq (prev-cong t=t') = eq t=t'

next-convert : {Γ : Ctx ω} {T T' : Ty (◄ Γ)} {η : T ↣ T'} (t : Tm (◄ Γ) T) →
               convert-tm (▻-map η) (next t) ≅ᵗᵐ next (convert-tm η t)
eq (next-convert t) {zero}  _ = refl
eq (next-convert t) {suc n} _ = refl


--------------------------------------------------
-- Naturality of the later type constructor and associated term formers

module _ {Δ : Ctx ω} {Γ : Ctx ω} (σ : Δ ⇒ Γ) {T : Ty (◄ Γ)} where
  ▻-natural-from : (▻ T) [ σ ] ↣ ▻ (T [ ◄-subst σ ])
  func ▻-natural-from {zero} t = t
  func ▻-natural-from {suc n} t = t
  naturality ▻-natural-from {f = z≤n} = refl
  naturality ▻-natural-from {f = s≤s m≤n} = refl

  ▻-natural-to : ▻ (T [ ◄-subst σ ]) ↣ (▻ T) [ σ ]
  func ▻-natural-to {zero} t = t
  func ▻-natural-to {suc n} t = t
  naturality ▻-natural-to {f = z≤n} = refl
  naturality ▻-natural-to {f = s≤s m≤n} = refl

  ▻-natural : (▻ T) [ σ ] ≅ᵗʸ ▻ (T [ ◄-subst σ ])
  from ▻-natural = ▻-natural-from
  to ▻-natural = ▻-natural-to
  eq (isoˡ ▻-natural) {zero}  _ = refl
  eq (isoˡ ▻-natural) {suc n} _ = refl
  eq (isoʳ ▻-natural) {zero}  _ = refl
  eq (isoʳ ▻-natural) {suc n} _ = refl

  next-natural : (t : Tm (◄ Γ) T) → (next t) [ σ ]' ≅ᵗᵐ ι[ ▻-natural ] (next (t [ ◄-subst σ ]'))
  eq (next-natural t) {zero} _ = refl
  eq (next-natural t) {suc n} _ = refl

  prev-natural : (t : Tm Γ (▻ T)) → (prev t) [ ◄-subst σ ]' ≅ᵗᵐ prev (ι⁻¹[ ▻-natural ] (t [ σ ]'))
  eq (prev-natural t) _ = refl

later-natural-map : (σ : Γ ⇒ Δ) {T S : Ty (◄ Δ)} (η : T ↣ S) →
                    ▻-map (ty-subst-map (◄-subst σ) η) ⊙ ▻-natural-from σ
                      ≅ⁿ
                    ▻-natural-from σ ⊙ ty-subst-map σ (▻-map η)
eq (later-natural-map σ e) {zero}  _ = refl
eq (later-natural-map σ e) {suc n} _ = refl

later-natural-id-map : {T : Ty (◄ Γ)} →
                       ▻-map (ty-subst-id-from T ⊙ ty-subst-eq-subst-morph ◄-subst-id T) ⊙ ▻-natural-from (id-subst Γ)
                         ≅ⁿ
                       ty-subst-id-from (▻ T)
eq later-natural-id-map           {zero}  _ = refl
eq (later-natural-id-map {T = T}) {suc n} _ = strong-ty-id T

later-natural-⊚-map : (τ : Δ ⇒ Θ) (σ : Γ ⇒ Δ) {T : Ty (◄ Θ)} →
                      ▻-map (ty-subst-comp-from T (◄-subst τ) (◄-subst σ))
                      ⊙ ▻-natural-from σ
                      ⊙ ty-subst-map σ (▻-natural-from τ)
                        ≅ⁿ
                      ▻-map (ty-subst-eq-subst-morph (◄-subst-⊚ τ σ) T)
                      ⊙ ▻-natural-from (τ ⊚ σ)
                      ⊙ ty-subst-comp-from (▻ T) τ σ
eq (later-natural-⊚-map τ σ)     {zero}  _ = refl
eq (later-natural-⊚-map τ σ {T}) {suc n} _ = sym (strong-ty-id T)

later-natural-subst-eq-map : {σ τ : Γ ⇒ Δ} {T : Ty (◄ Δ)} (ε : σ ≅ˢ τ) →
                             ▻-natural-from τ ⊙ ty-subst-eq-subst-morph ε (▻ T)
                               ≅ⁿ
                             ▻-map (ty-subst-eq-subst-morph (◄-subst-cong ε) T) ⊙ ▻-natural-from σ
eq (later-natural-subst-eq-map _) {zero}  _ = refl
eq (later-natural-subst-eq-map _) {suc n} _ = refl


--------------------------------------------------
-- Later as a DRA

instance
  ◄-is-functor : IsCtxFunctor ◄
  ctx-map {{◄-is-functor}} = ◄-subst
  ctx-map-cong {{◄-is-functor}} = ◄-subst-cong
  ctx-map-id {{◄-is-functor}} = ◄-subst-id
  ctx-map-⊚ {{◄-is-functor}} = ◄-subst-⊚

earlier-functor : CtxFunctor ω ω
ctx-op earlier-functor = ◄
is-functor earlier-functor = ◄-is-functor

later : DRA ω ω
ctx-functor later = earlier-functor
⟨_∣_⟩ later = ▻
dra-map later = ▻-map
dra-map-cong later = ▻-map-cong
dra-map-id later = ▻-map-id
dra-map-⊙ later = ▻-map-⊙
dra-natural later = ▻-natural
dra-natural-map later = later-natural-map
dra-natural-id-map later = later-natural-id-map
dra-natural-⊚-map later = later-natural-⊚-map
dra-natural-subst-eq-map later = later-natural-subst-eq-map
dra-intro later = next
dra-intro-cong later = next-cong
dra-intro-natural later = next-natural
dra-intro-convert later = next-convert
dra-elim later = prev
dra-elim-cong later = prev-cong
dra-β later = prev-next
dra-η later = next-prev


▻-cong : {T T' : Ty (◄ Γ)} → T ≅ᵗʸ T' → ▻ T ≅ᵗʸ ▻ T'
▻-cong e = dra-cong later e

module _ {Γ : Ctx ω} {T T' : Ty (◄ Γ)} {T=T' : T ≅ᵗʸ T'} where
  next-ι : (t : Tm (◄ Γ) T') → ι[ ▻-cong T=T' ] next t ≅ᵗᵐ next (ι[ T=T' ] t)
  next-ι t = dra-intro-ι later t

  next-ι⁻¹ : {T T' : Ty (◄ Γ)} {T=T' : T ≅ᵗʸ T'} (t : Tm (◄ Γ) T) →
             ι⁻¹[ ▻-cong T=T' ] next t ≅ᵗᵐ next (ι⁻¹[ T=T' ] t)
  next-ι⁻¹ t = dra-intro-ι⁻¹ later t

  prev-ι : (t : Tm Γ (▻ T')) → ι[ T=T' ] (prev t) ≅ᵗᵐ prev (ι[ ▻-cong T=T' ] t)
  prev-ι t = dra-elim-ι later t

  prev-ι⁻¹ : (t : Tm Γ (▻ T)) → ι⁻¹[ T=T' ] (prev t) ≅ᵗᵐ prev (ι⁻¹[ ▻-cong T=T' ] t)
  prev-ι⁻¹ t = dra-elim-ι⁻¹ later t
