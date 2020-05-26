--------------------------------------------------
-- Later and earlier modalities for types
--------------------------------------------------

module GuardedRecursion.Later where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Unit using (⊤; tt)
open import Function using (id; _∘_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Categories
open import Helpers
open import CwF-Structure
open import Types.Functions

private
  variable
    m n : ℕ


--------------------------------------------------
-- The "earlier" CwF-endomorphism

ctx-m≤1+n : (Γ : Ctx ω ℓ) (m≤n : m ≤ n) (γ : Γ ⟨ suc n ⟩) →
            Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n n ⟫ γ) ≡ Γ ⟪ n≤1+n m ⟫ (Γ ⟪ s≤s m≤n ⟫ γ)
ctx-m≤1+n Γ m≤n γ = trans (sym (rel-comp Γ m≤n (n≤1+n _) γ))
                          (trans (cong (Γ ⟪_⟫ γ) (≤-irrelevant _ _))
                                 (rel-comp Γ (n≤1+n _) (s≤s m≤n) γ))

◄ : Ctx ω ℓ → Ctx ω ℓ
set (◄ Γ) n = Γ ⟨ suc n ⟩
rel (◄ Γ) m≤n = Γ ⟪ s≤s m≤n ⟫
rel-id (◄ Γ) = rel-id Γ
rel-comp (◄ Γ) k≤m m≤n = rel-comp Γ (s≤s k≤m) (s≤s m≤n)

◄-subst : {Δ Γ : Ctx ω ℓ} (σ : Δ ⇒ Γ) → ◄ Δ ⇒ ◄ Γ
func (◄-subst σ) {n} = func σ {suc n}
naturality (◄-subst σ) {f = m≤n} = naturality σ {f = s≤s m≤n}

◅-ty : {Γ : Ctx ω ℓ} → Ty Γ → Ty (◄ Γ)
type (◅-ty T) n γ = T ⟨ suc n , γ ⟩
morph (◅-ty T) m≤n eγ = T ⟪ s≤s m≤n , eγ ⟫
morph-id (◅-ty T) t = morph-id T t
morph-comp (◅-ty T) k≤m m≤n = morph-comp T (s≤s k≤m) (s≤s m≤n)

◅-tm : {Γ : Ctx ω ℓ} {T : Ty Γ} → Tm Γ T → Tm (◄ Γ) (◅-ty T)
term (◅-tm t) n γ = t ⟨ suc n , γ ⟩'
naturality (◅-tm t) m≤n eγ = naturality t (s≤s m≤n) eγ

from-earlier : (Γ : Ctx ω ℓ) → ◄ Γ ⇒ Γ
func (from-earlier Γ) = Γ ⟪ n≤1+n _ ⟫
naturality (from-earlier Γ) γ = ctx-m≤1+n Γ _ γ


--------------------------------------------------
-- Congruence and naturality for earlier

◄-subst-cong : {Δ Γ : Ctx ω ℓ} {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → ◄-subst σ ≅ˢ ◄-subst τ
eq (◄-subst-cong σ=τ) δ = eq σ=τ δ

◅-ty-cong : {Γ : Ctx ω ℓ} {T T' : Ty Γ} → T ≅ᵗʸ T' → ◅-ty T ≅ᵗʸ ◅-ty T'
from (◅-ty-cong T=T') = record { func = func (from T=T') ; naturality = naturality (from T=T') }
to (◅-ty-cong T=T') = record { func = func (to T=T') ; naturality = naturality (to T=T') }
eq (isoˡ (◅-ty-cong T=T')) t = eq (isoˡ T=T') t
eq (isoʳ (◅-ty-cong T=T')) t = eq (isoʳ T=T') t

◅-tm-cong : {Γ : Ctx ω ℓ} {T : Ty Γ} {t t' : Tm Γ T} → t ≅ᵗᵐ t' → ◅-tm t ≅ᵗᵐ ◅-tm t'
eq (◅-tm-cong t=t') γ = eq t=t' γ

◅-tm-ι : {Γ : Ctx ω ℓ} {T T' : Ty Γ} (T=T' : T ≅ᵗʸ T') (t : Tm Γ T') →
          ◅-tm (ι[ T=T' ] t) ≅ᵗᵐ ι[ ◅-ty-cong T=T' ] (◅-tm t)
eq (◅-tm-ι T=T' t) γ = refl

module _ {Δ Γ : Ctx ω ℓ} (σ : Δ ⇒ Γ) {T : Ty Γ} where
  ◅-ty-natural : (◅-ty T) [ ◄-subst σ ] ≅ᵗʸ ◅-ty (T [ σ ])
  from ◅-ty-natural = record { func = id ; naturality = λ _ → refl }
  to ◅-ty-natural = record { func = id ; naturality = λ _ → refl }
  eq (isoˡ ◅-ty-natural) _ = refl
  eq (isoʳ ◅-ty-natural) _ = refl

  ◅-tm-natural : (t : Tm Γ T) → (◅-tm t) [ ◄-subst σ ]' ≅ᵗᵐ ι[ ◅-ty-natural ] (◅-tm (t [ σ ]'))
  eq (◅-tm-natural t) _ = refl

from-earlier-natural : {Δ Γ : Ctx ω ℓ} (σ : Δ ⇒ Γ) → from-earlier Γ ⊚ ◄-subst σ ≅ˢ σ ⊚ from-earlier Δ
eq (from-earlier-natural σ) δ = naturality σ δ


--------------------------------------------------
-- The later modality and corresponding term formers

▻ : {Γ : Ctx ω ℓ} → Ty (◄ Γ) → Ty Γ
type (▻ {Γ = Γ} T) zero _ = Lift _ ⊤
type (▻ {Γ = Γ} T) (suc n) γ = T ⟨ n , γ ⟩
morph (▻ {Γ = Γ} T) z≤n _ _ = lift tt
morph (▻ {Γ = Γ} T) (s≤s m≤n) eγ = T ⟪ m≤n , eγ ⟫
morph-id (▻ {Γ = Γ} T) {zero} _ = refl
morph-id (▻ {Γ = Γ} T) {suc n} = morph-id T
morph-comp (▻ {Γ = Γ} T) z≤n m≤n _ _ _ = refl
morph-comp (▻ {Γ = Γ} T) (s≤s k≤m) (s≤s m≤n) = morph-comp T k≤m m≤n

▻' : {Γ : Ctx ω ℓ} → Ty Γ → Ty Γ
▻' {Γ = Γ} T = ▻ (T [ from-earlier Γ ])

next : {Γ : Ctx ω ℓ} {T : Ty (◄ Γ)} → Tm (◄ Γ) T → Tm Γ (▻ T)
term (next t) zero _ = lift tt
term (next t) (suc n) γ = t ⟨ n , γ ⟩'
naturality (next t) z≤n γ = refl
naturality (next t) (s≤s m≤n) eγ = naturality t m≤n eγ

next' : {Γ : Ctx ω ℓ} {T : Ty Γ} → Tm Γ T → Tm Γ (▻' T)
next' t = next (t [ from-earlier _ ]')

prev : {Γ : Ctx ω ℓ} {T : Ty (◄ Γ)} → Tm Γ (▻ T) → Tm (◄ Γ) T
term (prev t) n γ = t ⟨ suc n , γ ⟩'
naturality (prev t) m≤n eγ = naturality t (s≤s m≤n) eγ

prev-next : {Γ : Ctx ω ℓ} {T : Ty (◄ Γ)} (t : Tm (◄ Γ) T) → prev {Γ = Γ} (next t) ≅ᵗᵐ t
eq (prev-next t) _ = refl

next-prev : {Γ : Ctx ω ℓ} {T : Ty (◄ Γ)} (t : Tm Γ (▻ T)) → next (prev t) ≅ᵗᵐ t
eq (next-prev t) {zero} γ = refl
eq (next-prev t) {suc n} γ = refl

-- We could make the argument T implicit, but giving it explicitly
-- drastically improves performance.
löb : {Γ : Ctx ω ℓ} (T : Ty Γ) → Tm Γ (▻' T ⇛ T) → Tm Γ T
term (löb T f) zero γ = f €⟨ zero , γ ⟩ lift tt
term (löb {Γ = Γ} T f) (suc n) γ = f €⟨ suc n , γ ⟩ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩')
naturality (löb T f) {y = zero} z≤n eγ = €-natural f z≤n eγ (lift tt)
naturality (löb {Γ = Γ} T f) {y = suc n} z≤n {γ} eγ = €-natural f z≤n eγ ((löb T f) ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩')
naturality (löb {Γ = Γ} T f) {x = suc m} {y = suc n} (s≤s m≤n) {γ} {γ'} eγ =
  T ⟪ s≤s m≤n , eγ ⟫ f €⟨ suc n , γ ⟩ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩')
    ≡⟨ €-natural f (s≤s m≤n) eγ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩') ⟩
  f €⟨ suc m , γ' ⟩ (T ⟪ m≤n , _ ⟫ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩'))
    ≡⟨ cong (f €⟨ _ , _ ⟩_) (naturality (löb T f) m≤n _) ⟩
  f €⟨ suc m , γ' ⟩ (löb T f ⟨ m , Γ ⟪ n≤1+n m ⟫ γ' ⟩') ∎
  where open ≡-Reasoning

löb-is-fixpoint : {Γ : Ctx ω ℓ} {T : Ty Γ} (f : Tm Γ (▻' T ⇛ T)) →
                  löb T f ≅ᵗᵐ app f (next' (löb T f))
eq (löb-is-fixpoint f) {zero} γ = refl
eq (löb-is-fixpoint f) {suc n} γ = refl

-- ▻ is an applicative functor
_⊛_ : {Γ : Ctx ω ℓ} {T S : Ty (◄ Γ)} → Tm Γ (▻ (T ⇛ S)) → Tm Γ (▻ T) → Tm Γ (▻ S)
f ⊛ t = next (app (prev f) (prev t))


--------------------------------------------------
-- Congruence and naturality for the later modality

▻-map : {Γ : Ctx ω ℓ} {T T' : Ty (◄ Γ)} → (T ↣ T') → (▻ {Γ = Γ} T ↣ ▻ T')
func (▻-map η) {zero} _ = lift tt
func (▻-map η) {suc n} t = func η t
naturality (▻-map η) {f = z≤n} _ = refl
naturality (▻-map η) {f = s≤s m≤n} t = naturality η t

▻-cong : {Γ : Ctx ω ℓ} {T T' : Ty (◄ Γ)} → T ≅ᵗʸ T' → ▻ {Γ = Γ} T ≅ᵗʸ ▻ T'
from (▻-cong T=T') = ▻-map (from T=T')
to (▻-cong T=T') = ▻-map (to T=T')
eq (isoˡ (▻-cong T=T')) {zero} _ = refl
eq (isoˡ (▻-cong T=T')) {suc n} t = eq (isoˡ T=T') t
eq (isoʳ (▻-cong T=T')) {zero} _ = refl
eq (isoʳ (▻-cong T=T')) {suc n} t = eq (isoʳ T=T') t

▻'-cong : {Γ : Ctx ω ℓ} {T T' : Ty Γ} → T ≅ᵗʸ T' → ▻' T ≅ᵗʸ ▻' T'
▻'-cong {Γ = Γ} T=T' = ▻-cong (ty-subst-cong-ty (from-earlier Γ) T=T')

next-cong : {Γ : Ctx ω ℓ} {T : Ty (◄ Γ)} {t t' : Tm (◄ Γ) T} → t ≅ᵗᵐ t' → next {Γ = Γ} t ≅ᵗᵐ next t'
eq (next-cong t=t') {zero} _ = refl
eq (next-cong t=t') {suc n} γ = eq t=t' γ

prev-cong : {Γ : Ctx ω ℓ} {T : Ty (◄ Γ)} {t t' : Tm Γ (▻ T)} → t ≅ᵗᵐ t' → prev t ≅ᵗᵐ prev t'
eq (prev-cong t=t') γ = eq t=t' γ

löb-cong : {Γ : Ctx ω ℓ} (T : Ty Γ) {f f' : Tm Γ (▻' T ⇛ T)} → f ≅ᵗᵐ f' → löb T f ≅ᵗᵐ löb T f'
eq (löb-cong T f=f') {zero} γ = cong (_$⟨ z≤n , _ ⟩ lift tt) (eq f=f' γ)
eq (löb-cong T f=f') {suc n} γ = €-cong f=f' (eq (löb-cong T f=f') {n} _)

module _ {Γ : Ctx ω ℓ} {T T' : Ty (◄ Γ)} (T=T' : T ≅ᵗʸ T') where
  next-ι : (t : Tm (◄ Γ) T') → ι[ ▻-cong T=T' ] next {Γ = Γ} t ≅ᵗᵐ next (ι[ T=T' ] t)
  eq (next-ι t) {zero} _ = refl
  eq (next-ι t) {suc n} _ = refl

  prev-ι : (t : Tm Γ (▻ T')) → ι[ T=T' ] (prev t) ≅ᵗᵐ prev (ι[ ▻-cong T=T' ] t)
  eq (prev-ι t) _ = refl

löb-ι : {Γ : Ctx ω ℓ} {T T' : Ty Γ} (T=T' : T ≅ᵗʸ T') (f : Tm Γ (▻' T' ⇛ T')) →
        ι[ T=T' ] (löb T' f) ≅ᵗᵐ löb T (ι[ ⇛-cong (▻'-cong T=T') T=T' ] f)
eq (löb-ι T=T' f) {zero} γ = refl
eq (löb-ι {Γ = Γ}{T}{T'} T=T' f) {suc n} γ = cong (func (to T=T')) (€-cong (≅ᵗᵐ-refl {t = f})
  (begin
    löb T' f ⟨ n , _ ⟩'
  ≡˘⟨ eq (isoʳ T=T') _ ⟩
    func (from T=T') (func (to T=T') (löb T' f ⟨ n , _ ⟩'))
  ≡⟨ cong (func (from T=T')) (eq (löb-ι T=T' f) {n} _) ⟩
    func (from T=T') (löb T g ⟨ n , _ ⟩') ∎))
  where
    open ≡-Reasoning
    g : Tm Γ (▻' T ⇛ T)
    g = ι[ ⇛-cong (▻'-cong T=T') T=T' ] f

module _ {Δ Γ : Ctx ω ℓ} (σ : Δ ⇒ Γ) {T : Ty (◄ Γ)} where
  ▻-natural-from : (▻ T) [ σ ] ↣ ▻ (T [ ◄-subst σ ])
  func ▻-natural-from {zero} t = t
  func ▻-natural-from {suc n} t = t
  naturality ▻-natural-from {f = z≤n} _ = refl
  naturality ▻-natural-from {f = s≤s m≤n} _ = refl

  ▻-natural-to : ▻ (T [ ◄-subst σ ]) ↣ (▻ T) [ σ ]
  func ▻-natural-to {zero} t = t
  func ▻-natural-to {suc n} t = t
  naturality ▻-natural-to {f = z≤n} _ = refl
  naturality ▻-natural-to {f = s≤s m≤n} _ = refl

  ▻-natural : (▻ T) [ σ ] ≅ᵗʸ ▻ (T [ ◄-subst σ ])
  from ▻-natural = ▻-natural-from
  to ▻-natural = ▻-natural-to
  eq (isoˡ ▻-natural) {zero} _ = refl
  eq (isoˡ ▻-natural) {suc n} _ = refl
  eq (isoʳ ▻-natural) {zero} _ = refl
  eq (isoʳ ▻-natural) {suc n} _ = refl

  next-natural : (t : Tm (◄ Γ) T) → (next t) [ σ ]' ≅ᵗᵐ ι[ ▻-natural ] (next (t [ ◄-subst σ ]'))
  eq (next-natural t) {zero} _ = refl
  eq (next-natural t) {suc n} _ = refl

  prev-natural : (t : Tm Γ (▻ T)) → (prev t) [ ◄-subst σ ]' ≅ᵗᵐ prev (ι⁻¹[ ▻-natural ] (t [ σ ]'))
  eq (prev-natural t) _ = refl

module _ {Δ Γ : Ctx ω ℓ} (σ : Δ ⇒ Γ) (T : Ty Γ) where
  ▻'-natural : (▻' T) [ σ ] ≅ᵗʸ ▻' (T [ σ ])
  ▻'-natural =
    begin
      ▻ (T [ from-earlier Γ ]) [ σ ]
    ≅⟨ ▻-natural σ ⟩
      ▻ (T [ from-earlier Γ ] [ ◄-subst σ ])
    ≅⟨ ▻-cong (ty-subst-seq-cong (from-earlier Γ ∷ ◄-subst σ ◼) (σ ∷ (from-earlier Δ ◼)) T (from-earlier-natural σ)) ⟩
      ▻ (T [ σ ] [ from-earlier Δ ]) ∎
    where open ≅ᵗʸ-Reasoning

  löb-natural : (f : Tm Γ (▻' T ⇛ T)) →
                (löb T f) [ σ ]' ≅ᵗᵐ löb (T [ σ ]) (ι⁻¹[ ⇛-cong ▻'-natural ≅ᵗʸ-refl ] (ι⁻¹[ ⇛-natural {T = ▻' T} {T} σ ] (f [ σ ]')))
  eq (löb-natural f) {zero} δ = $-cong (f ⟨ 0 , func σ δ ⟩') refl _ _
  eq (löb-natural f) {suc n} δ =
    begin
      f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , rel-id Γ (func σ δ) ⟩ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ (func σ δ) ⟩')
    ≡⟨ $-cong (f ⟨ suc n , func σ δ ⟩') refl _ α ⟩
      f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ (func σ δ) ⟩')
    ≡˘⟨ cong (f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩_) (naturality (löb T f) ≤-refl β) ⟩
      f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩ (T ⟪ ≤-refl , β ⟫ ((löb T f) [ σ ]' ⟨ n , Δ ⟪ n≤1+n n ⟫ δ ⟩'))
    ≡⟨ cong (f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩_ ∘ T ⟪ ≤-refl , β ⟫) (eq (löb-natural f) {n} (Δ ⟪ n≤1+n n ⟫ δ)) ⟩
      f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩ (T ⟪ ≤-refl , β ⟫ (löb (T [ σ ]) g ⟨ n , Δ ⟪ n≤1+n n ⟫ δ ⟩')) ∎
    where
      open ≡-Reasoning
      α = _
      β = _
      g : Tm Δ (▻' (T [ σ ]) ⇛ (T [ σ ]))
      g = ι⁻¹[ ⇛-cong ▻'-natural ≅ᵗʸ-refl ] (ι⁻¹[ ⇛-natural {T = ▻' T} {T} σ ] (f [ σ ]'))
