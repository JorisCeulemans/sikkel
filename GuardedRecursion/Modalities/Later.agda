--------------------------------------------------
-- The earlier-later dependent adjunction
--------------------------------------------------

module GuardedRecursion.Modalities.Later where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.String
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (id; _∘_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Categories
open import Helpers
open import CwF-Structure
open import Types.Functions
open import Reflection.SubstitutionSequence

private
  variable
    ℓ'' ℓt ℓt' : Level
    m n : ℕ
    Γ Δ Θ : Ctx ω ℓ

infixl 12 _⟨$⟩_
infixl 12 _⊛_
infixr 4 nlöb'[_∈_]_


--------------------------------------------------
-- The "earlier" Context operation

ctx-m≤1+n : (Γ : Ctx ω ℓ) (m≤n : m ≤ n) (γ : Γ ⟨ suc n ⟩) →
            Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n n ⟫ γ) ≡ Γ ⟪ n≤1+n m ⟫ (Γ ⟪ s≤s m≤n ⟫ γ)
ctx-m≤1+n {m = m}{n = n} Γ m≤n γ =
  begin
    Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n n ⟫ γ)
  ≡˘⟨ rel-comp Γ m≤n (n≤1+n n) γ ⟩
    Γ ⟪ ≤-trans m≤n (n≤1+n n) ⟫ γ
  ≡⟨ cong (Γ ⟪_⟫ γ) (≤-irrelevant _ _) ⟩
    Γ ⟪ ≤-trans (n≤1+n m)(s≤s m≤n) ⟫ γ
  ≡⟨ rel-comp Γ (n≤1+n m) (s≤s m≤n) γ ⟩
    Γ ⟪ n≤1+n m ⟫ (Γ ⟪ s≤s m≤n ⟫ γ) ∎
  where open ≡-Reasoning

◄ : Ctx ω ℓ → Ctx ω ℓ
set (◄ Γ) n = Γ ⟨ suc n ⟩
rel (◄ Γ) m≤n = Γ ⟪ s≤s m≤n ⟫
rel-id (◄ Γ) = rel-id Γ
rel-comp (◄ Γ) k≤m m≤n = rel-comp Γ (s≤s k≤m) (s≤s m≤n)

◄-subst : (σ : Δ ⇒ Γ) → ◄ Δ ⇒ ◄ Γ
func (◄-subst σ) {n} = func σ {suc n}
naturality (◄-subst σ) {f = m≤n} = naturality σ {f = s≤s m≤n}

{-
-- The operations on types and terms are not used anywhere
◅-ty : Ty Γ ℓ → Ty (◄ Γ) ℓ
type (◅-ty T) n γ = T ⟨ suc n , γ ⟩
morph (◅-ty T) m≤n eγ = T ⟪ s≤s m≤n , eγ ⟫
morph-cong (◅-ty T) e = morph-cong T (cong s≤s e)
morph-id (◅-ty T) t = morph-id T t
morph-comp (◅-ty T) k≤m m≤n = morph-comp T (s≤s k≤m) (s≤s m≤n)

◅-tm : {T : Ty Γ ℓ} → Tm Γ T → Tm (◄ Γ) (◅-ty T)
term (◅-tm t) n γ = t ⟨ suc n , γ ⟩'
naturality (◅-tm t) m≤n eγ = naturality t (s≤s m≤n) eγ
-}

from-earlier : (Γ : Ctx ω ℓ) → ◄ Γ ⇒ Γ
func (from-earlier Γ) = Γ ⟪ n≤1+n _ ⟫
naturality (from-earlier Γ) γ = ctx-m≤1+n Γ _ γ


--------------------------------------------------
-- Congruence, naturality and functoriality for earlier

◄-subst-cong : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → ◄-subst σ ≅ˢ ◄-subst τ
eq (◄-subst-cong σ=τ) δ = eq σ=τ δ

{-
-- The operations on types and terms are not used anywhere
◅-ty-cong : {T : Ty Γ ℓ} {T' : Ty Γ ℓ'} → T ≅ᵗʸ T' → ◅-ty T ≅ᵗʸ ◅-ty T'
func (from (◅-ty-cong T=T')) = func (from T=T')
naturality (from (◅-ty-cong T=T')) = naturality (from T=T')
func (to (◅-ty-cong T=T')) = func (to T=T')
naturality (to (◅-ty-cong T=T')) = naturality (to T=T')
eq (isoˡ (◅-ty-cong T=T')) t = eq (isoˡ T=T') t
eq (isoʳ (◅-ty-cong T=T')) t = eq (isoʳ T=T') t

◅-tm-cong : {T : Ty Γ ℓ} {t t' : Tm Γ T} → t ≅ᵗᵐ t' → ◅-tm t ≅ᵗᵐ ◅-tm t'
eq (◅-tm-cong t=t') γ = eq t=t' γ

◅-tm-ι : {T : Ty Γ ℓ} {T' : Ty Γ ℓ'} (T=T' : T ≅ᵗʸ T') (t : Tm Γ T') →
          ◅-tm (ι[ T=T' ] t) ≅ᵗᵐ ι[ ◅-ty-cong T=T' ] (◅-tm t)
eq (◅-tm-ι T=T' t) γ = refl

module _ {Δ : Ctx ω ℓ} {Γ : Ctx ω ℓ'} (σ : Δ ⇒ Γ) {T : Ty Γ ℓt} where
  ◅-ty-natural : (◅-ty T) [ ◄-subst σ ] ≅ᵗʸ ◅-ty (T [ σ ])
  func (from ◅-ty-natural) = id
  naturality (from ◅-ty-natural) _ = refl
  func (to ◅-ty-natural) = id
  naturality (to ◅-ty-natural) _ = refl
  eq (isoˡ ◅-ty-natural) _ = refl
  eq (isoʳ ◅-ty-natural) _ = refl

  ◅-tm-natural : (t : Tm Γ T) → (◅-tm t) [ ◄-subst σ ]' ≅ᵗᵐ ι[ ◅-ty-natural ] (◅-tm (t [ σ ]'))
  eq (◅-tm-natural t) _ = refl
-}

from-earlier-natural : (σ : Δ ⇒ Γ) → from-earlier Γ ⊚ ◄-subst σ ≅ˢ σ ⊚ from-earlier Δ
eq (from-earlier-natural σ) δ = naturality σ δ

◄-subst-id : ◄-subst (id-subst Γ) ≅ˢ id-subst (◄ Γ)
eq ◄-subst-id _ = refl

◄-subst-⊚ : (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → ◄-subst (τ ⊚ σ) ≅ˢ ◄-subst τ ⊚ ◄-subst σ
eq (◄-subst-⊚ τ σ) _ = refl


--------------------------------------------------
-- The later modality and corresponding term formers

▻ : Ty (◄ Γ) ℓ → Ty Γ ℓ
type (▻ T) zero _ = ⊤
type (▻ T) (suc n) γ = T ⟨ n , γ ⟩
morph (▻ T) z≤n _ _ = tt
morph (▻ T) (s≤s m≤n) eγ = T ⟪ m≤n , eγ ⟫
morph-cong (▻ T) {f = z≤n} {f' = z≤n} e = refl
morph-cong (▻ T) {f = s≤s m≤n} {f' = s≤s .m≤n} refl = morph-cong T refl
morph-id (▻ T) {zero} _ = refl
morph-id (▻ T) {suc n} = morph-id T
morph-comp (▻ T) z≤n m≤n _ _ _ = refl
morph-comp (▻ T) (s≤s k≤m) (s≤s m≤n) = morph-comp T k≤m m≤n

▻' : Ty Γ ℓ → Ty Γ ℓ
▻' {Γ = Γ} T = ▻ (T [ from-earlier Γ ])

next : {T : Ty (◄ Γ) ℓ} → Tm (◄ Γ) T → Tm Γ (▻ T)
term (next t) zero _ = tt
term (next t) (suc n) γ = t ⟨ n , γ ⟩'
naturality (next t) z≤n γ = refl
naturality (next t) (s≤s m≤n) eγ = naturality t m≤n eγ

prev' : {T : Ty Γ ℓ} → Tm Γ T → Tm (◄ Γ) (T [ from-earlier Γ ])
prev' t = t [ from-earlier _ ]'

next' : {T : Ty Γ ℓ} → Tm Γ T → Tm Γ (▻' T)
next' t = next (prev' t)

prev : {T : Ty (◄ Γ) ℓ} → Tm Γ (▻ T) → Tm (◄ Γ) T
term (prev t) n γ = t ⟨ suc n , γ ⟩'
naturality (prev t) m≤n eγ = naturality t (s≤s m≤n) eγ

prev-next : {T : Ty (◄ Γ) ℓ} (t : Tm (◄ Γ) T) → prev (next t) ≅ᵗᵐ t
eq (prev-next t) _ = refl

next-prev : {T : Ty (◄ Γ) ℓ} (t : Tm Γ (▻ T)) → next (prev t) ≅ᵗᵐ t
eq (next-prev t) {zero} γ = refl
eq (next-prev t) {suc n} γ = refl

-- TODO: Update : See if T can be made implicit.
löb : (T : Ty Γ ℓ) → Tm Γ (▻' T ⇛ T) → Tm Γ T
term (löb T f) zero γ = f €⟨ zero , γ ⟩ tt
term (löb {Γ = Γ} T f) (suc n) γ = f €⟨ suc n , γ ⟩ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩')
naturality (löb T f) {y = zero} z≤n eγ = €-natural f z≤n eγ tt
naturality (löb {Γ = Γ} T f) {y = suc n} z≤n {γ} eγ = €-natural f z≤n eγ ((löb T f) ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩')
naturality (löb {Γ = Γ} T f) {x = suc m} {y = suc n} (s≤s m≤n) {γ} {γ'} eγ =
  begin
    T ⟪ s≤s m≤n , eγ ⟫ f €⟨ suc n , γ ⟩ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩')
  ≡⟨ €-natural f (s≤s m≤n) eγ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩') ⟩
    f €⟨ suc m , γ' ⟩ (T ⟪ m≤n , _ ⟫ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩'))
  ≡⟨ cong (f €⟨ _ , _ ⟩_) (naturality (löb T f) m≤n _) ⟩
    f €⟨ suc m , γ' ⟩ (löb T f ⟨ m , Γ ⟪ n≤1+n m ⟫ γ' ⟩') ∎
  where open ≡-Reasoning

löb' : (T : Ty Γ ℓ) → Tm (Γ ,, ▻' T) (T [ π ]) → Tm Γ T
löb' T f = löb T (lam (▻' T) f)

nlöb'[_∈_]_ : (v : String) (T : Ty Γ ℓ) → Tm (Γ ,, v ∈ ▻' T) (T [ π ]) → Tm Γ T
nlöb'[_∈_]_ v = löb'

löb-is-fixpoint : {T : Ty Γ ℓ} (f : Tm Γ (▻' T ⇛ T)) →
                  app f (next' (löb T f)) ≅ᵗᵐ löb T f
eq (löb-is-fixpoint f) {zero} γ = refl
eq (löb-is-fixpoint f) {suc n} γ = refl

fixpoint-unique : {T : Ty Γ ℓ} (f  : Tm Γ (▻' T ⇛ T)) (t s : Tm Γ T) →
                  app f (next' t) ≅ᵗᵐ t → app f (next' s) ≅ᵗᵐ s → t ≅ᵗᵐ s
eq (fixpoint-unique f t s t-fix s-fix) {x = zero}  γ =
  begin
    t ⟨ zero , γ ⟩'
  ≡˘⟨ eq t-fix γ ⟩
    f €⟨ zero , γ ⟩ tt
  ≡⟨ eq s-fix γ ⟩
    s ⟨ zero , γ ⟩' ∎
  where open ≡-Reasoning
eq (fixpoint-unique f t s t-fix s-fix) {x = suc n} γ =
  begin
    t ⟨ suc n , γ ⟩'
  ≡˘⟨ eq t-fix γ ⟩
    f €⟨ suc n , γ ⟩ (t ⟨ n , _ ⟩')
  ≡⟨ cong (f €⟨ suc n , γ ⟩_) (eq (fixpoint-unique f t s t-fix s-fix) {x = n}  _) ⟩
    f €⟨ suc n , γ ⟩ (s ⟨ n , _ ⟩')
  ≡⟨ eq s-fix γ ⟩
    s ⟨ suc n , γ ⟩' ∎
  where open ≡-Reasoning

-- ▻ is an applicative functor
_⟨$⟩_ : {T : Ty (◄ Γ) ℓ} {S : Ty (◄ Γ) ℓ'} → Tm (◄ Γ) (T ⇛ S) → Tm Γ (▻ T) → Tm Γ (▻ S)
f ⟨$⟩ t = next (app f (prev t))

_⊛_ : {T : Ty (◄ Γ) ℓ} {S : Ty (◄ Γ) ℓ'} → Tm Γ (▻ (T ⇛ S)) → Tm Γ (▻ T) → Tm Γ (▻ S)
f ⊛ t = prev f ⟨$⟩ t


--------------------------------------------------
-- Congruence and naturality for the later modality

▻-map : {T : Ty (◄ Γ) ℓ} {T' : Ty (◄ Γ) ℓ'} → (T ↣ T') → (▻ T ↣ ▻ T')
func (▻-map η) {zero} _ = tt
func (▻-map η) {suc n} t = func η t
naturality (▻-map η) {f = z≤n} _ = refl
naturality (▻-map η) {f = s≤s m≤n} t = naturality η t

▻'-map : {T : Ty Γ ℓ} {S : Ty Γ ℓ'} → (T ↣ S) → (▻' T ↣ ▻' S)
▻'-map η = ▻-map (ty-subst-map (from-earlier _) η)

▻-cong : {T : Ty (◄ Γ) ℓ} {T' : Ty (◄ Γ) ℓ'} → T ≅ᵗʸ T' → ▻ T ≅ᵗʸ ▻ T'
from (▻-cong T=T') = ▻-map (from T=T')
to (▻-cong T=T') = ▻-map (to T=T')
eq (isoˡ (▻-cong T=T')) {zero} _ = refl
eq (isoˡ (▻-cong T=T')) {suc n} t = eq (isoˡ T=T') t
eq (isoʳ (▻-cong T=T')) {zero} _ = refl
eq (isoʳ (▻-cong T=T')) {suc n} t = eq (isoʳ T=T') t

▻'-cong : {T : Ty Γ ℓ} {T' : Ty Γ ℓ'} → T ≅ᵗʸ T' → ▻' T ≅ᵗʸ ▻' T'
▻'-cong {Γ = Γ} T=T' = ▻-cong (ty-subst-cong-ty (from-earlier Γ) T=T')

next-cong : {T : Ty (◄ Γ) ℓ} {t t' : Tm (◄ Γ) T} → t ≅ᵗᵐ t' → next t ≅ᵗᵐ next t'
eq (next-cong t=t') {zero} _ = refl
eq (next-cong t=t') {suc n} γ = eq t=t' γ

prev-cong : {T : Ty (◄ Γ) ℓ} {t t' : Tm Γ (▻ T)} → t ≅ᵗᵐ t' → prev t ≅ᵗᵐ prev t'
eq (prev-cong t=t') γ = eq t=t' γ

löb-cong : (T : Ty Γ ℓ) {f f' : Tm Γ (▻' T ⇛ T)} → f ≅ᵗᵐ f' → löb T f ≅ᵗᵐ löb T f'
eq (löb-cong T f=f') {zero} γ = cong (_$⟨ z≤n , _ ⟩ tt) (eq f=f' γ)
eq (löb-cong T f=f') {suc n} γ = €-cong f=f' (eq (löb-cong T f=f') {n} _)

module _ {Γ : Ctx ω ℓ} {T : Ty (◄ Γ) ℓt} {T' : Ty (◄ Γ) ℓt'} (T=T' : T ≅ᵗʸ T') where
  next-ι : (t : Tm (◄ Γ) T') → ι[ ▻-cong T=T' ] next t ≅ᵗᵐ next (ι[ T=T' ] t)
  eq (next-ι t) {zero} _ = refl
  eq (next-ι t) {suc n} _ = refl

  prev-ι : (t : Tm Γ (▻ T')) → ι[ T=T' ] (prev t) ≅ᵗᵐ prev (ι[ ▻-cong T=T' ] t)
  eq (prev-ι t) _ = refl

löb-ι : {T : Ty Γ ℓ} {T' : Ty Γ ℓ'} (T=T' : T ≅ᵗʸ T') (f : Tm Γ (▻' T' ⇛ T')) →
        ι[ T=T' ] (löb T' f) ≅ᵗᵐ löb T (ι[ ⇛-cong (▻'-cong T=T') T=T' ] f)
eq (löb-ι T=T' f) {zero} γ = refl
eq (löb-ι {Γ = Γ}{T = T}{T' = T'} T=T' f) {suc n} γ = cong (func (to T=T')) (€-cong (≅ᵗᵐ-refl {t = f}) (
  begin
    löb T' f ⟨ n , _ ⟩'
  ≡˘⟨ eq (isoʳ T=T') _ ⟩
    func (from T=T') (func (to T=T') (löb T' f ⟨ n , _ ⟩'))
  ≡⟨ cong (func (from T=T')) (eq (löb-ι T=T' f) {n} _) ⟩
    func (from T=T') (löb T g ⟨ n , _ ⟩') ∎))
  where
    open ≡-Reasoning
    g : Tm Γ (▻' T ⇛ T)
    g = ι[ ⇛-cong (▻'-cong T=T') T=T' ] f

module _ {Δ : Ctx ω ℓ} {Γ : Ctx ω ℓ'} (σ : Δ ⇒ Γ) {T : Ty (◄ Γ) ℓt} where
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

module _ {Δ : Ctx ω ℓ} {Γ : Ctx ω ℓ'} (σ : Δ ⇒ Γ) {T : Ty Γ ℓt} where
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
                (löb T f) [ σ ]' ≅ᵗᵐ löb (T [ σ ]) (ι⁻¹[ ⇛-cong ▻'-natural ≅ᵗʸ-refl ] (ι⁻¹[ ⇛-natural σ ] (f [ σ ]')))
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
      g = ι⁻¹[ ⇛-cong ▻'-natural ≅ᵗʸ-refl ] (ι⁻¹[ ⇛-natural σ ] (f [ σ ]'))

-- ▻' is an applicative functor as well (but this requires ▻-cong).
module _ {T : Ty Γ ℓ} {S : Ty Γ ℓ'} where
  infixl 12 _⊛'_
  infixl 12 _⟨$⟩'_

  _⊛'_ : Tm Γ (▻' (T ⇛ S)) → Tm Γ (▻' T) → Tm Γ (▻' S)
  f ⊛' t = (ι⁻¹[ ▻-cong (⇛-natural _) ] f) ⊛ t

  _⟨$⟩'_ : Tm Γ (T ⇛ S) → Tm Γ (▻' T) → Tm Γ (▻' S)
  f ⟨$⟩' t = next' f ⊛' t


--------------------------------------------------
-- Proofs that ▻ and ▻' act functorially on types

▻-map-cong : {T : Ty (◄ Γ) ℓ} {T' : Ty (◄ Γ) ℓ'} {η φ : T ↣ T'} →
              η ≅ⁿ φ → ▻-map η ≅ⁿ ▻-map φ
eq (▻-map-cong e) {x = zero } _ = refl
eq (▻-map-cong e) {x = suc x} t = eq e t

▻'-map-cong : {T : Ty Γ ℓ} {S : Ty Γ ℓ'} {η φ : T ↣ S} →
               η ≅ⁿ φ → ▻'-map η ≅ⁿ ▻'-map φ
▻'-map-cong e = ▻-map-cong (ty-subst-map-cong e)

▻-map-id : {T : Ty (◄ Γ) ℓ} → ▻-map (id-trans T) ≅ⁿ id-trans (▻ T)
eq ▻-map-id {x = zero } _ = refl
eq ▻-map-id {x = suc x} _ = refl

▻'-map-id : {T : Ty Γ ℓ} → ▻'-map (id-trans T) ≅ⁿ id-trans (▻' T)
▻'-map-id {T = T} =
  begin
    ▻-map (ty-subst-map (from-earlier _) (id-trans T))
  ≅⟨ ▻-map-cong (ty-subst-map-id (from-earlier _)) ⟩
    ▻-map (id-trans (T [ from-earlier _ ]))
  ≅⟨ ▻-map-id ⟩
    id-trans (▻' T) ∎
  where open ≅ⁿ-Reasoning

▻-map-comp : {R : Ty (◄ Γ) ℓ} {S : Ty (◄ Γ) ℓ'} {T : Ty (◄ Γ) ℓ''}
              (η : S ↣ T) (φ : R ↣ S) →
              ▻-map (η ⊙ φ) ≅ⁿ ▻-map η ⊙ ▻-map φ
eq (▻-map-comp η φ) {x = zero } _ = refl
eq (▻-map-comp η φ) {x = suc x} _ = refl

▻'-map-comp : {R : Ty Γ ℓ} {S : Ty Γ ℓ'} {T : Ty Γ ℓ''}
               (η : S ↣ T) (φ : R ↣ S) →
               ▻'-map (η ⊙ φ) ≅ⁿ ▻'-map η ⊙ ▻'-map φ
▻'-map-comp η φ =
  begin
    ▻'-map (η ⊙ φ)
  ≅⟨⟩
    ▻-map (ty-subst-map (from-earlier _) (η ⊙ φ))
  ≅⟨ ▻-map-cong (ty-subst-map-comp (from-earlier _) η φ) ⟩
    ▻-map (ty-subst-map (from-earlier _) η ⊙ ty-subst-map (from-earlier _) φ)
  ≅⟨ ▻-map-comp _ _ ⟩
    ▻'-map η ⊙ ▻'-map φ ∎
  where open ≅ⁿ-Reasoning

◄-▻-,, : (Γ : Ctx ω ℓ) (T : Ty (◄ Γ) ℓ') → ◄ (Γ ,, ▻ T) ≅ᶜ ◄ Γ ,, T
func (from (◄-▻-,, Γ T)) γt = γt
naturality (from (◄-▻-,, Γ T)) γt = refl
func (to (◄-▻-,, Γ T)) γt = γt
naturality (to (◄-▻-,, Γ T)) γt = refl
eq (isoˡ (◄-▻-,, Γ T)) γt = refl
eq (isoʳ (◄-▻-,, Γ T)) γt = refl
