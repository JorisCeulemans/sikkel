--------------------------------------------------
-- The earlier-later dependent adjunction
--------------------------------------------------

module Applications.GuardedRecursion.Model.Modalities.Later where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.String using (String)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Type.Function
open import Model.CwF-Structure.Reflection.SubstitutionSequence

private
  variable
    m n : ℕ
    Γ Δ Θ : Ctx ω

infixl 12 _⟨$⟩_
infixl 12 _⊛_
infixr 4 löb[_∈▻'_]_


--------------------------------------------------
-- The "earlier" Context operation

ctx-m≤1+n : (Γ : Ctx ω) {m≤n : m ≤ n} {γ : Γ ⟨ suc n ⟩} →
            Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n n ⟫ γ) ≡ Γ ⟪ n≤1+n m ⟫ (Γ ⟪ s≤s m≤n ⟫ γ)
ctx-m≤1+n {m = m}{n = n} Γ {m≤n}{γ} =
  begin
    Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n n ⟫ γ)
  ≡⟨ ctx-comp Γ ⟨
    Γ ⟪ ≤-trans m≤n (n≤1+n n) ⟫ γ
  ≡⟨ cong (Γ ⟪_⟫ γ) (≤-irrelevant _ _) ⟩
    Γ ⟪ ≤-trans (n≤1+n m)(s≤s m≤n) ⟫ γ
  ≡⟨ ctx-comp Γ ⟩
    Γ ⟪ n≤1+n m ⟫ (Γ ⟪ s≤s m≤n ⟫ γ) ∎
  where open ≡-Reasoning

◄ : Ctx ω → Ctx ω
◄ Γ ⟨ n ⟩ = Γ ⟨ suc n ⟩
◄ Γ ⟪ m≤n ⟫ γ = Γ ⟪ s≤s m≤n ⟫ γ
ctx-id (◄ Γ) = ctx-id Γ
ctx-comp (◄ Γ) = ctx-comp Γ

◄-subst : (σ : Δ ⇒ Γ) → ◄ Δ ⇒ ◄ Γ
func (◄-subst σ) {n} = func σ {suc n}
naturality (◄-subst σ) {f = m≤n} = naturality σ {f = s≤s m≤n}

{-
-- The operations on types and terms are not used anywhere
◅-ty : Ty Γ → Ty (◄ Γ)
type (◅-ty T) n γ = T ⟨ suc n , γ ⟩
morph (◅-ty T) m≤n eγ = T ⟪ s≤s m≤n , eγ ⟫
morph-cong (◅-ty T) e = morph-cong T (cong s≤s e)
morph-id (◅-ty T) t = morph-id T t
morph-comp (◅-ty T) k≤m m≤n = morph-comp T (s≤s k≤m) (s≤s m≤n)

◅-tm : {T : Ty Γ} → Tm Γ T → Tm (◄ Γ) (◅-ty T)
term (◅-tm t) n γ = t ⟨ suc n , γ ⟩'
naturality (◅-tm t) m≤n eγ = naturality t (s≤s m≤n) eγ
-}

from-earlier : (Γ : Ctx ω) → ◄ Γ ⇒ Γ
func (from-earlier Γ) = Γ ⟪ n≤1+n _ ⟫_
naturality (from-earlier Γ) = ctx-m≤1+n Γ


--------------------------------------------------
-- Congruence, naturality and functoriality for earlier

◄-subst-cong : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → ◄-subst σ ≅ˢ ◄-subst τ
eq (◄-subst-cong σ=τ) δ = eq σ=τ δ

{-
-- The operations on types and terms are not used anywhere

◅-ty-cong : {T : Ty Γ} {T' : Ty Γ} → T ≅ᵗʸ T' → ◅-ty T ≅ᵗʸ ◅-ty T'
◅-ty-cong : {T : Ty Γ ℓ} {T' : Ty Γ ℓ'} → T ≅ᵗʸ T' → ◅-ty T ≅ᵗʸ ◅-ty T'
func (from (◅-ty-cong T=T')) = func (from T=T')
naturality (from (◅-ty-cong T=T')) = naturality (from T=T')
func (to (◅-ty-cong T=T')) = func (to T=T')
naturality (to (◅-ty-cong T=T')) = naturality (to T=T')
eq (isoˡ (◅-ty-cong T=T')) t = eq (isoˡ T=T') t
eq (isoʳ (◅-ty-cong T=T')) t = eq (isoʳ T=T') t

◅-tm-cong : {T : Ty Γ} {t t' : Tm Γ T} → t ≅ᵗᵐ t' → ◅-tm t ≅ᵗᵐ ◅-tm t'
eq (◅-tm-cong t=t') γ = eq t=t' γ

◅-tm-ι : {T : Ty Γ} {T' : Ty Γ} (T=T' : T ≅ᵗʸ T') (t : Tm Γ T') →
          ◅-tm (ι[ T=T' ] t) ≅ᵗᵐ ι[ ◅-ty-cong T=T' ] (◅-tm t)
eq (◅-tm-ι T=T' t) γ = refl

module _ {Δ : Ctx ω} {Γ : Ctx ω} (σ : Δ ⇒ Γ) {T : Ty Γ} where
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
eq (from-earlier-natural σ) δ = naturality σ

◄-subst-id : ◄-subst (id-subst Γ) ≅ˢ id-subst (◄ Γ)
eq ◄-subst-id _ = refl

◄-subst-⊚ : (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → ◄-subst (τ ⊚ σ) ≅ˢ ◄-subst τ ⊚ ◄-subst σ
eq (◄-subst-⊚ τ σ) _ = refl

instance
  ◄-is-functor : IsCtxFunctor ◄
  ctx-map {{◄-is-functor}} = ◄-subst
  ctx-map-cong {{◄-is-functor}} = ◄-subst-cong
  ctx-map-id {{◄-is-functor}} = ◄-subst-id
  ctx-map-⊚ {{◄-is-functor}} = ◄-subst-⊚


--------------------------------------------------
-- The later modality and corresponding term formers

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

▻' : Ty Γ → Ty Γ
▻' {Γ = Γ} T = ▻ (T [ from-earlier Γ ])

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

prev' : {T : Ty Γ} → Tm Γ T → Tm (◄ Γ) (T [ from-earlier Γ ])
prev' t = t [ from-earlier _ ]'

next' : {T : Ty Γ} → Tm Γ T → Tm Γ (▻' T)
next' t = next (prev' t)

löb : (T : Ty Γ) → Tm Γ (▻' T ⇛ T) → Tm Γ T
löb {Γ = Γ} T f = MkTm tm nat
  where
    tm : (n : ℕ) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
    tm zero    γ = f €⟨ zero , γ ⟩ tt
    tm (suc n) γ = f €⟨ suc n , γ ⟩ tm n (Γ ⟪ n≤1+n n ⟫ γ)

    open ≡-Reasoning
    nat : ∀ {m n} {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} (m≤n : m ≤ n) (eγ : Γ ⟪ m≤n ⟫ γn ≡ γm) →
          T ⟪ m≤n , eγ ⟫ tm n γn ≡ tm m γm
    nat {m = .zero} {n = zero}  z≤n _ = €-natural f
    nat {m = .zero} {n = suc n} z≤n _ = €-natural f
    nat {m = suc m} {n = suc n} {γ} {γ'} (s≤s m≤n) eγ =
      begin
        T ⟪ s≤s m≤n , eγ ⟫ f €⟨ suc n , γ ⟩ (tm n (Γ ⟪ n≤1+n n ⟫ γ))
      ≡⟨ €-natural f ⟩
        f €⟨ suc m , γ' ⟩ (T ⟪ m≤n , _ ⟫ (tm n (Γ ⟪ n≤1+n n ⟫ γ)))
      ≡⟨ cong (f €⟨ _ , _ ⟩_) (nat m≤n _) ⟩
        f €⟨ suc m , γ' ⟩ (tm m (Γ ⟪ n≤1+n m ⟫ γ')) ∎

löb' : (T : Ty Γ) → Tm (Γ ,, ▻' T) (T [ π ]) → Tm Γ T
löb' T f = löb T (lam (▻' T) f)

löb[_∈▻'_]_ : (v : String) (T : Ty Γ) → Tm (Γ ,, v ∈ ▻' T) (T [ π ]) → Tm Γ T
löb[_∈▻'_]_ v = löb'

löb-is-fixpoint : {T : Ty Γ} (f : Tm Γ (▻' T ⇛ T)) →
                  app f (next' (löb T f)) ≅ᵗᵐ löb T f
eq (löb-is-fixpoint f) {zero}  γ = refl
eq (löb-is-fixpoint f) {suc n} γ = refl

fixpoint-unique : {T : Ty Γ} (f  : Tm Γ (▻' T ⇛ T)) (t s : Tm Γ T) →
                  app f (next' t) ≅ᵗᵐ t → app f (next' s) ≅ᵗᵐ s → t ≅ᵗᵐ s
eq (fixpoint-unique f t s t-fix s-fix) {x = zero}  γ =
  begin
    t ⟨ zero , γ ⟩'
  ≡⟨ eq t-fix γ ⟨
    f €⟨ zero , γ ⟩ tt
  ≡⟨ eq s-fix γ ⟩
    s ⟨ zero , γ ⟩' ∎
  where open ≡-Reasoning
eq (fixpoint-unique f t s t-fix s-fix) {x = suc n} γ =
  begin
    t ⟨ suc n , γ ⟩'
  ≡⟨ eq t-fix γ ⟨
    f €⟨ suc n , γ ⟩ (t ⟨ n , _ ⟩')
  ≡⟨ cong (f €⟨ suc n , γ ⟩_) (eq (fixpoint-unique f t s t-fix s-fix) {x = n}  _) ⟩
    f €⟨ suc n , γ ⟩ (s ⟨ n , _ ⟩')
  ≡⟨ eq s-fix γ ⟩
    s ⟨ suc n , γ ⟩' ∎
  where open ≡-Reasoning

-- ▻ is an applicative functor
_⟨$⟩_ : {T : Ty (◄ Γ)} {S : Ty (◄ Γ)} → Tm (◄ Γ) (T ⇛ S) → Tm Γ (▻ T) → Tm Γ (▻ S)
f ⟨$⟩ t = next (app f (prev t))

_⊛_ : {T : Ty (◄ Γ)} {S : Ty (◄ Γ)} → Tm Γ (▻ (T ⇛ S)) → Tm Γ (▻ T) → Tm Γ (▻ S)
f ⊛ t = prev f ⟨$⟩ t


--------------------------------------------------
-- Congruence and naturality for the later modality

▻-map : {T : Ty (◄ Γ)} {T' : Ty (◄ Γ)} → (T ↣ T') → (▻ T ↣ ▻ T')
func (▻-map η) {zero} _ = tt
func (▻-map η) {suc n} t = func η t
naturality (▻-map η) {f = z≤n} = refl
naturality (▻-map η) {f = s≤s m≤n} = naturality η

▻'-map : {T : Ty Γ} {S : Ty Γ} → (T ↣ S) → (▻' T ↣ ▻' S)
▻'-map η = ▻-map (ty-subst-map (from-earlier _) η)

▻-cong : {T : Ty (◄ Γ)} {T' : Ty (◄ Γ)} → T ≅ᵗʸ T' → ▻ T ≅ᵗʸ ▻ T'
from (▻-cong T=T') = ▻-map (from T=T')
to (▻-cong T=T') = ▻-map (to T=T')
eq (isoˡ (▻-cong T=T')) {zero} _ = refl
eq (isoˡ (▻-cong T=T')) {suc n} = eq (isoˡ T=T')
eq (isoʳ (▻-cong T=T')) {zero} _ = refl
eq (isoʳ (▻-cong T=T')) {suc n} = eq (isoʳ T=T')

▻'-cong : {T : Ty Γ} {T' : Ty Γ} → T ≅ᵗʸ T' → ▻' T ≅ᵗʸ ▻' T'
▻'-cong {Γ = Γ} T=T' = ▻-cong (ty-subst-cong-ty (from-earlier Γ) T=T')

▻-cong-refl : {T : Ty (◄ Γ)} → ▻-cong (reflᵗʸ {T = T}) ≅ᵉ reflᵗʸ
eq (from-eq ▻-cong-refl) {zero}  _ = refl
eq (from-eq ▻-cong-refl) {suc n} _ = refl

▻-cong-sym : {T S : Ty (◄ Γ)} {e : T ≅ᵗʸ S} → ▻-cong (symᵗʸ e) ≅ᵉ symᵗʸ (▻-cong e)
eq (from-eq ▻-cong-sym) {zero}  _ = refl
eq (from-eq ▻-cong-sym) {suc n} _ = refl

▻-cong-trans : {R S T : Ty (◄ Γ)} {e1 : R ≅ᵗʸ S} {e2 : S ≅ᵗʸ T} → ▻-cong (transᵗʸ e1 e2) ≅ᵉ transᵗʸ (▻-cong e1) (▻-cong e2)
eq (from-eq ▻-cong-trans) {zero}  _ = refl
eq (from-eq ▻-cong-trans) {suc n} _ = refl

▻-cong-cong : {T S : Ty (◄ Γ)} {e e' : T ≅ᵗʸ S} → e ≅ᵉ e' → ▻-cong e ≅ᵉ ▻-cong e'
eq (from-eq (▻-cong-cong 𝑒)) {zero}  _ = refl
eq (from-eq (▻-cong-cong 𝑒)) {suc n} t = eq (from-eq 𝑒) t

next-cong : {T : Ty (◄ Γ)} {t t' : Tm (◄ Γ) T} → t ≅ᵗᵐ t' → next t ≅ᵗᵐ next t'
eq (next-cong t=t') {zero} _ = refl
eq (next-cong t=t') {suc n} = eq t=t'

prev-cong : {T : Ty (◄ Γ)} {t t' : Tm Γ (▻ T)} → t ≅ᵗᵐ t' → prev t ≅ᵗᵐ prev t'
eq (prev-cong t=t') = eq t=t'

löb-cong : (T : Ty Γ) {f f' : Tm Γ (▻' T ⇛ T)} → f ≅ᵗᵐ f' → löb T f ≅ᵗᵐ löb T f'
eq (löb-cong T f=f') {zero} γ = cong (_$⟨ z≤n , _ ⟩ tt) (eq f=f' γ)
eq (löb-cong T f=f') {suc n} _ = €-cong f=f' (eq (löb-cong T f=f') {n} _)

next-convert : {Γ : Ctx ω} {T T' : Ty (◄ Γ)} {η : T ↣ T'} (t : Tm (◄ Γ) T) →
               convert-tm (▻-map η) (next t) ≅ᵗᵐ next (convert-tm η t)
eq (next-convert t) {zero}  _ = refl
eq (next-convert t) {suc n} _ = refl

module _ {Γ : Ctx ω} {T : Ty (◄ Γ)} {T' : Ty (◄ Γ)} {T=T' : T ≅ᵗʸ T'} where
  next-ι : (t : Tm (◄ Γ) T') → ι[ ▻-cong T=T' ] next t ≅ᵗᵐ next (ι[ T=T' ] t)
  eq (next-ι t) {zero}  _ = refl
  eq (next-ι t) {suc n} _ = refl

  prev-ι : (t : Tm Γ (▻ T')) → ι[ T=T' ] (prev t) ≅ᵗᵐ prev (ι[ ▻-cong T=T' ] t)
  eq (prev-ι t) _ = refl

löb-ι : {T : Ty Γ} {T' : Ty Γ} {T=T' : T ≅ᵗʸ T'} (f : Tm Γ (▻' T' ⇛ T')) →
        ι[ T=T' ] (löb T' f) ≅ᵗᵐ löb T (ι[ ⇛-cong (▻'-cong T=T') T=T' ] f)
eq (löb-ι f) {zero} _ = refl
eq (löb-ι {Γ = Γ}{T = T}{T' = T'}{T=T' = T=T'} f) {suc n} γ = cong (func (to T=T')) (€-cong (reflᵗᵐ {t = f}) (
  begin
    löb T' f ⟨ n , _ ⟩'
  ≡⟨ eq (isoʳ T=T') _ ⟨
    func (from T=T') (func (to T=T') (löb T' f ⟨ n , _ ⟩'))
  ≡⟨ cong (func (from T=T')) (eq (löb-ι f) {n} _) ⟩
    func (from T=T') (löb T g ⟨ n , _ ⟩') ∎))
  where
    open ≡-Reasoning
    g : Tm Γ (▻' T ⇛ T)
    g = ι[ ⇛-cong (▻'-cong T=T') T=T' ] f

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

module _ {Δ : Ctx ω} {Γ : Ctx ω} (σ : Δ ⇒ Γ) {T : Ty Γ} where
  ▻'-natural : (▻' T) [ σ ] ≅ᵗʸ ▻' (T [ σ ])
  ▻'-natural =
    transᵗʸ (▻-natural σ) (▻-cong (ty-subst-seq-cong (from-earlier Γ ∷ ◄-subst σ ◼) (σ ∷ from-earlier Δ ◼) T (from-earlier-natural σ)))

  löb-natural : (f : Tm Γ (▻' T ⇛ T)) →
                (löb T f) [ σ ]' ≅ᵗᵐ löb (T [ σ ]) (ι⁻¹[ ⇛-cong ▻'-natural reflᵗʸ ] (ι⁻¹[ ⇛-natural σ ] (f [ σ ]')))
  eq (löb-natural f) {zero} δ = $-cong (f ⟨ 0 , func σ δ ⟩') refl
  eq (löb-natural f) {suc n} δ =
    begin
      f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , ctx-id Γ ⟩ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ (func σ δ) ⟩')
    ≡⟨ $-cong (f ⟨ suc n , func σ δ ⟩') refl ⟩
      f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ (func σ δ) ⟩')
    ≡⟨ cong (f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩_) (naturality (löb T f) ≤-refl β) ⟨
      f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩ (T ⟪ ≤-refl , β ⟫ ((löb T f) [ σ ]' ⟨ n , Δ ⟪ n≤1+n n ⟫ δ ⟩'))
    ≡⟨ cong (f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩_ ∘ T ⟪ ≤-refl , β ⟫_) (eq (löb-natural f) {n} (Δ ⟪ n≤1+n n ⟫ δ)) ⟩
      f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩ (T ⟪ ≤-refl , β ⟫ (löb (T [ σ ]) g ⟨ n , Δ ⟪ n≤1+n n ⟫ δ ⟩')) ∎
    where
      open ≡-Reasoning
      α = _
      β = _
      g : Tm Δ (▻' (T [ σ ]) ⇛ (T [ σ ]))
      g = ι⁻¹[ ⇛-cong ▻'-natural reflᵗʸ ] (ι⁻¹[ ⇛-natural σ ] (f [ σ ]'))

{-
instance
  ▻'-closed : {A : ClosedTy ω} {{_ : IsClosedNatural A}} → IsClosedNatural (▻' A)
  closed-natural {{▻'-closed}} σ = transᵗʸ (▻'-natural σ) (▻'-cong (closed-natural σ))

  ▻-closed : {A : ClosedTy ω} {{_ : IsClosedNatural A}} → IsClosedNatural (▻ A)
  closed-natural {{▻-closed}} σ = transᵗʸ (▻-natural σ) (▻-cong (closed-natural (◄-subst σ)))
-}

-- ▻' is an applicative functor as well (but this requires ▻-cong).
module _ {T : Ty Γ} {S : Ty Γ} where
  infixl 12 _⊛'_
  infixl 12 _⟨$⟩'_

  _⊛'_ : Tm Γ (▻' (T ⇛ S)) → Tm Γ (▻' T) → Tm Γ (▻' S)
  f ⊛' t = (ι⁻¹[ ▻-cong (⇛-natural _) ] f) ⊛ t

  _⟨$⟩'_ : Tm Γ (T ⇛ S) → Tm Γ (▻' T) → Tm Γ (▻' S)
  f ⟨$⟩' t = next' f ⊛' t

-- The following operations would be easier to define for closed types (since we can then make use of
-- lamι, varι, ⟨$⟩ and ⊛) but we want them to work for all types.
lift▻ : {T S : Ty (◄ Γ)} → Tm (◄ Γ) (T ⇛ S) → Tm Γ (▻ T ⇛ ▻ S)
lift▻ {T = T} f = lam (▻ T) (
  ι[ ▻-natural π ] next (
  ι⁻¹[ ⇛-natural (◄-subst π) ] (f [ ◄-subst π ]') $ prev (ι⁻¹[ ▻-natural π ] ξ)))

lift2▻ : {T S R : Ty (◄ Γ)} → Tm (◄ Γ) (T ⇛ S ⇛ R) → Tm Γ (▻ T ⇛ ▻ S ⇛ ▻ R)
lift2▻ {T = T}{S} f = lam (▻ T) (ι[ ⇛-natural π ] ι[ ⇛-cong (▻-natural π) (▻-natural π) ]
  lift▻ (ι⁻¹[ ⇛-natural (◄-subst π) ] (
  ι⁻¹[ ⇛-natural (◄-subst π) ] (f [ ◄-subst π ]') $ prev (ι⁻¹[ ▻-natural π ] ξ))))

lift▻' : {T S : Ty Γ} → Tm Γ (T ⇛ S) → Tm Γ (▻' T ⇛ ▻' S)
lift▻' {Γ = Γ} f = lift▻ (ι⁻¹[ ⇛-natural (from-earlier Γ) ] (f [ from-earlier Γ ]'))

lift2▻' : {T S R : Ty Γ} → Tm Γ (T ⇛ S ⇛ R) → Tm Γ (▻' T ⇛ ▻' S ⇛ ▻' R)
lift2▻' {Γ = Γ} f =
  lift2▻ (ι⁻¹[ ⇛-cong reflᵗʸ (⇛-natural (from-earlier Γ)) ] ι⁻¹[ ⇛-natural (from-earlier Γ) ] (f [ from-earlier Γ ]'))


--------------------------------------------------
-- Proofs that ▻ and ▻' act functorially on types

▻-map-cong : {T : Ty (◄ Γ)} {T' : Ty (◄ Γ)} {η φ : T ↣ T'} →
              η ≅ⁿ φ → ▻-map η ≅ⁿ ▻-map φ
eq (▻-map-cong 𝔢) {x = zero} _ = refl
eq (▻-map-cong 𝔢) {x = suc _} = eq 𝔢

▻'-map-cong : {T : Ty Γ} {S : Ty Γ} {η φ : T ↣ S} →
               η ≅ⁿ φ → ▻'-map η ≅ⁿ ▻'-map φ
▻'-map-cong 𝔢 = ▻-map-cong (ty-subst-map-cong 𝔢)

▻-map-id : {T : Ty (◄ Γ)} → ▻-map (id-trans T) ≅ⁿ id-trans (▻ T)
eq ▻-map-id {x = zero} _ = refl
eq ▻-map-id {x = suc _} _ = refl

▻'-map-id : {T : Ty Γ} → ▻'-map (id-trans T) ≅ⁿ id-trans (▻' T)
▻'-map-id {T = T} =
  begin
    ▻-map (ty-subst-map (from-earlier _) (id-trans T))
  ≅⟨ ▻-map-cong ty-subst-map-id ⟩
    ▻-map (id-trans (T [ from-earlier _ ]))
  ≅⟨ ▻-map-id ⟩
    id-trans (▻' T) ∎
  where open ≅ⁿ-Reasoning

▻-map-comp : {R : Ty (◄ Γ)} {S : Ty (◄ Γ)} {T : Ty (◄ Γ)}
             {η : S ↣ T} {φ : R ↣ S} →
             ▻-map (η ⊙ φ) ≅ⁿ ▻-map η ⊙ ▻-map φ
eq ▻-map-comp {x = zero} _ = refl
eq ▻-map-comp {x = suc _} _ = refl

▻'-map-comp : {R : Ty Γ} {S : Ty Γ} {T : Ty Γ}
              {η : S ↣ T} {φ : R ↣ S} →
              ▻'-map (η ⊙ φ) ≅ⁿ ▻'-map η ⊙ ▻'-map φ
▻'-map-comp {η = η} {φ} =
  begin
    ▻'-map (η ⊙ φ)
  ≅⟨⟩
    ▻-map (ty-subst-map (from-earlier _) (η ⊙ φ))
  ≅⟨ ▻-map-cong ty-subst-map-⊙ ⟩
    ▻-map (ty-subst-map (from-earlier _) η ⊙ ty-subst-map (from-earlier _) φ)
  ≅⟨ ▻-map-comp ⟩
    ▻'-map η ⊙ ▻'-map φ ∎
  where open ≅ⁿ-Reasoning

◄-▻-,, : (Γ : Ctx ω) (T : Ty (◄ Γ)) → ◄ (Γ ,, ▻ T) ≅ᶜ ◄ Γ ,, T
func (from (◄-▻-,, Γ T)) γt = γt
naturality (from (◄-▻-,, Γ T)) = refl
func (to (◄-▻-,, Γ T)) γt = γt
naturality (to (◄-▻-,, Γ T)) = refl
eq (isoˡ (◄-▻-,, Γ T)) γt = refl
eq (isoʳ (◄-▻-,, Γ T)) γt = refl
