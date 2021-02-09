--------------------------------------------------
-- The earlier-later dependent adjunction
--------------------------------------------------

module GuardedRecursion.Modalities.Later where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.String using (String)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (id; _∘_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality) renaming (setoid to ≡setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

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
            Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n n ⟫ γ) ≈[ Γ ]≈ Γ ⟪ n≤1+n m ⟫ (Γ ⟪ s≤s m≤n ⟫ γ)
ctx-m≤1+n {m = m}{n = n} Γ m≤n γ =
  begin
    Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n n ⟫ γ)
  ≈˘⟨ rel-comp Γ m≤n (n≤1+n n) γ ⟩
    Γ ⟪ ≤-trans m≤n (n≤1+n n) ⟫ γ
  ≈⟨ rel-hom-cong Γ (≤-irrelevant _ _) ⟩
    Γ ⟪ ≤-trans (n≤1+n m)(s≤s m≤n) ⟫ γ
  ≈⟨ rel-comp Γ (n≤1+n m) (s≤s m≤n) γ ⟩
    Γ ⟪ n≤1+n m ⟫ (Γ ⟪ s≤s m≤n ⟫ γ) ∎
  where open SetoidReasoning (setoid Γ m)

◄ : Ctx ω ℓ → Ctx ω ℓ
setoid (◄ Γ) n = setoid Γ (suc n)
rel (◄ Γ) m≤n = Γ ⟪ s≤s m≤n ⟫_
rel-cong (◄ Γ) m≤n = rel-cong Γ (s≤s m≤n)
rel-id (◄ Γ) = rel-id Γ
rel-comp (◄ Γ) k≤m m≤n = rel-comp Γ (s≤s k≤m) (s≤s m≤n)

◄-subst : (σ : Δ ⇒ Γ) → ◄ Δ ⇒ ◄ Γ
func (◄-subst σ) {n} = func σ {suc n}
func-cong (◄-subst σ) = func-cong σ
naturality (◄-subst σ) {f = m≤n} = naturality σ {f = s≤s m≤n}

{-
-- The operations on types and terms are not used anywhere
◅-ty : Ty Γ ℓ r → Ty (◄ Γ) ℓ r
type (◅-ty T) n γ = type T (suc n) γ
morph (◅-ty T) m≤n eγ = T ⟪ s≤s m≤n , eγ ⟫_
morph-cong (◅-ty T) m≤n eγ = morph-cong T (s≤s m≤n) eγ
morph-hom-cong (◅-ty T) e = morph-hom-cong T (cong s≤s e)
morph-id (◅-ty T) t = morph-id T t
morph-comp (◅-ty T) k≤m m≤n = morph-comp T (s≤s k≤m) (s≤s m≤n)

◅-tm : {T : Ty Γ ℓ r} → Tm Γ T → Tm (◄ Γ) (◅-ty T)
term (◅-tm t) n γ = t ⟨ suc n , γ ⟩'
naturality (◅-tm t) m≤n eγ = naturality t (s≤s m≤n) eγ
-}

from-earlier : (Γ : Ctx ω ℓ) → ◄ Γ ⇒ Γ
func (from-earlier Γ) = Γ ⟪ n≤1+n _ ⟫_
func-cong (from-earlier Γ) = rel-cong Γ _
naturality (from-earlier Γ) γ = ctx-m≤1+n Γ _ γ


--------------------------------------------------
-- Congruence, naturality and functoriality for earlier

◄-subst-cong : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → ◄-subst σ ≅ˢ ◄-subst τ
eq (◄-subst-cong σ=τ) δ = eq σ=τ δ

{-
-- The operations on types and terms are not used anywhere
◅-ty-cong : {T : Ty Γ ℓ r} {T' : Ty Γ ℓ' r'} → T ≅ᵗʸ T' → ◅-ty T ≅ᵗʸ ◅-ty T'
func (from (◅-ty-cong T=T')) = func (from T=T')
func-cong (from (◅-ty-cong T=T')) = func-cong (from T=T')
naturality (from (◅-ty-cong T=T')) = naturality (from T=T')
func (to (◅-ty-cong T=T')) = func (to T=T')
func-cong (to (◅-ty-cong T=T')) = func-cong (to T=T')
naturality (to (◅-ty-cong T=T')) = naturality (to T=T')
eq (isoˡ (◅-ty-cong T=T')) t = eq (isoˡ T=T') t
eq (isoʳ (◅-ty-cong T=T')) t = eq (isoʳ T=T') t

◅-tm-cong : {T : Ty Γ ℓ r} {t t' : Tm Γ T} → t ≅ᵗᵐ t' → ◅-tm t ≅ᵗᵐ ◅-tm t'
eq (◅-tm-cong t=t') γ = eq t=t' γ

◅-tm-ι : {T : Ty Γ ℓ r} {T' : Ty Γ ℓ' r'} (T=T' : T ≅ᵗʸ T') (t : Tm Γ T') →
          ◅-tm (ι[ T=T' ] t) ≅ᵗᵐ ι[ ◅-ty-cong T=T' ] (◅-tm t)
eq (◅-tm-ι {T = T} T=T' t) γ = ty≈-refl (◅-ty T)

module _ {Δ : Ctx ω ℓ r} {Γ : Ctx ω ℓ' r'} (σ : Δ ⇒ Γ) {T : Ty Γ ℓt rt} where
  ◅-ty-natural : (◅-ty T) [ ◄-subst σ ] ≅ᵗʸ ◅-ty (T [ σ ])
  func (from ◅-ty-natural) = id
  func-cong (from ◅-ty-natural) = id
  naturality (from ◅-ty-natural) _ = ty≈-refl T
  func (to ◅-ty-natural) = id
  func-cong (to ◅-ty-natural) = id
  naturality (to ◅-ty-natural) _ = ty≈-refl T
  eq (isoˡ ◅-ty-natural) _ = ty≈-refl T
  eq (isoʳ ◅-ty-natural) _ = ty≈-refl T

  ◅-tm-natural : (t : Tm Γ T) → (◅-tm t) [ ◄-subst σ ]' ≅ᵗᵐ ι[ ◅-ty-natural ] (◅-tm (t [ σ ]'))
  eq (◅-tm-natural t) _ = ty≈-refl T
-}

from-earlier-natural : (σ : Δ ⇒ Γ) → from-earlier Γ ⊚ ◄-subst σ ≅ˢ σ ⊚ from-earlier Δ
eq (from-earlier-natural σ) δ = naturality σ δ

◄-subst-id : ◄-subst (id-subst Γ) ≅ˢ id-subst (◄ Γ)
eq (◄-subst-id {Γ = Γ}) _ = ctx≈-refl (◄ Γ)

◄-subst-⊚ : (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → ◄-subst (τ ⊚ σ) ≅ˢ ◄-subst τ ⊚ ◄-subst σ
eq (◄-subst-⊚ {Θ = Θ} τ σ) _ = ctx≈-refl (◄ Θ)


--------------------------------------------------
-- The later modality and corresponding term formers

⊤-setoid : Setoid ℓ ℓ
Setoid.Carrier ⊤-setoid = ⊤
Setoid._≈_ ⊤-setoid tt tt = ⊤
Setoid.isEquivalence ⊤-setoid = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }

▻ : Ty (◄ Γ) ℓ → Ty Γ ℓ
type (▻ T)  zero   γ = ⊤-setoid
type (▻ T) (suc n) γ = type T n γ
morph (▻ T) z≤n _ _ = tt
morph (▻ T) (s≤s m≤n) eγ = T ⟪ m≤n , eγ ⟫_
morph-cong (▻ T) z≤n _ _ = tt
morph-cong (▻ T) (s≤s m≤n) = morph-cong T m≤n
morph-hom-cong (▻ T) {f = z≤n}     {f' = z≤n}      _ = tt
morph-hom-cong (▻ T) {f = s≤s m≤n} {f' = s≤s m≤n'} e = morph-hom-cong T (≤-irrelevant m≤n m≤n')
morph-id (▻ T) {zero} _ = tt
morph-id (▻ T) {suc n} = morph-id T
morph-comp (▻ T) z≤n m≤n _ _ _ = tt
morph-comp (▻ T) (s≤s k≤m) (s≤s m≤n) = morph-comp T k≤m m≤n

▻' : Ty Γ ℓ → Ty Γ ℓ
▻' {Γ = Γ} T = ▻ (T [ from-earlier Γ ])

module _ {T : Ty (◄ Γ) ℓ} where
  next : Tm (◄ Γ) T → Tm Γ (▻ T)
  term (next t) zero _ = tt
  term (next t) (suc n) γ = t ⟨ n , γ ⟩'
  naturality (next t) z≤n _ = tt
  naturality (next t) (s≤s m≤n) eγ = naturality t m≤n eγ

  prev : Tm Γ (▻ T) → Tm (◄ Γ) T
  term (prev t) n γ = t ⟨ suc n , γ ⟩'
  naturality (prev t) m≤n eγ = naturality t (s≤s m≤n) eγ

  prev-next : (t : Tm (◄ Γ) T) → prev (next t) ≅ᵗᵐ t
  eq (prev-next t) _ = ty≈-refl T

  next-prev : (t : Tm Γ (▻ T)) → next (prev t) ≅ᵗᵐ t
  eq (next-prev t) {zero}  γ = tt
  eq (next-prev t) {suc n} γ = ty≈-refl T

prev' : {T : Ty Γ ℓ} → Tm Γ T → Tm (◄ Γ) (T [ from-earlier Γ ])
prev' t = t [ from-earlier _ ]'

next' : {T : Ty Γ ℓ} → Tm Γ T → Tm Γ (▻' T)
next' t = next (prev' t)

-- TODO: Update : See if T can be made implicit.
löb : (T : Ty Γ ℓ) → Tm Γ (▻' T ⇛ T) → Tm Γ T
term (löb T f) zero γ = f €⟨ zero , γ ⟩ tt
term (löb {Γ = Γ} T f) (suc n) γ = f €⟨ suc n , γ ⟩ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩')
naturality (löb T f) {y = zero} z≤n eγ = €-natural f z≤n eγ tt
naturality (löb {Γ = Γ} T f) {y = suc n} z≤n {γ} eγ = €-natural f z≤n eγ ((löb T f) ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩')
naturality (löb {Γ = Γ} T f) {x = suc m} {y = suc n} (s≤s m≤n) {γ} {γ'} eγ =
  begin
    T ⟪ s≤s m≤n , eγ ⟫ f €⟨ suc n , γ ⟩ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩')
  ≈⟨ €-natural f (s≤s m≤n) eγ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩') ⟩
    f €⟨ suc m , γ' ⟩ (T ⟪ m≤n , _ ⟫ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩'))
  ≈⟨ €-congʳ f (naturality (löb T f) m≤n _) ⟩
    f €⟨ suc m , γ' ⟩ (löb T f ⟨ m , Γ ⟪ n≤1+n m ⟫ γ' ⟩') ∎
  where open SetoidReasoning (type T (suc m) γ')

löb' : (T : Ty Γ ℓ) → Tm (Γ ,, ▻' T) (T [ π ]) → Tm Γ T
löb' T f = löb T (lam (▻' T) f)

nlöb'[_∈_]_ : (v : String) (T : Ty Γ ℓ) → Tm (Γ ,, v ∈ ▻' T) (T [ π ]) → Tm Γ T
nlöb'[_∈_]_ v = löb'

löb-is-fixpoint : {T : Ty Γ ℓ} (f : Tm Γ (▻' T ⇛ T)) →
                  app f (next' (löb T f)) ≅ᵗᵐ löb T f
eq (löb-is-fixpoint {T = T} f) {zero}  γ = ty≈-refl T
eq (löb-is-fixpoint {T = T} f) {suc n} γ = ty≈-refl T

fixpoint-unique : {T : Ty Γ ℓ} (f  : Tm Γ (▻' T ⇛ T)) (t s : Tm Γ T) →
                  app f (next' t) ≅ᵗᵐ t → app f (next' s) ≅ᵗᵐ s → t ≅ᵗᵐ s
eq (fixpoint-unique {T = T} f t s t-fix s-fix) {x = zero} γ =
  begin
    t ⟨ zero , γ ⟩'
  ≈˘⟨ eq t-fix γ ⟩
    f €⟨ zero , γ ⟩ tt
  ≈⟨ eq s-fix γ ⟩
    s ⟨ zero , γ ⟩' ∎
  where open SetoidReasoning (type T zero γ)
eq (fixpoint-unique {T = T} f t s t-fix s-fix) {x = suc n} γ =
  begin
    t ⟨ suc n , γ ⟩'
  ≈˘⟨ eq t-fix γ ⟩
    f €⟨ suc n , γ ⟩ (t ⟨ n , _ ⟩')
  ≈⟨ €-congʳ f (eq (fixpoint-unique f t s t-fix s-fix) {x = n}  _) ⟩
    f €⟨ suc n , γ ⟩ (s ⟨ n , _ ⟩')
  ≈⟨ eq s-fix γ ⟩
    s ⟨ suc n , γ ⟩' ∎
  where open SetoidReasoning (type T (suc n) γ)

-- ▻ is an applicative functor
_⟨$⟩_ : {T : Ty (◄ Γ) ℓ} {S : Ty (◄ Γ) ℓ'} → Tm (◄ Γ) (T ⇛ S) → Tm Γ (▻ T) → Tm Γ (▻ S)
f ⟨$⟩ t = next (app f (prev t))

_⊛_ : {T : Ty (◄ Γ) ℓ} {S : Ty (◄ Γ) ℓ'} → Tm Γ (▻ (T ⇛ S)) → Tm Γ (▻ T) → Tm Γ (▻ S)
f ⊛ t = prev f ⟨$⟩ t


--------------------------------------------------
-- Congruence and naturality for the later modality

▻-map : {T : Ty (◄ Γ) ℓ} {T' : Ty (◄ Γ) ℓ'} → (T ↣ T') → (▻ T ↣ ▻ T')
func (▻-map η) {zero} _ = tt
func (▻-map η) {suc n} = func η
func-cong (▻-map η) {zero} _ = tt
func-cong (▻-map η) {suc n} = func-cong η
naturality (▻-map η) {f = z≤n} _ = tt
naturality (▻-map η) {f = s≤s m≤n} = naturality η

▻'-map : {T : Ty Γ ℓ} {S : Ty Γ ℓ'} → (T ↣ S) → (▻' T ↣ ▻' S)
▻'-map η = ▻-map (ty-subst-map (from-earlier _) η)

▻-cong : {T : Ty (◄ Γ) ℓ} {T' : Ty (◄ Γ) ℓ'} → T ≅ᵗʸ T' → ▻ T ≅ᵗʸ ▻ T'
from (▻-cong T=T') = ▻-map (from T=T')
to (▻-cong T=T') = ▻-map (to T=T')
eq (isoˡ (▻-cong T=T')) {zero} _ = tt
eq (isoˡ (▻-cong T=T')) {suc n} = eq (isoˡ T=T')
eq (isoʳ (▻-cong T=T')) {zero} _ = tt
eq (isoʳ (▻-cong T=T')) {suc n} = eq (isoʳ T=T')

▻'-cong : {T : Ty Γ ℓ} {T' : Ty Γ ℓ'} → T ≅ᵗʸ T' → ▻' T ≅ᵗʸ ▻' T'
▻'-cong {Γ = Γ} T=T' = ▻-cong (ty-subst-cong-ty (from-earlier Γ) T=T')

next-cong : {T : Ty (◄ Γ) ℓ} {t t' : Tm (◄ Γ) T} → t ≅ᵗᵐ t' → next t ≅ᵗᵐ next t'
eq (next-cong t=t') {zero} _ = tt
eq (next-cong t=t') {suc n} = eq t=t'

prev-cong : {T : Ty (◄ Γ) ℓ} {t t' : Tm Γ (▻ T)} → t ≅ᵗᵐ t' → prev t ≅ᵗᵐ prev t'
eq (prev-cong t=t') = eq t=t'

löb-cong : (T : Ty Γ ℓ) {f f' : Tm Γ (▻' T ⇛ T)} → f ≅ᵗᵐ f' → löb T f ≅ᵗᵐ löb T f'
eq (löb-cong T f=f') {zero}  _ = €-congˡ f=f'
eq (löb-cong T f=f') {suc n} _ = €-cong f=f' (eq (löb-cong T f=f') {n} _)

module _ {Γ : Ctx ω ℓ} {T : Ty (◄ Γ) ℓt} {T' : Ty (◄ Γ) ℓt'} (T=T' : T ≅ᵗʸ T') where
  next-ι : (t : Tm (◄ Γ) T') → ι[ ▻-cong T=T' ] next t ≅ᵗᵐ next (ι[ T=T' ] t)
  eq (next-ι t) {zero}  _ = tt
  eq (next-ι t) {suc n} _ = ty≈-refl T

  prev-ι : (t : Tm Γ (▻ T')) → ι[ T=T' ] (prev t) ≅ᵗᵐ prev (ι[ ▻-cong T=T' ] t)
  eq (prev-ι t) _ = ty≈-refl T

löb-ι : {T : Ty Γ ℓ} {T' : Ty Γ ℓ'} (T=T' : T ≅ᵗʸ T') (f : Tm Γ (▻' T' ⇛ T')) →
        ι[ T=T' ] (löb T' f) ≅ᵗᵐ löb T (ι[ ⇛-cong (▻'-cong T=T') T=T' ] f)
eq (löb-ι {T = T} T=T' f) {zero} _ = ty≈-refl T
eq (löb-ι {Γ = Γ}{T = T}{T' = T'} T=T' f) {suc n} γ = func-cong (to T=T') (€-congʳ f (
  begin
    löb T' f ⟨ n , _ ⟩'
  ≈˘⟨ eq (isoʳ T=T') _ ⟩
    func (from T=T') (func (to T=T') (löb T' f ⟨ n , _ ⟩'))
  ≈⟨ func-cong (from T=T') (eq (löb-ι T=T' f) {n} _) ⟩
    func (from T=T') (löb T g ⟨ n , _ ⟩') ∎))
  where
    open SetoidReasoning (type T' n (func (from-earlier Γ) γ))
    g : Tm Γ (▻' T ⇛ T)
    g = ι[ ⇛-cong (▻'-cong T=T') T=T' ] f

module _ {Δ : Ctx ω ℓ} {Γ : Ctx ω ℓ'} (σ : Δ ⇒ Γ) {T : Ty (◄ Γ) ℓt} where
  ▻-natural-from : (▻ T) [ σ ] ↣ ▻ (T [ ◄-subst σ ])
  func ▻-natural-from {zero}  = id
  func ▻-natural-from {suc n} = id
  func-cong ▻-natural-from {zero}  = id
  func-cong ▻-natural-from {suc n} = id
  naturality ▻-natural-from {f = z≤n}     _ = tt
  naturality ▻-natural-from {f = s≤s m≤n} _ = ty≈-refl T

  ▻-natural-to : ▻ (T [ ◄-subst σ ]) ↣ (▻ T) [ σ ]
  func ▻-natural-to {zero}  = id
  func ▻-natural-to {suc n} = id
  func-cong ▻-natural-to {zero}  = id
  func-cong ▻-natural-to {suc n} = id
  naturality ▻-natural-to {f = z≤n}     _ = tt
  naturality ▻-natural-to {f = s≤s m≤n} _ = ty≈-refl T

  ▻-natural : (▻ T) [ σ ] ≅ᵗʸ ▻ (T [ ◄-subst σ ])
  from ▻-natural = ▻-natural-from
  to ▻-natural = ▻-natural-to
  eq (isoˡ ▻-natural) {zero}  _ = tt
  eq (isoˡ ▻-natural) {suc n} _ = ty≈-refl T
  eq (isoʳ ▻-natural) {zero}  _ = tt
  eq (isoʳ ▻-natural) {suc n} _ = ty≈-refl T

  next-natural : (t : Tm (◄ Γ) T) → (next t) [ σ ]' ≅ᵗᵐ ι[ ▻-natural ] (next (t [ ◄-subst σ ]'))
  eq (next-natural t) {zero}  _ = tt
  eq (next-natural t) {suc n} _ = ty≈-refl T

  prev-natural : (t : Tm Γ (▻ T)) → (prev t) [ ◄-subst σ ]' ≅ᵗᵐ prev (ι⁻¹[ ▻-natural ] (t [ σ ]'))
  eq (prev-natural t) _ = ty≈-refl T

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
  eq (löb-natural f) {zero}  δ = $-hom-cong (f ⟨ 0 , func σ δ ⟩') refl
  eq (löb-natural f) {suc n} δ =
    begin
      f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , rel-id Γ (func σ δ) ⟩ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ (func σ δ) ⟩')
    ≈⟨ $-hom-cong (f ⟨ suc n , func σ δ ⟩') refl ⟩
      f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ (func σ δ) ⟩')
    ≈˘⟨ $-cong (f ⟨ suc n , func σ δ ⟩') (s≤s ≤-refl) α (naturality (löb T f) ≤-refl β) ⟩
      f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩ (T ⟪ ≤-refl , β ⟫ ((löb T f) [ σ ]' ⟨ n , Δ ⟪ n≤1+n n ⟫ δ ⟩'))
    ≈⟨ $-cong (f ⟨ suc n , func σ δ ⟩') (s≤s ≤-refl) α (morph-cong T ≤-refl β (eq (löb-natural f) {n} (Δ ⟪ n≤1+n n ⟫ δ))) ⟩
      f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩ (T ⟪ ≤-refl , β ⟫ (löb (T [ σ ]) g ⟨ n , Δ ⟪ n≤1+n n ⟫ δ ⟩')) ∎
    where
      open SetoidReasoning (type T (suc n) (func σ δ))
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
eq (▻-map-cong e) {x = zero} _ = tt
eq (▻-map-cong e) {x = suc x} = eq e

▻'-map-cong : {T : Ty Γ ℓ} {S : Ty Γ ℓ'} {η φ : T ↣ S} →
               η ≅ⁿ φ → ▻'-map η ≅ⁿ ▻'-map φ
▻'-map-cong e = ▻-map-cong (ty-subst-map-cong e)

▻-map-id : {T : Ty (◄ Γ) ℓ} → ▻-map (id-trans T) ≅ⁿ id-trans (▻ T)
eq ▻-map-id {x = zero}  _ = tt
eq (▻-map-id {T = T}) {x = suc x} _ = ty≈-refl T

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
eq (▻-map-comp η φ) {x = zero}  _ = tt
eq (▻-map-comp {T = T} η φ) {x = suc _} _ = ty≈-refl T

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
func-cong (from (◄-▻-,, Γ T)) e = e
naturality (from (◄-▻-,, Γ T)) γt = ctx≈-refl (◄ Γ ,, T)
func (to (◄-▻-,, Γ T)) γt = γt
func-cong (to (◄-▻-,, Γ T)) e = e
naturality (to (◄-▻-,, Γ T)) γt = ctx≈-refl (◄ (Γ ,, ▻ T))
eq (isoˡ (◄-▻-,, Γ T)) γt = ctx≈-refl (◄ (Γ ,, ▻ T))
eq (isoʳ (◄-▻-,, Γ T)) γt = ctx≈-refl (◄ Γ ,, T)
