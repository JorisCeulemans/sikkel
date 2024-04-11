--------------------------------------------------
-- The now-constantly dependent adjunction
--------------------------------------------------

module Applications.GuardedRecursion.Model.Modalities.Constantly where

open import Data.Bool
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Type.Constant
open import Model.DRA

private
  variable
    Δ Γ Θ : Ctx ω


--------------------------------------------------
-- The "now" functor

now : Ctx ω → Ctx ★
now Γ ⟨ _ ⟩ = Γ ⟨ 0 ⟩
now Γ ⟪ _ ⟫ γ = γ
ctx-id (now Γ) = refl
ctx-comp (now Γ) = refl

now-subst : Δ ⇒ Γ → now Δ ⇒ now Γ
func (now-subst σ) = func σ
_⇒_.naturality (now-subst σ) = refl

now-subst-cong : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → now-subst σ ≅ˢ now-subst τ
eq (now-subst-cong σ=τ) δ = eq σ=τ δ

now-subst-id : now-subst (id-subst Γ) ≅ˢ id-subst (now Γ)
eq now-subst-id _ = refl

now-subst-⊚ : (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) → now-subst (σ ⊚ τ) ≅ˢ now-subst σ ⊚ now-subst τ
eq (now-subst-⊚ σ τ) _ = refl


--------------------------------------------------
-- The constantly type constructor and related term formers

constantly-ty : Ty (now Γ) → Ty Γ
constantly-ty {Γ = Γ} T ⟨ n , γ ⟩ = T ⟨ tt , Γ ⟪ z≤n ⟫ γ ⟩
_⟪_,_⟫_ (constantly-ty {Γ = Γ} T) m≤n {γy = γn}{γx = γm} eγ = T ⟪ tt , proof ⟫_
  where
    open ≡-Reasoning
    proof : Γ ⟪ z≤n ⟫ γn ≡ Γ ⟪ z≤n ⟫ γm
    proof =
      begin
        Γ ⟪ z≤n ⟫ γn
      ≡⟨⟩
        Γ ⟪ ≤-trans z≤n m≤n ⟫ γn
      ≡⟨ ctx-comp Γ ⟩
        Γ ⟪ z≤n ⟫ (Γ ⟪ m≤n ⟫ γn)
      ≡⟨ cong (Γ ⟪ z≤n ⟫_) eγ ⟩
        Γ ⟪ z≤n ⟫ γm ∎
ty-cong (constantly-ty T) e = ty-cong T refl
ty-id (constantly-ty T) = strong-ty-id T
ty-comp (constantly-ty T) = strong-ty-comp T

module _ {T : Ty (now Γ)} where
  constantly-tm : Tm (now Γ) T → Tm Γ (constantly-ty T)
  constantly-tm t ⟨ n , γ ⟩' = t ⟨ tt , Γ ⟪ z≤n ⟫ γ ⟩'
  Tm.naturality (constantly-tm t) _ _ = Tm.naturality t tt _

  unconstantly-tm : Tm Γ (constantly-ty T) → Tm (now Γ) T
  unconstantly-tm t ⟨ _ , γ ⟩' = ty-ctx-subst T (ctx-id Γ) (t ⟨ 0 , γ ⟩')
  Tm.naturality (unconstantly-tm t) tt refl = ty-id T

  constantly-ty-η : (t : Tm Γ (constantly-ty T)) → constantly-tm (unconstantly-tm t) ≅ᵗᵐ t
  eq (constantly-ty-η t) {n} γ =
    begin
      T ⟪ tt , ctx-id Γ ⟫ (t ⟨ 0 , Γ ⟪ z≤n ⟫ γ ⟩')
    ≡⟨ cong (T ⟪ tt , ctx-id Γ ⟫_) (Tm.naturality t z≤n refl) ⟨
      T ⟪ tt , ctx-id Γ ⟫ T ⟪ tt , _ ⟫ (t ⟨ n , γ ⟩')
    ≡⟨ ty-cong-2-1 T refl ⟩
      T ⟪ tt , _ ⟫ (t ⟨ n , γ ⟩')
    ≡⟨ Tm.naturality t ≤-refl (ctx-id Γ) ⟩
      t ⟨ n , γ ⟩' ∎
    where open ≡-Reasoning

  constantly-ty-β : (t : Tm (now Γ) T) → unconstantly-tm (constantly-tm t) ≅ᵗᵐ t
  eq (constantly-ty-β t) γ = Tm.naturality t tt _


--------------------------------------------------
-- Functoriality of constantly-ty

constantly-ty-map : {T S : Ty (now Γ)} → (T ↣ S) → constantly-ty T ↣ constantly-ty S
func (constantly-ty-map η) = func η
_↣_.naturality (constantly-ty-map η) = _↣_.naturality η

constantly-ty-map-cong : {T S : Ty (now Γ)} {η φ : T ↣ S} → η ≅ⁿ φ → constantly-ty-map η ≅ⁿ constantly-ty-map φ
eq (constantly-ty-map-cong 𝔢) t = eq 𝔢 t

constantly-ty-map-id : {T : Ty (now Γ)} → constantly-ty-map (id-trans T) ≅ⁿ id-trans (constantly-ty T)
eq constantly-ty-map-id _ = refl

constantly-ty-map-⊙ : {R S T : Ty (now Γ)} {η : R ↣ S} {φ : S ↣ T} →
                      constantly-ty-map (φ ⊙ η) ≅ⁿ constantly-ty-map φ ⊙ constantly-ty-map η
eq constantly-ty-map-⊙ _ = refl

module _ {T : Ty (now Γ)} where
  constantly-tm-cong : {t s : Tm (now Γ) T} → t ≅ᵗᵐ s → constantly-tm t ≅ᵗᵐ constantly-tm s
  eq (constantly-tm-cong t=s) γ = eq t=s (Γ ⟪ z≤n ⟫ γ)

  unconstantly-tm-cong : {t s : Tm Γ (constantly-ty T)} → t ≅ᵗᵐ s → unconstantly-tm t ≅ᵗᵐ unconstantly-tm s
  eq (unconstantly-tm-cong t=s) γ = cong (T ⟪ tt , _ ⟫_) (eq t=s γ)


module _ {T S : Ty (now Γ)} where
  constantly-tm-convert : {φ : T ↣ S} (t : Tm (now Γ) T) →
                          convert-tm (constantly-ty-map φ) (constantly-tm t) ≅ᵗᵐ constantly-tm (convert-tm φ t)
  eq (constantly-tm-convert t) _ = refl


--------------------------------------------------
-- Naturality of constantly-ty

constantly-ty-natural : (σ : Δ ⇒ Γ) {T : Ty (now Γ)} → (constantly-ty T) [ σ ] ≅ᵗʸ constantly-ty (T [ now-subst σ ])
func (from (constantly-ty-natural σ {T})) = ty-ctx-subst T (_⇒_.naturality σ)
_↣_.naturality (from (constantly-ty-natural σ {T})) = ty-cong-2-2 T refl
func (to (constantly-ty-natural σ {T})) = ty-ctx-subst T (sym (_⇒_.naturality σ))
_↣_.naturality (to (constantly-ty-natural σ {T})) = ty-cong-2-2 T refl
eq (isoˡ (constantly-ty-natural σ {T})) t =
  begin
    T ⟪ tt , _ ⟫ (T ⟪ tt , _ ⟫ t)
  ≡⟨ ty-cong-2-1 T refl ⟩
    T ⟪ tt , refl ⟫ t
  ≡⟨ ty-id T ⟩
    t ∎
  where open ≡-Reasoning
eq (isoʳ (constantly-ty-natural σ {T})) t =
  begin
    T ⟪ tt , _ ⟫ (T ⟪ tt , _ ⟫ t)
  ≡⟨ ty-cong-2-1 T refl ⟩
    T ⟪ tt , refl ⟫ t
  ≡⟨ ty-id T ⟩
    t ∎
  where open ≡-Reasoning

constantly-ty-natural-map : (σ : Γ ⇒ Δ) {T S : Ty (now Δ)} (φ : T ↣ S) →
  constantly-ty-map (ty-subst-map (now-subst σ) φ) ⊙ from (constantly-ty-natural σ)
    ≅ⁿ
  from (constantly-ty-natural σ) ⊙ ty-subst-map σ (constantly-ty-map φ)
eq (constantly-ty-natural-map σ φ) _ = sym (_↣_.naturality φ)

constantly-ty-natural-id-map : {T : Ty (now Γ)} →
  constantly-ty-map (ty-subst-id-from T ⊙ ty-subst-eq-subst-morph now-subst-id T) ⊙ from (constantly-ty-natural (id-subst Γ))
    ≅ⁿ
  ty-subst-id-from (constantly-ty T)
eq (constantly-ty-natural-id-map {T = T}) _ = trans (ty-id T) (ty-id T)

constantly-ty-natural-⊚-map : (τ : Δ ⇒ Θ) (σ : Γ ⇒ Δ) {T : Ty (now Θ)} →
  constantly-ty-map (ty-subst-comp-from T (now-subst τ) (now-subst σ))
  ⊙ from (constantly-ty-natural σ)
  ⊙ ty-subst-map σ (from (constantly-ty-natural τ))
    ≅ⁿ
  constantly-ty-map (ty-subst-eq-subst-morph (now-subst-⊚ τ σ) T)
  ⊙ from (constantly-ty-natural (τ ⊚ σ))
  ⊙ ty-subst-comp-from (constantly-ty T) τ σ
eq (constantly-ty-natural-⊚-map τ σ {T}) _ = ty-cong-2-2 T refl

constantly-ty-natural-subst-eq-map : {σ τ : Γ ⇒ Δ} {T : Ty (now Δ)} (ε : σ ≅ˢ τ) →
  from (constantly-ty-natural τ) ⊙ ty-subst-eq-subst-morph ε (constantly-ty T)
    ≅ⁿ
  constantly-ty-map (ty-subst-eq-subst-morph (now-subst-cong ε) T) ⊙ from (constantly-ty-natural σ)
eq (constantly-ty-natural-subst-eq-map {T = T} _) _ = ty-cong-2-2 T refl

module _ (σ : Δ ⇒ Γ) {T : Ty (now Γ)} where
  constantly-tm-natural : (t : Tm (now Γ) T) →
                          (constantly-tm t) [ σ ]' ≅ᵗᵐ ι[ constantly-ty-natural σ ] constantly-tm (t [ now-subst σ ]')
  eq (constantly-tm-natural t) δ = sym (Tm.naturality t tt _)

  unconstantly-tm-natural : (t : Tm Γ (constantly-ty T)) →
                            (unconstantly-tm t) [ now-subst σ ]' ≅ᵗᵐ unconstantly-tm (ι⁻¹[ constantly-ty-natural σ ] (t [ σ ]'))
  eq (unconstantly-tm-natural t) δ = sym (ty-cong-2-1 T refl)


--------------------------------------------------
-- Constantly as a DRA

instance
  now-is-functor : IsCtxFunctor now
  ctx-map {{now-is-functor}} = now-subst
  ctx-map-cong {{now-is-functor}} = now-subst-cong
  ctx-map-id {{now-is-functor}} = now-subst-id
  ctx-map-⊚ {{now-is-functor}} = now-subst-⊚

now-functor : CtxFunctor ω ★
ctx-op now-functor = now
is-functor now-functor = now-is-functor

constantly : DRA ★ ω
ctx-functor constantly = now-functor
⟨_∣_⟩ constantly = constantly-ty
dra-map constantly = constantly-ty-map
dra-map-cong constantly = constantly-ty-map-cong
dra-map-id constantly = constantly-ty-map-id
dra-map-⊙ constantly = constantly-ty-map-⊙
dra-natural constantly = constantly-ty-natural
dra-natural-map constantly = constantly-ty-natural-map
dra-natural-id-map constantly = constantly-ty-natural-id-map
dra-natural-⊚-map constantly = constantly-ty-natural-⊚-map
dra-natural-subst-eq-map constantly = constantly-ty-natural-subst-eq-map
dra-intro constantly = constantly-tm
dra-intro-cong constantly = constantly-tm-cong
dra-intro-natural constantly = constantly-tm-natural
dra-intro-convert constantly = constantly-tm-convert
dra-elim constantly = unconstantly-tm
dra-elim-cong constantly = unconstantly-tm-cong
dra-β constantly = constantly-ty-β
dra-η constantly = constantly-ty-η

constantly-ty-cong : {T : Ty (now Γ)} {S : Ty (now Γ)} → T ≅ᵗʸ S → constantly-ty T ≅ᵗʸ constantly-ty S
constantly-ty-cong e = dra-cong constantly e

module _ {T S : Ty (now Γ)} where
  constantly-tm-ι : {T=S : T ≅ᵗʸ S} (s : Tm (now Γ) S) →
                    ι[ constantly-ty-cong T=S ] constantly-tm s ≅ᵗᵐ constantly-tm (ι[ T=S ] s)
  constantly-tm-ι s = dra-intro-ι constantly s

  unconstantly-tm-ι : {T=S : T ≅ᵗʸ S} (s : Tm Γ (constantly-ty S)) →
                      ι[ T=S ] unconstantly-tm s ≅ᵗᵐ unconstantly-tm (ι[ constantly-ty-cong T=S ] s)
  unconstantly-tm-ι s = dra-elim-ι constantly s


--------------------------------------------------
-- A modal version of the eliminator for booleans for the constantly modality

constantly-if'_then'_else'_ : {T : Ty Γ} → Tm Γ (constantly-ty Bool') → Tm Γ T → Tm Γ T → Tm Γ T
constantly-if' c then' t else' f ⟨ n , γ ⟩' = if c ⟨ n , γ ⟩' then t ⟨ n , γ ⟩' else f ⟨ n , γ ⟩'
Tm.naturality (constantly-if'_then'_else'_ c t f) {m} {n} {γ} {γ'} m≤n eγ with c ⟨ m , γ' ⟩' | c ⟨ n , γ ⟩' | Tm.naturality c m≤n eγ
Tm.naturality (constantly-if'_then'_else'_ c t f) {m} {n} {γ} {γ'} m≤n eγ | false | .false | refl = Tm.naturality f m≤n eγ
Tm.naturality (constantly-if'_then'_else'_ c t f) {m} {n} {γ} {γ'} m≤n eγ | true  | .true  | refl = Tm.naturality t m≤n eγ
