--------------------------------------------------
-- The now-timeless dependent adjunction
--------------------------------------------------

module Applications.GuardedRecursion.Model.Modalities.Timeless where

open import Data.Bool
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Type.Discrete

private
  variable
    Δ Γ Θ : Ctx ω


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

instance
  now-is-functor : IsCtxFunctor now
  ctx-map {{now-is-functor}} = now-subst
  ctx-map-cong {{now-is-functor}} = now-subst-cong
  ctx-map-id {{now-is-functor}} = now-subst-id
  ctx-map-⊚ {{now-is-functor}} = now-subst-⊚

timeless-ty : Ty (now Γ) → Ty Γ
timeless-ty {Γ = Γ} T ⟨ n , γ ⟩ = T ⟨ tt , Γ ⟪ z≤n ⟫ γ ⟩
_⟪_,_⟫_ (timeless-ty {Γ = Γ} T) m≤n {γy = γn}{γx = γm} eγ = T ⟪ tt , proof ⟫_
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
ty-cong (timeless-ty T) e = ty-cong T refl
ty-id (timeless-ty T) = strong-ty-id T
ty-comp (timeless-ty T) = strong-ty-comp T

module _ {T : Ty (now Γ)} where
  timeless-tm : Tm (now Γ) T → Tm Γ (timeless-ty T)
  timeless-tm t ⟨ n , γ ⟩' = t ⟨ tt , Γ ⟪ z≤n ⟫ γ ⟩'
  Tm.naturality (timeless-tm t) _ _ = Tm.naturality t tt _

  untimeless-tm : Tm Γ (timeless-ty T) → Tm (now Γ) T
  untimeless-tm t ⟨ _ , γ ⟩' = ty-ctx-subst T (ctx-id Γ) (t ⟨ 0 , γ ⟩')
  Tm.naturality (untimeless-tm t) tt refl = ty-id T

  timeless-ty-η : (t : Tm Γ (timeless-ty T)) → timeless-tm (untimeless-tm t) ≅ᵗᵐ t
  eq (timeless-ty-η t) {n} γ =
    begin
      T ⟪ tt , ctx-id Γ ⟫ (t ⟨ 0 , Γ ⟪ z≤n ⟫ γ ⟩')
    ≡˘⟨ cong (T ⟪ tt , ctx-id Γ ⟫_) (Tm.naturality t z≤n refl) ⟩
      T ⟪ tt , ctx-id Γ ⟫ T ⟪ tt , _ ⟫ (t ⟨ n , γ ⟩')
    ≡⟨ ty-cong-2-1 T refl ⟩
      T ⟪ tt , _ ⟫ (t ⟨ n , γ ⟩')
    ≡⟨ Tm.naturality t ≤-refl (ctx-id Γ) ⟩
      t ⟨ n , γ ⟩' ∎
    where open ≡-Reasoning

  timeless-ty-β : (t : Tm (now Γ) T) → untimeless-tm (timeless-tm t) ≅ᵗᵐ t
  eq (timeless-ty-β t) γ = Tm.naturality t tt _

timeless-ty-cong : {T : Ty (now Γ)} {S : Ty (now Γ)} → T ≅ᵗʸ S → timeless-ty T ≅ᵗʸ timeless-ty S
func (from (timeless-ty-cong T=S)) = func (from T=S)
_↣_.naturality (from (timeless-ty-cong T=S)) = _↣_.naturality (from T=S)
func (to (timeless-ty-cong T=S)) = func (to T=S)
_↣_.naturality (to (timeless-ty-cong T=S)) = _↣_.naturality (to T=S)
eq (isoˡ (timeless-ty-cong T=S)) = eq (isoˡ T=S)
eq (isoʳ (timeless-ty-cong T=S)) = eq (isoʳ T=S)

module _ {T : Ty (now Γ)} where
  timeless-tm-cong : {t s : Tm (now Γ) T} → t ≅ᵗᵐ s → timeless-tm t ≅ᵗᵐ timeless-tm s
  eq (timeless-tm-cong t=s) γ = eq t=s (Γ ⟪ z≤n ⟫ γ)

  untimeless-tm-cong : {t s : Tm Γ (timeless-ty T)} → t ≅ᵗᵐ s → untimeless-tm t ≅ᵗᵐ untimeless-tm s
  eq (untimeless-tm-cong t=s) γ = cong (T ⟪ tt , _ ⟫_) (eq t=s γ)

module _ {T S : Ty (now Γ)} where
  timeless-tm-ι : (T=S : T ≅ᵗʸ S) (s : Tm (now Γ) S) → ι[ timeless-ty-cong T=S ] timeless-tm s ≅ᵗᵐ timeless-tm (ι[ T=S ] s)
  eq (timeless-tm-ι T=S s) _ = refl

  untimeless-tm-ι : (T=S : T ≅ᵗʸ S) (s : Tm Γ (timeless-ty S)) → ι[ T=S ] untimeless-tm s ≅ᵗᵐ untimeless-tm (ι[ timeless-ty-cong T=S ] s)
  eq (untimeless-tm-ι T=S s) γ = sym (_↣_.naturality (to T=S))

timeless-ty-natural : (σ : Δ ⇒ Γ) {T : Ty (now Γ)} → (timeless-ty T) [ σ ] ≅ᵗʸ timeless-ty (T [ now-subst σ ])
func (from (timeless-ty-natural σ {T})) = ty-ctx-subst T (_⇒_.naturality σ)
_↣_.naturality (from (timeless-ty-natural σ {T})) = ty-cong-2-2 T refl
func (to (timeless-ty-natural σ {T})) = ty-ctx-subst T (sym (_⇒_.naturality σ))
_↣_.naturality (to (timeless-ty-natural σ {T})) = ty-cong-2-2 T refl
eq (isoˡ (timeless-ty-natural σ {T})) t =
  begin
    T ⟪ tt , _ ⟫ (T ⟪ tt , _ ⟫ t)
  ≡⟨ ty-cong-2-1 T refl ⟩
    T ⟪ tt , refl ⟫ t
  ≡⟨ ty-id T ⟩
    t ∎
  where open ≡-Reasoning
eq (isoʳ (timeless-ty-natural σ {T})) t =
  begin
    T ⟪ tt , _ ⟫ (T ⟪ tt , _ ⟫ t)
  ≡⟨ ty-cong-2-1 T refl ⟩
    T ⟪ tt , refl ⟫ t
  ≡⟨ ty-id T ⟩
    t ∎
  where open ≡-Reasoning

instance
  timeless-closed : {A : ClosedTy ★} {{_ : IsClosedNatural A}} → IsClosedNatural (timeless-ty A)
  closed-natural {{timeless-closed}} σ = ≅ᵗʸ-trans (timeless-ty-natural σ) (timeless-ty-cong (closed-natural (now-subst σ)))

module _ (σ : Δ ⇒ Γ) {T : Ty (now Γ)} where
  timeless-tm-natural : (t : Tm (now Γ) T) →
                        (timeless-tm t) [ σ ]' ≅ᵗᵐ ι[ timeless-ty-natural σ ] timeless-tm (t [ now-subst σ ]')
  eq (timeless-tm-natural t) δ = sym (Tm.naturality t tt _)

  untimeless-tm-natural : (t : Tm Γ (timeless-ty T)) →
                          (untimeless-tm t) [ now-subst σ ]' ≅ᵗᵐ untimeless-tm (ι⁻¹[ timeless-ty-natural σ ] (t [ σ ]'))
  eq (untimeless-tm-natural t) δ = sym (ty-cong-2-1 T refl)

-- A modal version of the eliminator for booleans for the timeless modality.
timeless-if'_then'_else'_ : {T : Ty Γ} → Tm Γ (timeless-ty Bool') → Tm Γ T → Tm Γ T → Tm Γ T
timeless-if' c then' t else' f ⟨ n , γ ⟩' = if c ⟨ n , γ ⟩' then t ⟨ n , γ ⟩' else f ⟨ n , γ ⟩'
Tm.naturality (timeless-if'_then'_else'_ c t f) {m} {n} {γ} {γ'} m≤n eγ with c ⟨ m , γ' ⟩' | c ⟨ n , γ ⟩' | Tm.naturality c m≤n eγ
Tm.naturality (timeless-if'_then'_else'_ c t f) {m} {n} {γ} {γ'} m≤n eγ | false | .false | refl = Tm.naturality f m≤n eγ
Tm.naturality (timeless-if'_then'_else'_ c t f) {m} {n} {γ} {γ'} m≤n eγ | true  | .true  | refl = Tm.naturality t m≤n eγ
