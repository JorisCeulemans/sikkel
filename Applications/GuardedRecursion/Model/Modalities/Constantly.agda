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
    ≡˘⟨ cong (T ⟪ tt , ctx-id Γ ⟫_) (Tm.naturality t z≤n refl) ⟩
      T ⟪ tt , ctx-id Γ ⟫ T ⟪ tt , _ ⟫ (t ⟨ n , γ ⟩')
    ≡⟨ ty-cong-2-1 T refl ⟩
      T ⟪ tt , _ ⟫ (t ⟨ n , γ ⟩')
    ≡⟨ Tm.naturality t ≤-refl (ctx-id Γ) ⟩
      t ⟨ n , γ ⟩' ∎
    where open ≡-Reasoning

  constantly-ty-β : (t : Tm (now Γ) T) → unconstantly-tm (constantly-tm t) ≅ᵗᵐ t
  eq (constantly-ty-β t) γ = Tm.naturality t tt _

constantly-ty-cong : {T : Ty (now Γ)} {S : Ty (now Γ)} → T ≅ᵗʸ S → constantly-ty T ≅ᵗʸ constantly-ty S
func (from (constantly-ty-cong T=S)) = func (from T=S)
_↣_.naturality (from (constantly-ty-cong T=S)) = _↣_.naturality (from T=S)
func (to (constantly-ty-cong T=S)) = func (to T=S)
_↣_.naturality (to (constantly-ty-cong T=S)) = _↣_.naturality (to T=S)
eq (isoˡ (constantly-ty-cong T=S)) = eq (isoˡ T=S)
eq (isoʳ (constantly-ty-cong T=S)) = eq (isoʳ T=S)

constantly-ty-cong-refl : {T : Ty (now Γ)} → constantly-ty-cong (reflᵗʸ {T = T}) ≅ᵉ reflᵗʸ
eq (from-eq constantly-ty-cong-refl) _ = refl

constantly-ty-cong-sym : {T S : Ty (now Γ)} {e : T ≅ᵗʸ S} → constantly-ty-cong (symᵗʸ e) ≅ᵉ symᵗʸ (constantly-ty-cong e)
eq (from-eq constantly-ty-cong-sym) _ = refl

constantly-ty-cong-trans : {R S T : Ty (now Γ)} {e1 : R ≅ᵗʸ S} {e2 : S ≅ᵗʸ T} → constantly-ty-cong (transᵗʸ e1 e2) ≅ᵉ transᵗʸ (constantly-ty-cong e1) (constantly-ty-cong e2)
eq (from-eq constantly-ty-cong-trans) _ = refl

constantly-ty-cong-cong : {T S : Ty (now Γ)} {e e' : T ≅ᵗʸ S} → e ≅ᵉ e' → constantly-ty-cong e ≅ᵉ constantly-ty-cong e'
eq (from-eq (constantly-ty-cong-cong 𝑒)) t = eq (from-eq 𝑒) t

module _ {T : Ty (now Γ)} where
  constantly-tm-cong : {t s : Tm (now Γ) T} → t ≅ᵗᵐ s → constantly-tm t ≅ᵗᵐ constantly-tm s
  eq (constantly-tm-cong t=s) γ = eq t=s (Γ ⟪ z≤n ⟫ γ)

  unconstantly-tm-cong : {t s : Tm Γ (constantly-ty T)} → t ≅ᵗᵐ s → unconstantly-tm t ≅ᵗᵐ unconstantly-tm s
  eq (unconstantly-tm-cong t=s) γ = cong (T ⟪ tt , _ ⟫_) (eq t=s γ)

module _ {T S : Ty (now Γ)} where
  constantly-tm-ι : {T=S : T ≅ᵗʸ S} (s : Tm (now Γ) S) →
                    ι[ constantly-ty-cong T=S ] constantly-tm s ≅ᵗᵐ constantly-tm (ι[ T=S ] s)
  eq (constantly-tm-ι s) _ = refl

  unconstantly-tm-ι : {T=S : T ≅ᵗʸ S} (s : Tm Γ (constantly-ty S)) →
                      ι[ T=S ] unconstantly-tm s ≅ᵗᵐ unconstantly-tm (ι[ constantly-ty-cong T=S ] s)
  eq (unconstantly-tm-ι {T=S = T=S} s) γ = sym (_↣_.naturality (to T=S))

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

constantly-ty-natural-ty-eq : (σ : Γ ⇒ Δ) {T S : Ty (now Δ)} (e : T ≅ᵗʸ S) →
  transᵗʸ (constantly-ty-natural σ) (constantly-ty-cong (ty-subst-cong-ty (now-subst σ) e))
    ≅ᵉ
  transᵗʸ (ty-subst-cong-ty σ (constantly-ty-cong e)) (constantly-ty-natural σ)
eq (from-eq (constantly-ty-natural-ty-eq σ e)) _ = sym (_↣_.naturality (from e))

constantly-ty-natural-id : {T : Ty (now Γ)} →
  transᵗʸ (constantly-ty-natural (id-subst Γ)) (constantly-ty-cong (transᵗʸ (ty-subst-cong-subst now-subst-id T) (ty-subst-id T)))
    ≅ᵉ
  ty-subst-id (constantly-ty T)
eq (from-eq (constantly-ty-natural-id {T = T})) _ = trans (ty-id T) (ty-id T)

constantly-ty-natural-⊚ : (τ : Δ ⇒ Θ) (σ : Γ ⇒ Δ) {T : Ty (now Θ)} →
  transᵗʸ (ty-subst-cong-ty σ (constantly-ty-natural τ))
          (transᵗʸ (constantly-ty-natural σ)
                   (constantly-ty-cong (ty-subst-comp T (now-subst τ) (now-subst σ))))
    ≅ᵉ
  transᵗʸ (ty-subst-comp (constantly-ty T) τ σ)
          (transᵗʸ (constantly-ty-natural (τ ⊚ σ))
                   (constantly-ty-cong (ty-subst-cong-subst (now-subst-⊚ τ σ) T)))
eq (from-eq (constantly-ty-natural-⊚ τ σ {T})) _ = ty-cong-2-2 T refl

constantly-ty-natural-subst-eq : {σ τ : Γ ⇒ Δ} {T : Ty (now Δ)} (ε : σ ≅ˢ τ) →
  transᵗʸ (ty-subst-cong-subst ε (constantly-ty T)) (constantly-ty-natural τ)
    ≅ᵉ
  transᵗʸ (constantly-ty-natural σ) (constantly-ty-cong (ty-subst-cong-subst (now-subst-cong ε) T))
eq (from-eq (constantly-ty-natural-subst-eq {T = T} _)) _ = ty-cong-2-2 T refl

{-
instance
  constantly-closed : {A : ClosedTy ★} {{_ : IsClosedNatural A}} → IsClosedNatural (constantly-ty A)
  closed-natural {{constantly-closed}} σ = transᵗʸ (constantly-ty-natural σ) (constantly-ty-cong (closed-natural (now-subst σ)))
-}

module _ (σ : Δ ⇒ Γ) {T : Ty (now Γ)} where
  constantly-tm-natural : (t : Tm (now Γ) T) →
                        (constantly-tm t) [ σ ]' ≅ᵗᵐ ι[ constantly-ty-natural σ ] constantly-tm (t [ now-subst σ ]')
  eq (constantly-tm-natural t) δ = sym (Tm.naturality t tt _)

  unconstantly-tm-natural : (t : Tm Γ (constantly-ty T)) →
                          (unconstantly-tm t) [ now-subst σ ]' ≅ᵗᵐ unconstantly-tm (ι⁻¹[ constantly-ty-natural σ ] (t [ σ ]'))
  eq (unconstantly-tm-natural t) δ = sym (ty-cong-2-1 T refl)

-- A modal version of the eliminator for booleans for the constantly modality.
constantly-if'_then'_else'_ : {T : Ty Γ} → Tm Γ (constantly-ty Bool') → Tm Γ T → Tm Γ T → Tm Γ T
constantly-if' c then' t else' f ⟨ n , γ ⟩' = if c ⟨ n , γ ⟩' then t ⟨ n , γ ⟩' else f ⟨ n , γ ⟩'
Tm.naturality (constantly-if'_then'_else'_ c t f) {m} {n} {γ} {γ'} m≤n eγ with c ⟨ m , γ' ⟩' | c ⟨ n , γ ⟩' | Tm.naturality c m≤n eγ
Tm.naturality (constantly-if'_then'_else'_ c t f) {m} {n} {γ} {γ'} m≤n eγ | false | .false | refl = Tm.naturality f m≤n eγ
Tm.naturality (constantly-if'_then'_else'_ c t f) {m} {n} {γ} {γ'} m≤n eγ | true  | .true  | refl = Tm.naturality t m≤n eγ
