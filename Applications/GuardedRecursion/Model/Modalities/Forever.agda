--------------------------------------------------
-- The constantly-forever dependent adjunction
--------------------------------------------------

module Applications.GuardedRecursion.Model.Modalities.Forever where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.BaseCategory
open import Model.CwF-Structure

private
  variable
    Δ Γ Θ : Ctx ★


constantly-ctx : Ctx ★ → Ctx ω
constantly-ctx Γ ⟨ _ ⟩ = Γ ⟨ tt ⟩
constantly-ctx Γ ⟪ _ ⟫ γ = γ
ctx-id (constantly-ctx Γ) = refl
ctx-comp (constantly-ctx Γ) = refl

constantly-subst : Δ ⇒ Γ → constantly-ctx Δ ⇒ constantly-ctx Γ
func (constantly-subst σ) = func σ
_⇒_.naturality (constantly-subst σ) = refl

constantly-subst-cong : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → constantly-subst σ ≅ˢ constantly-subst τ
eq (constantly-subst-cong σ=τ) δ = eq σ=τ δ

constantly-subst-id : constantly-subst (id-subst Γ) ≅ˢ id-subst (constantly-ctx Γ)
eq constantly-subst-id _ = refl

constantly-subst-⊚ : (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) → constantly-subst (σ ⊚ τ) ≅ˢ constantly-subst σ ⊚ constantly-subst τ
eq (constantly-subst-⊚ σ τ) _ = refl

instance
  constantly-ctx-is-functor : IsCtxFunctor constantly-ctx
  ctx-map {{constantly-ctx-is-functor}} = constantly-subst
  ctx-map-cong {{constantly-ctx-is-functor}} = constantly-subst-cong
  ctx-map-id {{constantly-ctx-is-functor}} = constantly-subst-id
  ctx-map-⊚ {{constantly-ctx-is-functor}} = constantly-subst-⊚

const-subst : Γ ⟨ tt ⟩ → ◇ ⇒ constantly-ctx Γ
func (const-subst γ) _ = γ
_⇒_.naturality (const-subst γ) = refl

const-subst-cong : {γ1 γ2 : Γ ⟨ tt ⟩} → γ1 ≡ γ2 → const-subst {Γ = Γ} γ1 ≅ˢ const-subst γ2
eq (const-subst-cong eγ) tt = eγ

const-subst-natural : (δ : Δ ⟨ tt ⟩) (σ : Δ ⇒ Γ) → constantly-subst σ ⊚ const-subst δ ≅ˢ const-subst (func σ δ)
eq (const-subst-natural δ σ) _ = refl

forever-ty : Ty (constantly-ctx Γ) → Ty Γ
forever-ty T ⟨ tt , γ ⟩ = Tm ◇ (T [ const-subst γ ])
_⟪_,_⟫_ (forever-ty {Γ = Γ} T) tt {γ}{γ'} eγ t = ι⁻¹[ proof ] t
  where
    proof : T [ const-subst γ ] ≅ᵗʸ T [ const-subst γ' ]
    proof = ty-subst-cong-subst (const-subst-cong (trans (sym (ctx-id Γ)) eγ)) T
ty-cong (forever-ty T) _ = tm-≅-to-≡ (record { eq = λ _ → ty-cong T refl })
ty-id (forever-ty T) = tm-≅-to-≡ (record { eq = λ _ → strong-ty-id T })
ty-comp (forever-ty T) = tm-≅-to-≡
  (record { eq = λ _ → trans (ty-cong T (≤-irrelevant _ _)) (ty-comp T) })

module _ {T : Ty (constantly-ctx Γ)} where
  forever-tm : Tm (constantly-ctx Γ) T → Tm Γ (forever-ty T)
  (forever-tm t ⟨ tt , γ ⟩') ⟨ n , tt ⟩' = t ⟨ n , γ ⟩'
  Tm.naturality (forever-tm t ⟨ tt , γ ⟩') f refl = Tm.naturality t f _
  Tm.naturality (forever-tm t) f eγ = tm-≅-to-≡ (record { eq = λ _ → Tm.naturality t ≤-refl _ })

  unforever-tm : Tm Γ (forever-ty T) → Tm (constantly-ctx Γ) T
  unforever-tm t ⟨ n , γ ⟩' = t ⟨ tt , γ ⟩' ⟨ n , tt ⟩'
  Tm.naturality (unforever-tm t) f refl = Tm.naturality (t ⟨ tt , _ ⟩') f refl

  forever-ty-β : (t : Tm (constantly-ctx Γ) T) → unforever-tm (forever-tm t) ≅ᵗᵐ t
  eq (forever-ty-β t) _ = refl

  forever-ty-η : (t : Tm Γ (forever-ty T)) → forever-tm (unforever-tm t) ≅ᵗᵐ t
  eq (forever-ty-η t) γ = tm-≅-to-≡ (record { eq = λ { tt → refl } })

forever-ty-cong : {T : Ty (constantly-ctx Γ)} {S : Ty (constantly-ctx Γ)} →
                  T ≅ᵗʸ S → forever-ty T ≅ᵗʸ forever-ty S
func (from (forever-ty-cong T=S)) = ι⁻¹[ ty-subst-cong-ty (const-subst _) T=S ]_
_↣_.naturality (from (forever-ty-cong T=S)) = tm-≅-to-≡ (record { eq = λ _ → _↣_.naturality (from T=S) })
func (to (forever-ty-cong T=S)) = ι[ ty-subst-cong-ty (const-subst _) T=S ]_
_↣_.naturality (to (forever-ty-cong T=S)) = tm-≅-to-≡ (record { eq = λ _ → _↣_.naturality (to T=S) })
eq (isoˡ (forever-ty-cong T=S)) _ = tm-≅-to-≡ (ι-symʳ (ty-subst-cong-ty (const-subst _) T=S) _)
eq (isoʳ (forever-ty-cong T=S)) _ = tm-≅-to-≡ (ι-symˡ (ty-subst-cong-ty (const-subst _) T=S) _)

module _ {T : Ty (constantly-ctx Γ)} where
  forever-tm-cong : {t s : Tm (constantly-ctx Γ) T} → t ≅ᵗᵐ s → forever-tm t ≅ᵗᵐ forever-tm s
  eq (forever-tm-cong t=s) γ = tm-≅-to-≡ (record { eq = λ _ → eq t=s γ })

  unforever-tm-cong : {t s : Tm Γ (forever-ty T)} → t ≅ᵗᵐ s → unforever-tm t ≅ᵗᵐ unforever-tm s
  eq (unforever-tm-cong t=s) γ = cong (λ - → - ⟨ _ , tt ⟩') (eq t=s γ)

module _ {T S : Ty (constantly-ctx Γ)} (T=S : T ≅ᵗʸ S) where
  forever-tm-ι : (s : Tm (constantly-ctx Γ) S) → ι[ forever-ty-cong T=S ] forever-tm s ≅ᵗᵐ forever-tm (ι[ T=S ] s)
  eq (forever-tm-ι s) γ = tm-≅-to-≡ (record { eq = λ _ → refl })

  unforever-tm-ι : (s : Tm Γ (forever-ty S)) → ι[ T=S ] unforever-tm s ≅ᵗᵐ unforever-tm (ι[ forever-ty-cong T=S ] s)
  eq (unforever-tm-ι s) _ = refl

ty-const-subst : (T : Ty (constantly-ctx Γ)) (σ : Δ ⇒ Γ) (δ : Δ ⟨ tt ⟩) →
                 (T [ constantly-subst σ ]) [ const-subst δ ] ≅ᵗʸ T [ const-subst (func σ δ) ]
ty-const-subst T σ δ = ≅ᵗʸ-trans (ty-subst-comp T (constantly-subst σ) (const-subst _))
                                 (ty-subst-cong-subst (const-subst-natural _ σ) T)

forever-ty-natural : (σ : Δ ⇒ Γ) {T : Ty (constantly-ctx Γ)} → (forever-ty T) [ σ ] ≅ᵗʸ forever-ty (T [ constantly-subst σ ])
func (from (forever-ty-natural σ {T})) = ι[ ty-const-subst T σ _ ]_
_↣_.naturality (from (forever-ty-natural σ {T})) = tm-≅-to-≡ (record { eq = λ _ → ty-cong-2-2 T refl })
func (to (forever-ty-natural σ {T})) = ι⁻¹[ ty-const-subst T σ _ ]_
_↣_.naturality (to (forever-ty-natural σ {T})) = tm-≅-to-≡ (record { eq = λ _ → ty-cong-2-2 T refl })
eq (isoˡ (forever-ty-natural σ {T})) t = tm-≅-to-≡ (ι-symˡ (ty-const-subst T σ _) t)
eq (isoʳ (forever-ty-natural σ {T})) t = tm-≅-to-≡ (ι-symʳ (ty-const-subst T σ _) t)

instance
  forever-closed : {A : ClosedTy ω} {{_ : IsClosedNatural A}} → IsClosedNatural (forever-ty A)
  closed-natural {{forever-closed}} σ = ≅ᵗʸ-trans (forever-ty-natural σ) (forever-ty-cong (closed-natural (constantly-subst σ)))

module _ (σ : Δ ⇒ Γ) {T : Ty (constantly-ctx Γ)} where
  forever-tm-natural : (t : Tm (constantly-ctx Γ) T) →
                       (forever-tm t) [ σ ]' ≅ᵗᵐ ι[ forever-ty-natural σ ] forever-tm (t [ constantly-subst σ ]')
  eq (forever-tm-natural t) _ = tm-≅-to-≡ (record { eq = λ _ → sym (ty-id T) })

  unforever-tm-natural : (t : Tm Γ (forever-ty T)) →
                         (unforever-tm t) [ constantly-subst σ ]' ≅ᵗᵐ unforever-tm (ι⁻¹[ forever-ty-natural σ ] (t [ σ ]'))
  eq (unforever-tm-natural t) _ = sym (ty-id T)
