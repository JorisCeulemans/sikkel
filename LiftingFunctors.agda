module LiftingFunctors where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product renaming (_,_ to [_,_])
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension

record ω-Functor : Set where
  constructor MkωFunctor
  field
    _∙_ : ℕ → ℕ
    monotone : {m n : ℕ} → m ≤ n → _∙_ m ≤ _∙_ n

  monotone-id : monotone (≤-refl {n}) ≡ ≤-refl {_∙_ n}
  monotone-id = ≤-irrelevant (monotone ≤-refl) ≤-refl

  monotone-comp : (k≤m : k ≤ m) (m≤n : m ≤ n) →
                  monotone (≤-trans k≤m m≤n) ≡ ≤-trans (monotone k≤m) (monotone m≤n)
  monotone-comp k≤m m≤n = ≤-irrelevant _ _
open ω-Functor

-- We now show that an endofunctor on ω can be lifted to a
-- strict CwF endomorphism on Psh(ω).
module LiftedFunctor (F : ω-Functor) where
  ctx-lift : Ctx ℓ → Ctx ℓ
  set (ctx-lift Γ) n = Γ ⟨ F ∙ n ⟩
  rel (ctx-lift Γ) m≤n = Γ ⟪ monotone F m≤n ⟫
  rel-id (ctx-lift Γ) γ = trans (cong (λ x → Γ ⟪ x ⟫ γ) (monotone-id F)) (rel-id Γ γ)
  rel-comp (ctx-lift Γ) k≤m m≤n γ = trans (cong (λ x → Γ ⟪ x ⟫ γ) (monotone-comp F k≤m m≤n)) (rel-comp Γ (monotone F k≤m) (monotone F m≤n) γ)

  subst-lift : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) → ctx-lift Δ ⇒ ctx-lift Γ
  func (subst-lift σ) {n} = func σ {F ∙ n}
  naturality (subst-lift σ) {m≤n = m≤n} δ = naturality σ {m≤n = monotone F m≤n} δ

  subst-lift-id : {Γ : Ctx ℓ} → subst-lift (id-subst Γ) ≅ˢ id-subst (ctx-lift Γ)
  subst-lift-id = ≅ˢ-refl

  subst-lift-comp : {Δ Γ Θ : Ctx ℓ} (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                    subst-lift (τ ⊚ σ) ≅ˢ subst-lift τ ⊚ subst-lift σ
  subst-lift-comp τ σ = ≅ˢ-refl

  ty-lift : {Γ : Ctx ℓ} → Ty Γ → Ty (ctx-lift Γ)
  type (ty-lift T) n γ = T ⟨ F ∙ n , γ ⟩
  morph (ty-lift T) m≤n eγ t = T ⟪ monotone F m≤n , eγ ⟫ t
  morph-id (ty-lift T) t = trans (morph-cong T (monotone-id F) _ _)
                                 (morph-id T t)
  morph-comp (ty-lift {Γ = Γ} T) k≤m m≤n eq-nm eq-mk t =
    trans (morph-cong T (monotone-comp F k≤m m≤n) _ _)
          (morph-comp T (monotone F k≤m) (monotone F m≤n) eq-nm eq-mk t)

  ty-lift-natural : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) (T : Ty Γ) →
                    ty-lift (T [ σ ]) ≅ᵗʸ ty-lift T [ subst-lift σ ]
  from (ty-lift-natural σ T) = record { func = id ; naturality = λ _ → refl }
  to (ty-lift-natural σ T) = record { func = id ; naturality = λ _ → refl }
  eq (isoˡ (ty-lift-natural σ T)) _ = refl
  eq (isoʳ (ty-lift-natural σ T)) _ = refl

  tm-lift : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → Tm (ctx-lift Γ) (ty-lift T)
  term (tm-lift t) n γ = t ⟨ F ∙ n , γ ⟩'
  naturality (tm-lift t) m≤n eγ = naturality t (monotone F m≤n) eγ

  tm-lift-natural : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) {T : Ty Γ} (t : Tm Γ T) →
                    tm-lift (t [ σ ]') ≅ᵗᵐ ι[ ty-lift-natural σ T ] ((tm-lift t) [ subst-lift σ ]')
  eq (tm-lift-natural σ t) δ = refl

  lift-◇ : ctx-lift {ℓ} ◇ ≅ᶜ ◇
  from lift-◇ = MkSubst id (λ _ → refl)
  to lift-◇ = MkSubst id (λ _ → refl)
  eq (isoˡ lift-◇) _ = refl
  eq (isoʳ lift-◇) _ = refl

  lift-ctx-ext : (Γ : Ctx ℓ) (T : Ty Γ) → ctx-lift (Γ ,, T) ≅ᶜ ctx-lift Γ ,, ty-lift T
  from (lift-ctx-ext Γ T) = MkSubst id (λ _ → refl)
  to (lift-ctx-ext Γ T) = MkSubst id (λ _ → refl)
  eq (isoˡ (lift-ctx-ext Γ T)) _ = refl
  eq (isoʳ (lift-ctx-ext Γ T)) _ = refl

  lift-π : (Γ : Ctx ℓ) (T : Ty Γ) → subst-lift (π {T = T}) ⊚ to (lift-ctx-ext Γ T) ≅ˢ π
  eq (lift-π Γ T) _ = refl

  lift-ξ : (Γ : Ctx ℓ) (T : Ty Γ) → tm-lift (ξ {T = T}) [ to (lift-ctx-ext Γ T) ]' ≅ᵗᵐ
                                     ι[ ty-subst-cong-ty (to (lift-ctx-ext Γ T)) (ty-lift-natural π T) ] (
                                     ι[ ty-subst-comp (ty-lift T) (subst-lift (π {T = T})) (to (lift-ctx-ext Γ T)) ] (
                                     ι[ ty-subst-cong-subst (lift-π Γ T) (ty-lift T) ] ξ))
  eq (lift-ξ Γ T) [ γ , t ] = sym (
    begin
      T ⟪ monotone F ≤-refl , _ ⟫ t
    ≡⟨ morph-cong T (monotone-id F) _ _ ⟩
      T ⟪ ≤-refl , _ ⟫ t
    ≡⟨ morph-id T t ⟩
      t ∎)
    where open ≡-Reasoning
