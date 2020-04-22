module LiftingFunctors where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
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

  subst-lift-id : {Γ : Ctx ℓ} → subst-lift (id-subst Γ) ≡ id-subst (ctx-lift Γ)
  subst-lift-id = refl

  subst-lift-comp : {Δ Γ Θ : Ctx ℓ} (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                    subst-lift (τ ⊚ σ) ≡ subst-lift τ ⊚ subst-lift σ
  subst-lift-comp τ σ = refl

  ty-lift : {Γ : Ctx ℓ} → Ty Γ → Ty (ctx-lift Γ)
  type (ty-lift T) n γ = T ⟨ F ∙ n , γ ⟩
  morph (ty-lift T) m≤n eq t = T ⟪ monotone F m≤n , eq ⟫ t
  morph-id (ty-lift T) t = trans (morph-ineq-cong T (monotone-id F) _)
                                 (morph-id T t)
  morph-comp (ty-lift {Γ = Γ} T) k≤m m≤n eq-nm eq-mk t =
    trans (cong (λ x → T ⟪ _ , x ⟫ t) (trans-assoc (cong (λ x → Γ ⟪ x ⟫  _) (monotone-comp F _ _))))
          (trans (morph-ineq-cong T (monotone-comp F k≤m m≤n) _)
                 (morph-comp T (monotone F k≤m) (monotone F m≤n) eq-nm eq-mk t))

  ty-lift-natural : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) (T : Ty Γ) →
                    ty-lift (T [ σ ]) ≡ ty-lift T [ subst-lift σ ]
  ty-lift-natural σ T = cong₂-d (MkTy _ _)
                                (funextI (funextI (funext (λ _ → uip _ _))))
                                (funextI (funextI (funextI (funext λ _ → funext λ _ → funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _)))))))

  tm-lift : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → Tm (ctx-lift Γ) (ty-lift T)
  term (tm-lift t) n γ = t ⟨ F ∙ n , γ ⟩'
  naturality (tm-lift t) m≤n eq = t ⟪ monotone F m≤n , eq ⟫'

  tm-lift-natural : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) {T : Ty Γ} (t : Tm Γ T) →
                    subst (Tm (ctx-lift Δ)) (ty-lift-natural σ T) (tm-lift (t [ σ ]')) ≡ tm-lift t [ subst-lift σ ]'
  tm-lift-natural {Δ = Δ} σ {T} t = cong₂-d MkTm
    proof
    (funextI (funextI (funext λ _ → funextI (funextI (funext λ _ → uip _ _)))))
    where
      open ≡-Reasoning
      proof = term (subst (Tm (ctx-lift Δ)) (ty-lift-natural σ T) (tm-lift (t [ σ ]')))
                ≡⟨ sym (weak-subst-application (λ x y → term y) (ty-lift-natural σ T)) ⟩
              subst (λ x → (n : ℕ) (δ : Δ ⟨ F ∙ n ⟩) → x ⟨ n , δ ⟩) (ty-lift-natural σ T) (term (tm-lift (t [ σ ]')))
                ≡⟨ subst-∘ (ty-lift-natural σ T) ⟩
              subst (λ x → (n : ℕ) (δ : Δ ⟨ F ∙ n ⟩) → x n δ) (cong type (ty-lift-natural σ T)) (term (tm-lift (t [ σ ]')))
                ≡⟨ cong (λ z → subst (λ x → (n : ℕ) (δ : Δ ⟨ F ∙ n ⟩) → x n δ) z (term (tm-lift (t [ σ ]'))))
                        (uip (cong type (ty-lift-natural σ T)) refl) ⟩
              term (tm-lift t [ subst-lift σ ]') ∎

  lift-◇ : ctx-lift {ℓ} ◇ ≡ ◇
  lift-◇ = cong₂-d (MkCtx _ _)
                    (funextI (funext λ _ → uip _ _))
                    (funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _))))

  lift-ctx-ext : (Γ : Ctx ℓ) (T : Ty Γ) → ctx-lift (Γ ,, T) ≡ ctx-lift Γ ,, ty-lift T
  lift-ctx-ext Γ T = cong₂-d (MkCtx _ _)
                             (funextI (funext λ _ → uip _ _))
                             (funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _))))

  -- TODO: look at the following (there is some trouble using implicit functions)
  {-
  lift-π : (Γ : Ctx ℓ) (T : Ty Γ) → subst (λ x → x ⇒ ctx-lift Γ) (lift-ctx-ext Γ T) (subst-lift (π {T = T})) ≡ π {T = ty-lift T}
  lift-π Γ T = cong₂-d MkSubst
    ((λ {n} → func (subst (λ x → x ⇒ ctx-lift Γ) (lift-ctx-ext Γ T) (subst-lift (π {T = T}))) {n})
        ≡⟨ {!!} ⟩
      subst (λ x → {n : ℕ} → x ⟨ n ⟩ → ctx-lift Γ ⟨ n ⟩) (lift-ctx-ext Γ T) (λ {n} → func (subst-lift (π {T = T})) {n})
        ≡⟨ {!!} ⟩
      (λ {n} → func (π {T = ty-lift T}) {n}) ∎)
    {!!}
    where open ≡-Reasoning
  -}
