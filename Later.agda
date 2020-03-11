module Later where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Unit using (⊤; tt)
open import Function hiding (_⟨_⟩_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

open import Helpers
open import CwF-Structure
open import Types.Functions

--------------------------------------------------
-- Later and earlier modalities for types
--------------------------------------------------

ctx-m≤1+n : (Γ : Ctx ℓ) (m≤n : m ≤ n) →
            Γ ⟪ m≤n ⟫ ∘ Γ ⟪ n≤1+n n ⟫ ≡ Γ ⟪ n≤1+n m ⟫ ∘ Γ ⟪ s≤s m≤n ⟫
ctx-m≤1+n Γ m≤n = funext λ γ →
  trans (cong-app (sym (rel-comp Γ m≤n (n≤1+n _))) γ)
        (trans (cong (Γ ⟪_⟫ γ) (≤-irrelevant _ _))
               (cong-app (rel-comp Γ (n≤1+n _) (s≤s m≤n)) γ))

-- We could define ◄ as LiftedFunctor.ctx-lift (MkFunctor suc s≤s), but then some equalities
-- only hold propositionally, which makes working with them harder.
◄ : Ctx ℓ → Ctx ℓ
set (◄ Γ) n = Γ ⟨ suc n ⟩
rel (◄ Γ) ineq = Γ ⟪ s≤s ineq ⟫
rel-id (◄ Γ) = rel-id Γ
rel-comp (◄ Γ) k≤m m≤n = rel-comp Γ (s≤s k≤m) (s≤s m≤n)

◄-subst : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) → ◄ Δ ⇒ ◄ Γ
func (◄-subst σ) {n} = func σ {suc n}
naturality (◄-subst σ) {ineq = m≤n} = naturality σ {ineq = s≤s m≤n}

◅-ty : {Γ : Ctx ℓ} → Ty Γ → Ty (◄ Γ)
type (◅-ty T) n γ = T ⟨ suc n , γ ⟩
morph (◅-ty T) m≤n γ = T ⟪ s≤s m≤n , γ ⟫
morph-id (◅-ty T) γ = morph-id T γ
morph-comp (◅-ty T) k≤m m≤n γ = morph-comp T (s≤s k≤m) (s≤s m≤n) γ

◅-tm : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → Tm (◄ Γ) (◅-ty T)
term (◅-tm t) n γ = t ⟨ suc n , γ ⟩'
naturality (◅-tm t) m≤n γ = t ⟪ s≤s m≤n , γ ⟫'

◄Γ⇒Γ : (Γ : Ctx ℓ) → ◄ Γ ⇒ Γ
func (◄Γ⇒Γ Γ) = Γ ⟪ n≤1+n _ ⟫
naturality (◄Γ⇒Γ Γ) = ctx-m≤1+n Γ _

▻ : {Γ : Ctx ℓ} → Ty (◄ Γ) → Ty Γ
type (▻ {Γ = Γ} T) zero _ = Lift _ ⊤
type (▻ {Γ = Γ} T) (suc n) γ = T ⟨ n , γ ⟩
morph (▻ {Γ = Γ} T) z≤n γ _ = lift tt
morph (▻ {Γ = Γ} T) (s≤s m≤n) γ = T ⟪ m≤n , γ ⟫
morph-id (▻ {Γ = Γ} T) {zero} _ = refl
morph-id (▻ {Γ = Γ} T) {suc n} = morph-id T
morph-comp (▻ {Γ = Γ} T) z≤n m≤n γ = refl
morph-comp (▻ {Γ = Γ} T) (s≤s k≤m) (s≤s m≤n) = morph-comp T k≤m m≤n

▻' : {Γ : Ctx ℓ} → Ty Γ → Ty Γ
▻' {Γ = Γ} T = ▻ (T [ ◄Γ⇒Γ Γ ])

next : {Γ : Ctx ℓ} {T : Ty (◄ Γ)} → Tm (◄ Γ) T → Tm Γ (▻ T)
term (next t) zero γ = lift tt
term (next t) (suc n) γ = t ⟨ n , γ ⟩'
naturality (next t) z≤n γ = refl
naturality (next t) (s≤s m≤n) γ = t ⟪ m≤n , γ ⟫'

prev : {Γ : Ctx ℓ} {T : Ty (◄ Γ)} → Tm Γ (▻ T) → Tm (◄ Γ) T
term (prev t) n γ = t ⟨ suc n , γ ⟩'
naturality (prev t) m≤n γ = t ⟪ s≤s m≤n , γ ⟫'

prev-next : {Γ : Ctx ℓ} {T : Ty (◄ Γ)} (t : Tm (◄ Γ) T) → prev {Γ = Γ} (next t) ≡ t
prev-next t = refl

next-prev : {Γ : Ctx ℓ} {T : Ty (◄ Γ)} (t : Tm Γ (▻ T)) → next (prev t) ≡ t
next-prev t = cong₂-d MkTm (funext λ { zero → refl ; (suc n) → refl })
                           (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))

-- Agda can infer the implicit arguments Γ and T in the recursive calls itself, but giving them explicitly
-- drastically reduces typechecking time.
Löb : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ (▻' T ⇛ T) → Tm Γ T
term (Löb f) zero γ = f €⟨ zero , γ ⟩ lift tt
term (Löb {Γ = Γ}{T} f) (suc n) γ = f €⟨ suc n , γ ⟩ (Löb {Γ = Γ} {T = T} f ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩')
naturality (Löb f) {n = zero} z≤n γ = €-natural f z≤n γ (lift tt)
naturality (Löb {Γ = Γ}{T} f) {n = suc n} z≤n γ = €-natural f z≤n γ ((Löb {Γ = Γ}{T = T} f) ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩')
naturality (Löb {Γ = Γ}{T} f) {suc m} {suc n} (s≤s m≤n) γ =
  T ⟪ s≤s m≤n , γ ⟫ f €⟨ _ , γ ⟩ (Löb {Γ = Γ}{T} f ⟨ _ , Γ ⟪ n≤1+n _ ⟫ γ ⟩')
      ≡⟨ €-natural f (s≤s m≤n) γ (Löb {Γ = Γ}{T} f ⟨ _ , Γ ⟪ n≤1+n _ ⟫ γ ⟩') ⟩
  f €⟨ _ , Γ ⟪ s≤s m≤n ⟫ γ ⟩ (▻' T ⟪ s≤s m≤n , γ ⟫ (Löb {Γ = Γ}{T} f ⟨ _ , Γ ⟪ n≤1+n _ ⟫ γ ⟩'))
      ≡⟨⟩
  f €⟨ _ , Γ ⟪ s≤s m≤n ⟫ γ ⟩
    (subst (λ x → T ⟨ _ , x γ ⟩) (ctx-m≤1+n Γ m≤n)
    (T ⟪ m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ Löb {Γ = Γ}{T} f ⟨ _ , Γ ⟪ n≤1+n _ ⟫ γ ⟩'))
      ≡⟨ cong (λ z → f €⟨ _ , Γ ⟪ s≤s m≤n ⟫ γ ⟩
                      (subst (λ x → T ⟨ _ , x γ ⟩) (ctx-m≤1+n Γ m≤n) z))
              (naturality (Löb {Γ = Γ}{T} f) m≤n (Γ ⟪ n≤1+n _ ⟫ γ)) ⟩
  (f €⟨ _ , Γ ⟪ s≤s m≤n ⟫ γ ⟩
    (subst (λ x → T ⟨ _ , x γ ⟩) (ctx-m≤1+n Γ m≤n)
    (Löb {Γ = Γ}{T} f ⟨ _ , Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n _ ⟫ γ) ⟩')))
      ≡⟨ cong (f €⟨ _ , Γ ⟪ s≤s m≤n ⟫ γ ⟩_) (cong-d (λ x → Löb {Γ = Γ}{T} f ⟨ _ , x γ ⟩') (ctx-m≤1+n Γ m≤n)) ⟩
  Löb {Γ = Γ}{T} f ⟨ _ , Γ ⟪ s≤s m≤n ⟫ γ ⟩' ∎
  where open ≡-Reasoning

_⊛_ : {Γ : Ctx ℓ} {T S : Ty (◄ Γ)} → Tm Γ (▻ (T ⇛ S)) → Tm Γ (▻ T) → Tm Γ (▻ S)
f ⊛ t = next (app (prev f) (prev t))

-- This is an earlier attempt to define ▻, without the use of ◄.
{-
ctx-m≤1+n-app : (Γ : Ctx ℓ) (m≤n : m ≤ n) (γ : Γ ⟨ suc n ⟩) →
                Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n n ⟫ γ) ≡ Γ ⟪ n≤1+n m ⟫ (Γ ⟪ s≤s m≤n ⟫ γ)
ctx-m≤1+n-app Γ m≤n γ = cong-app (ctx-m≤1+n Γ m≤n) γ

▻ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ
type (▻ {Γ = Γ} T) zero _ = Lift _ ⊤
type (▻ {Γ = Γ} T) (suc n) γ = T ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩
morph (▻ {Γ = Γ} T) z≤n γ = λ _ → lift tt
morph (▻ {Γ = Γ} T) (s≤s ineq) γ t = subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ ineq γ) (T ⟪ ineq , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t)
morph-id (▻ {Γ = Γ} T) {zero} γ = refl
morph-id (▻ {Γ = Γ} T) {suc n} γ = funext λ t →
  subst (λ x → T ⟨ n , Γ ⟪ n≤1+n n ⟫ (x γ) ⟩) (rel-id Γ)
    (subst (λ x → T ⟨ n , x ⟩) (ctx-m≤1+n-app Γ ≤-refl γ) (T ⟪ ≤-refl , Γ ⟪ n≤1+n n ⟫ γ ⟫ t))
      ≡⟨ subst-∘ (rel-id Γ) ⟩
  subst (λ x → T ⟨ n , x ⟩) (cong (λ z → Γ ⟪ n≤1+n n ⟫ (z γ)) (rel-id Γ))
    (subst (λ x → T ⟨ n , x ⟩) (ctx-m≤1+n-app Γ ≤-refl γ) (T ⟪ ≤-refl , Γ ⟪ n≤1+n n ⟫ γ ⟫ t))
      ≡⟨ subst-subst (ctx-m≤1+n-app Γ ≤-refl γ) ⟩
  subst (λ x → T ⟨ n , x ⟩) (trans (ctx-m≤1+n-app Γ ≤-refl γ) (cong (λ z → Γ ⟪ n≤1+n n ⟫ (z γ)) (rel-id Γ)))
    (T ⟪ ≤-refl , Γ ⟪ n≤1+n n ⟫ γ ⟫ t)
      ≡⟨ cong (λ z → subst (λ x → T ⟨ n , x ⟩) z
                            (T ⟪ ≤-refl , Γ ⟪ n≤1+n n ⟫ γ ⟫ t))
              (uip _ _) ⟩
  subst (λ x → T ⟨ n , x ⟩) (cong-app (rel-id Γ) (Γ ⟪ n≤1+n n ⟫ γ))
    (T ⟪ ≤-refl , Γ ⟪ n≤1+n n ⟫ γ ⟫ t)
      ≡⟨ subst-cong-app (rel-id Γ) _ ⟩
  subst (λ x → T ⟨ n , x (Γ ⟪ n≤1+n n ⟫ γ) ⟩) (rel-id Γ)
    (T ⟪ ≤-refl , Γ ⟪ n≤1+n n ⟫ γ ⟫ t)
      ≡⟨ cong-app (morph-id T (Γ ⟪ n≤1+n n ⟫ γ)) t ⟩
  t ∎
  where open ≡-Reasoning
morph-comp (▻ T) z≤n m≤n γ = refl
morph-comp (▻ {Γ = Γ} T) (s≤s k≤m) (s≤s m≤n) γ = funext λ t →
  subst (λ x → T ⟨ _ , Γ ⟪ n≤1+n _ ⟫ (x γ) ⟩) (rel-comp Γ (s≤s k≤m) (s≤s m≤n))
    (subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ (≤-trans k≤m m≤n) γ) (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t))
      ≡⟨ subst-∘ (rel-comp Γ (s≤s k≤m) (s≤s m≤n)) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (cong (λ z → Γ ⟪ n≤1+n _ ⟫ (z γ)) (rel-comp Γ (s≤s k≤m) (s≤s m≤n)))
    (subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ (≤-trans k≤m m≤n) γ) (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t))
      ≡⟨ subst-subst (ctx-m≤1+n-app Γ (≤-trans k≤m m≤n) γ) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (trans (ctx-m≤1+n-app Γ (≤-trans k≤m m≤n) γ)
                                   (cong (λ z → Γ ⟪ n≤1+n _ ⟫ (z γ)) (rel-comp Γ (s≤s k≤m) (s≤s m≤n))))
    (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t)
      ≡⟨ cong (λ z → subst (λ x → T ⟨ _ , x ⟩) z
                            (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t))
              (uip _ _) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (trans (cong-app (rel-comp Γ k≤m m≤n) (Γ ⟪ n≤1+n _ ⟫ γ))
                                   (trans (cong (Γ ⟪ k≤m ⟫) (ctx-m≤1+n-app Γ m≤n γ))
                                          (ctx-m≤1+n-app Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))))
    (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t)
      ≡⟨ sym (subst-subst (cong-app (rel-comp Γ k≤m m≤n) (Γ ⟪ n≤1+n _ ⟫ γ))) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (trans (cong (Γ ⟪ k≤m ⟫) (ctx-m≤1+n-app Γ m≤n γ))
                                          (ctx-m≤1+n-app Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ)))
    (subst (λ x → T ⟨ _ , x ⟩) (cong-app (rel-comp Γ k≤m m≤n) (Γ ⟪ n≤1+n _ ⟫ γ))
    (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t))
      ≡⟨ sym (subst-subst (cong (Γ ⟪ k≤m ⟫) (ctx-m≤1+n-app Γ m≤n γ))) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))
    (subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ k≤m ⟫) (ctx-m≤1+n-app Γ m≤n γ))
    (subst (λ x → T ⟨ _ , x ⟩) (cong-app (rel-comp Γ k≤m m≤n) (Γ ⟪ n≤1+n _ ⟫ γ))
    (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t)))
      ≡⟨ cong (subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ)))
              (sym (subst-∘ (ctx-m≤1+n-app Γ m≤n γ))) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))
    (subst (λ x → T ⟨ _ , Γ ⟪ k≤m ⟫ x ⟩) (ctx-m≤1+n-app Γ m≤n γ)
    (subst (λ x → T ⟨ _ , x ⟩) (cong-app (rel-comp Γ k≤m m≤n) (Γ ⟪ n≤1+n _ ⟫ γ))
    (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t)))
      ≡⟨ cong (λ z → subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))
                            (subst (λ x → T ⟨ _ , Γ ⟪ k≤m ⟫ x ⟩) (ctx-m≤1+n-app Γ m≤n γ) z))
              (subst-cong-app (rel-comp Γ k≤m m≤n) _) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))
    (subst (λ x → T ⟨ _ , Γ ⟪ k≤m ⟫ x ⟩) (ctx-m≤1+n-app Γ m≤n γ)
    (subst (λ x → T ⟨ _ , x (Γ ⟪ n≤1+n _ ⟫ γ) ⟩) (rel-comp Γ k≤m m≤n)
    (T ⟪ ≤-trans k≤m m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t)))
      ≡⟨ cong (λ z → subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))
                            (subst (λ x → T ⟨ _ , Γ ⟪ k≤m ⟫ x ⟩) (ctx-m≤1+n-app Γ m≤n γ) z))
              (cong-app (morph-comp T k≤m m≤n (Γ ⟪ n≤1+n _ ⟫ γ)) t) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))
    (subst (λ x → T ⟨ _ , Γ ⟪ k≤m ⟫ x ⟩) (ctx-m≤1+n-app Γ m≤n γ)
    (T ⟪ k≤m , Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n _ ⟫ γ) ⟫
    (T ⟪ m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t)))
      ≡⟨ cong (subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ)))
              (weak-subst-application (λ x → T ⟪ k≤m , x ⟫) (ctx-m≤1+n-app Γ m≤n γ)) ⟩
  subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ k≤m (Γ ⟪ s≤s m≤n ⟫ γ))
    (T ⟪ k≤m , Γ ⟪ n≤1+n _ ⟫ (Γ ⟪ s≤s m≤n ⟫ γ) ⟫
    (subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ m≤n γ)
    (T ⟪ m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ t))) ∎
  where open ≡-Reasoning

next : {Γ : Ctx ℓ} {T : Ty Γ} → Tm (◄ Γ) (T [ ◄Γ⇒Γ Γ ]) → Tm Γ (▻ T)
term (next t) zero γ = lift tt
term (next t) (suc n) γ = t ⟨ n , γ ⟩'
naturality (next t) z≤n γ = refl
naturality (next {Γ = Γ}{T} t) (s≤s m≤n) γ =
  subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ m≤n γ)
    (T ⟪ m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ (t ⟨ _ , γ ⟩'))
      ≡⟨ subst-cong-app (ctx-m≤1+n Γ m≤n) _ ⟩
  T [ ◄Γ⇒Γ Γ ] ⟪ m≤n , γ ⟫ (t ⟨ _ , γ ⟩')
      ≡⟨ t ⟪ m≤n , γ ⟫' ⟩
  t ⟨ _ , Γ ⟪ s≤s m≤n ⟫ γ ⟩' ∎
  where open ≡-Reasoning

prev : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ (▻ T) → Tm (◄ Γ) (T [ ◄Γ⇒Γ Γ ])
term (prev t) n γ = t ⟨ suc n , γ ⟩'
naturality (prev {Γ = Γ}{T} t) {m}{n} m≤n γ =
  (T [ ◄Γ⇒Γ Γ ]) ⟪ m≤n , γ ⟫ prev t ⟨ n , γ ⟩'
    ≡⟨⟩
  subst (λ x → T ⟨ _ , x γ ⟩) (ctx-m≤1+n Γ m≤n) (T ⟪ m≤n , Γ ⟪ n≤1+n n ⟫ γ ⟫ t ⟨ suc n , γ ⟩')
    ≡⟨ {!!} ⟩
  subst (λ x → T ⟨ _ , x γ ⟩) (ctx-m≤1+n Γ m≤n) (t ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩')
    ≡⟨ ? ⟩
  t ⟨ suc m , Γ ⟪ s≤s m≤n ⟫ γ ⟩'
    ≡⟨⟩
  prev t ⟨ m , ◄ Γ ⟪ m≤n ⟫ γ ⟩' ∎
  where open ≡-Reasoning

Löb : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ (▻ T ⇛ T) → Tm Γ T
term (Löb f) zero γ = f €⟨ zero , γ ⟩ lift tt
term (Löb {Γ = Γ} f) (suc n) γ = f €⟨ suc n , γ ⟩ (Löb f ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩')
naturality (Löb f) {n = zero} z≤n γ = €-natural f z≤n γ (lift tt)
naturality (Löb {Γ = Γ} f) {n = suc n} z≤n γ = €-natural f z≤n γ (Löb f ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩')
naturality (Löb {Γ = Γ}{T} f) (s≤s m≤n) γ =
  T ⟪ s≤s m≤n , γ ⟫ f €⟨ _ , γ ⟩ (Löb f ⟨ _ , Γ ⟪ n≤1+n _ ⟫ γ ⟩')
      ≡⟨ €-natural f (s≤s m≤n) γ (Löb f ⟨ _ , Γ ⟪ n≤1+n _ ⟫ γ ⟩') ⟩
  f €⟨ _ , Γ ⟪ s≤s m≤n ⟫ γ ⟩ (▻ T ⟪ s≤s m≤n , γ ⟫ (Löb f ⟨ _ , Γ ⟪ n≤1+n _ ⟫ γ ⟩'))
      ≡⟨⟩
  f €⟨ _ , Γ ⟪ s≤s m≤n ⟫ γ ⟩
    (subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ m≤n γ)
    (T ⟪ m≤n , Γ ⟪ n≤1+n _ ⟫ γ ⟫ Löb f ⟨ _ , Γ ⟪ n≤1+n _ ⟫ γ ⟩'))
      ≡⟨ cong (λ z → f €⟨ _ , Γ ⟪ s≤s m≤n ⟫ γ ⟩
                      (subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ m≤n γ) z))
              (naturality (Löb f) m≤n (Γ ⟪ n≤1+n _ ⟫ γ)) ⟩
  f €⟨ _ , Γ ⟪ s≤s m≤n ⟫ γ ⟩
    (subst (λ x → T ⟨ _ , x ⟩) (ctx-m≤1+n-app Γ m≤n γ)
    (Löb f ⟨ _ , Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n _ ⟫ γ) ⟩'))
      ≡⟨ cong (f €⟨ _ , Γ ⟪ s≤s m≤n ⟫ γ ⟩_) (cong-d (λ x → Löb f ⟨ _ , x ⟩') (ctx-m≤1+n-app Γ m≤n γ)) ⟩
  Löb f ⟨ _ , Γ ⟪ s≤s m≤n ⟫ γ ⟩' ∎
  where open ≡-Reasoning
-}
