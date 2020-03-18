module Types.Functions where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Function hiding (_⟨_⟩_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension

-- TODO: show that everything is natural with respect to the context (so e.g. that
-- (T ⇛ S) [ σ ] ≡ T [ σ ] ⇛ S [ σ ])

--------------------------------------------------
-- (Non-dependent) function types
--------------------------------------------------

record PresheafFunc {ℓ} {Γ : Ctx ℓ} (T S : Ty Γ) (n : ℕ) (γ : Γ ⟨ n ⟩) : Set ℓ where
  constructor MkFunc
  field
    _$⟨_⟩_ : ∀ {m} (ineq : m ≤ n) → T ⟨ m , Γ ⟪ ineq ⟫ γ ⟩ → S ⟨ m , Γ ⟪ ineq ⟫ γ ⟩
    naturality : ∀ {k m} (k≤m : k ≤ m) (m≤n : m ≤ n) (t : T ⟨ m , Γ ⟪ m≤n ⟫ γ ⟩)→
                 _$⟨_⟩_ (≤-trans k≤m m≤n) (subst (λ x → T ⟨ k , x ⟩) (sym (rel-comp Γ k≤m m≤n γ)) (T ⟪ k≤m , Γ ⟪ m≤n ⟫ γ ⟫ t)) ≡
                   subst (λ x → S ⟨ k , x ⟩) (sym (rel-comp Γ k≤m m≤n γ)) (S ⟪ k≤m , Γ ⟪ m≤n ⟫ γ ⟫ (_$⟨_⟩_ m≤n t))
  infix 13 _$⟨_⟩_
open PresheafFunc public

to-pshfun-eq : {Γ : Ctx ℓ} {T S : Ty Γ} {n : ℕ} {γ : Γ ⟨ n ⟩} {f g : PresheafFunc T S n γ} →
               (∀ {m} (ineq : m ≤ n) t → f $⟨ ineq ⟩ t ≡ g $⟨ ineq ⟩ t) →
               f ≡ g
to-pshfun-eq e = cong₂-d MkFunc
  (funextI (funext (λ ineq → funext λ t → e ineq t)))
  (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _)))

lower-presheaffunc : ∀ {m n} {Γ : Ctx ℓ} {T S : Ty Γ} (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → PresheafFunc T S n γ → PresheafFunc T S m (Γ ⟪ ineq ⟫ γ)
lower-presheaffunc {m = m}{n}{Γ}{T}{S} m≤n γ f = MkFunc g g-nat
  where
    g : ∀ {k} (k≤m : k ≤ m) → T ⟨ k , Γ ⟪ k≤m ⟫ (Γ ⟪ m≤n ⟫ γ) ⟩ → S ⟨ k , Γ ⟪ k≤m ⟫ (Γ ⟪ m≤n ⟫ γ) ⟩
    g k≤m = subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ k≤m m≤n γ)
            ∘ f $⟨ ≤-trans k≤m m≤n ⟩_
            ∘ subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤m m≤n γ))
    open ≡-Reasoning
    g-nat : ∀ {k l} (k≤l : k ≤ l) (l≤m : l ≤ m) → _
    g-nat k≤l l≤m t =
      subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
        (f $⟨ ≤-trans (≤-trans k≤l l≤m) m≤n ⟩
        subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ))
        (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ)))
        (T ⟪ k≤l , Γ ⟪ l≤m ⟫ (Γ ⟪ m≤n ⟫ γ) ⟫ t)))
          ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
                                (f $⟨ ≤-trans (≤-trans k≤l l≤m) m≤n ⟩ z))
                  (sym (subst-subst-sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))) ⟩
      subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
        (f $⟨ ≤-trans (≤-trans k≤l l≤m) m≤n ⟩
        subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
        (subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
        (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ))
        (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ)))
        (T ⟪ k≤l , Γ ⟪ l≤m ⟫ (Γ ⟪ m≤n ⟫ γ) ⟫ t)))))
          ≡⟨ cong (subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ))
                  (sym (weak-subst-application (λ x → f $⟨ x ⟩_) (≤-irrelevant _ _))) ⟩
      subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
        (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
        (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
        subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
        (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ))
        (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ)))
        (T ⟪ k≤l , Γ ⟪ l≤m ⟫ (Γ ⟪ m≤n ⟫ γ) ⟫ t)))))
          ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
                          (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
                          (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩ z)))
                  (sym (ctx-≤-trans-sym-assoc Γ (λ y → T ⟨ _ , y ⟩))) ⟩
      subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
        (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
        (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
        subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ))
        (subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ k≤l ⟫) (sym (rel-comp Γ l≤m m≤n γ)))
        (T ⟪ k≤l , Γ ⟪ l≤m ⟫ (Γ ⟪ m≤n ⟫ γ) ⟫ t))))
          ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
                          (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
                          (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
                          subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ)) z)))
                  (subst-application' (λ x → T ⟨ _ , x ⟩) (λ x → T ⟪ k≤l , x ⟫) (sym (rel-comp Γ l≤m m≤n γ))) ⟩
      subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
        (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
        (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
        subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ))
        (T ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
        subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ l≤m m≤n γ)) t)))
          ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
                         (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
                         z))
                  (naturality f k≤l (≤-trans l≤m m≤n) _) ⟩
      subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
        (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
        (subst (λ x → S ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ))
        (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
        (f $⟨ ≤-trans l≤m m≤n ⟩
        subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ l≤m m≤n γ)) t))))
          ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ) z)
                  (subst-∘ (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))) ⟩
      subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
        (subst (λ x → S ⟨ _ , x ⟩) (cong (λ x → Γ ⟪ x ⟫ γ) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
        (subst (λ x → S ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ))
        (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
        (f $⟨ ≤-trans l≤m m≤n ⟩
        subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ l≤m m≤n γ)) t))))
          ≡⟨ subst-subst (cong (λ x → Γ ⟪ x ⟫ γ) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))) ⟩
      subst (λ x → S ⟨ _ , x ⟩)
            (trans (cong (λ x → Γ ⟪ x ⟫ γ) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
                   (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ))
        (subst (λ x → S ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ))
        (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
        (f $⟨ ≤-trans l≤m m≤n ⟩
        subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ l≤m m≤n γ)) t)))
          ≡⟨ subst-subst (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ)) ⟩
      subst (λ x → S ⟨ _ , x ⟩)
            (trans (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ))
            (trans (cong (λ x → Γ ⟪ x ⟫ γ) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
                   (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)))
        (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
        (f $⟨ ≤-trans l≤m m≤n ⟩
        subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ l≤m m≤n γ)) t))
          ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x ⟩) z
                         (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
                         (f $⟨ ≤-trans l≤m m≤n ⟩
                         subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ l≤m m≤n γ)) t)))
                  (uip _ (trans (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ))
                                (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))))) ⟩
      subst (λ x → S ⟨ _ , x ⟩)
            (trans (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ))
                   (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))))
        (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
        (f $⟨ ≤-trans l≤m m≤n ⟩
        subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ l≤m m≤n γ)) t))
          ≡⟨ sym (subst-subst (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ))) ⟩
      subst (λ x → S ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ)))
        (subst (λ x → S ⟨ _ , x ⟩) (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ))
        (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
        (f $⟨ ≤-trans l≤m m≤n ⟩
        subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ l≤m m≤n γ)) t)))
          ≡⟨ cong (subst (λ x → S ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))))
                  (subst-application' (λ z → S ⟨ _ , z ⟩) (λ x → S ⟪ k≤l , x ⟫) (rel-comp Γ l≤m m≤n γ)) ⟩
      subst (λ x → S ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ)))
        (S ⟪ k≤l , Γ ⟪ l≤m ⟫ (Γ ⟪ m≤n ⟫ γ) ⟫
        subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ l≤m m≤n γ)
        (f $⟨ ≤-trans l≤m m≤n ⟩
        subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ l≤m m≤n γ)) t)) ∎

_⇛_ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ → Ty Γ
type (_⇛_ {Γ = Γ} T S) = λ n γ → PresheafFunc T S n γ
morph (_⇛_ {Γ = Γ} T S) = lower-presheaffunc
morph-id (_⇛_ {Γ = Γ} T S) {γ = γ} f = to-pshfun-eq λ m≤n t →
  subst (λ x → (T ⇛ S) ⟨ _ , x ⟩) (rel-id Γ γ) ((T ⇛ S) ⟪ ≤-refl , γ ⟫ f) $⟨ m≤n ⟩ t
      ≡⟨ cong (λ z → z t) (sym (subst-application' (λ x → (T ⇛ S) ⟨ _ , x ⟩) {λ x → T ⟨ _ , x ⟩ → S ⟨ _ , x ⟩} (λ x y → y $⟨ m≤n ⟩_) (rel-id Γ γ))) ⟩
  subst (λ x → T ⟨ _ , x ⟩ → S ⟨ _ , x ⟩) (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ)) (((T ⇛ S) ⟪ ≤-refl , γ ⟫ f) $⟨ m≤n ⟩_) t
      ≡⟨ function-subst (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ)) (((T ⇛ S) ⟪ ≤-refl , γ ⟫ f) $⟨ m≤n ⟩_) ⟩
  subst (λ x → S ⟨ _ , x ⟩) (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))
    (((T ⇛ S) ⟪ ≤-refl , γ ⟫ f) $⟨ m≤n ⟩
    (subst (λ x → T ⟨ _ , x ⟩) (sym (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))) t))
      ≡⟨⟩
  subst (λ x → S ⟨ _ , x ⟩) (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))
    (subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ m≤n ≤-refl γ)
    (f $⟨ ≤-trans m≤n ≤-refl ⟩
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ m≤n ≤-refl γ))
    (subst (λ x → T ⟨ _ , x ⟩) (sym (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))) t)))
      ≡⟨ ctx-≤-trans-right-id Γ (λ x → S ⟨ _ , x ⟩) ⟩
  subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)
    (f $⟨ ≤-trans m≤n ≤-refl ⟩
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ m≤n ≤-refl γ))
    (subst (λ x → T ⟨ _ , x ⟩) (sym (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))) t))
      ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)
                      (f $⟨ ≤-trans m≤n ≤-refl ⟩
                      z))
              (ctx-≤-trans-sym-right-id Γ (λ x → T ⟨ _ , x ⟩)) ⟩
  subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)
    (f $⟨ ≤-trans m≤n ≤-refl ⟩
    subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (sym (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)) t)
      ≡⟨ weak-subst-application (λ x → f $⟨ x ⟩_) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n) ⟩
  f $⟨ m≤n ⟩
    subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)
    (subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (sym (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)) t)
      ≡⟨ cong (f $⟨ m≤n ⟩_) (subst-subst-sym (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)) ⟩
  f $⟨ m≤n ⟩ t ∎
  where open ≡-Reasoning
morph-comp (_⇛_ {Γ = Γ} T S) l≤m m≤n {γ} f = to-pshfun-eq λ k≤l t →
  (subst (λ x → (T ⇛ S) ⟨ _ , x ⟩) (rel-comp Γ l≤m m≤n γ) ((T ⇛ S) ⟪ ≤-trans l≤m m≤n , γ ⟫ f)) $⟨ k≤l ⟩ t
      ≡⟨ cong (λ z → z t) (sym (subst-application' (λ x → (T ⇛ S) ⟨ _ , x ⟩) {λ x → T ⟨ _ , x ⟩ → S ⟨ _ , x ⟩} (λ x y → y $⟨ k≤l ⟩_) (rel-comp Γ l≤m m≤n γ))) ⟩
  subst (λ x → T ⟨ _ , x ⟩ → S ⟨ _ , x ⟩) (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ)) (((T ⇛ S) ⟪ ≤-trans l≤m m≤n , γ ⟫ f) $⟨ k≤l ⟩_) t
      ≡⟨ function-subst (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ)) (((T ⇛ S) ⟪ ≤-trans l≤m m≤n , γ ⟫ f) $⟨ k≤l ⟩_) ⟩
  subst (λ x → S ⟨ _ , x ⟩) (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ))
    (((T ⇛ S) ⟪ ≤-trans l≤m m≤n , γ ⟫ f) $⟨ k≤l ⟩
    (subst (λ x → T ⟨ _ , x ⟩) (sym (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ))) t))
      ≡⟨⟩
  subst (λ x → S ⟨ _ , x ⟩) (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ))
    (subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ)
    (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ))
    (subst (λ x → T ⟨ _ , x ⟩) (sym (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ))) t)))
      ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x ⟩) (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ))
                      (subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ)
                      (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
                      subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ))
                      (subst (λ x → T ⟨ _ , x ⟩) z t))))
              (sym (cong-sym (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ))) ⟩
  subst (λ x → S ⟨ _ , x ⟩) (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ))
    (subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ)
    (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ))
    (subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ k≤l ⟫) (sym (rel-comp Γ l≤m m≤n γ))) t)))
      ≡⟨ ctx-≤-trans-assoc Γ (λ y → S ⟨ _ , y ⟩) ⟩
  subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))
    (subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
    (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
    (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ))
    (subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ k≤l ⟫) (sym (rel-comp Γ l≤m m≤n γ))) t))))
      ≡⟨ cong (λ z →   subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))
                        (subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
                        (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
                        (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩ z))))
             (ctx-≤-trans-sym-assoc Γ (λ y → T ⟨ _ , y ⟩)) ⟩
  subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))
    (subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
    (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
    (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
    subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
    (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ))
    (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))) t)))))
      ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))
                      (subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ) z))
              (weak-subst-application (λ x → f $⟨ x ⟩_) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))) ⟩
  subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))
    (subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
    (f $⟨ ≤-trans (≤-trans k≤l l≤m) m≤n ⟩
    subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
    (subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
    (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ))
    (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))) t)))))
      ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))
                      (subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
                      (f $⟨ ≤-trans (≤-trans k≤l l≤m) m≤n ⟩ z)))
              (subst-subst-sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))) ⟩
  ((T ⇛ S) ⟪ l≤m , Γ ⟪ m≤n ⟫ γ ⟫) ((T ⇛ S) ⟪ m≤n , γ ⟫ f) $⟨ k≤l ⟩ t ∎
  where open ≡-Reasoning

lam : {Γ : Ctx ℓ} (T : Ty Γ) {S : Ty Γ} → Tm (Γ ,, T) (S [ π ]) → Tm Γ (T ⇛ S)
term (lam {Γ = Γ} T {S} b) = λ n γ → MkFunc (λ m≤n t → b ⟨ _ , [ Γ ⟪ m≤n ⟫ γ , t ] ⟩')
                                             (λ k≤m m≤n t →
  b ⟨ _ , [ Γ ⟪ ≤-trans k≤m m≤n ⟫ γ , subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤m m≤n γ)) ((T ⟪ k≤m , Γ ⟪ m≤n ⟫ γ ⟫) t) ] ⟩'
    ≡⟨ sym (weak-subst-application (λ x y → b ⟨ _ , [ x , y ] ⟩') (sym (rel-comp Γ k≤m m≤n γ))) ⟩
  subst (λ x → S ⟨ _ , x ⟩) (sym (rel-comp Γ k≤m m≤n γ)) (b ⟨ _ , [ Γ ⟪ k≤m ⟫ (Γ ⟪ m≤n ⟫ γ) , T ⟪ k≤m , Γ ⟪ m≤n ⟫ γ ⟫ t ] ⟩')
    ≡⟨ cong (subst (λ x → S ⟨ _ , x ⟩) (sym (rel-comp Γ k≤m m≤n γ))) (sym (naturality b k≤m [ Γ ⟪ m≤n ⟫ γ , t ])) ⟩
  subst (λ x → S ⟨ _ , x ⟩) (sym (rel-comp Γ k≤m m≤n γ)) (S ⟪ k≤m , Γ ⟪ m≤n ⟫ γ ⟫ (b ⟨ _ , [ Γ ⟪ m≤n ⟫ γ , t ] ⟩')) ∎)
  where open ≡-Reasoning
naturality (lam {Γ = Γ} T {S} b) = λ m≤n γ → to-pshfun-eq (λ k≤m t →
  subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ k≤m m≤n γ) (b ⟨ _ , [ Γ ⟪ ≤-trans k≤m m≤n ⟫ γ , subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤m m≤n γ)) t ] ⟩')
    ≡⟨ weak-subst-application (λ x y → b ⟨ _ , [ x , y ] ⟩') (rel-comp Γ k≤m m≤n γ) ⟩
  b ⟨ _ , [ Γ ⟪ k≤m ⟫ (Γ ⟪ m≤n ⟫ γ) , subst (λ x → T ⟨ _ , x ⟩) (rel-comp Γ k≤m m≤n γ) (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ k≤m m≤n γ)) t) ] ⟩'
    ≡⟨ cong (λ z → b ⟨ _ , [ Γ ⟪ k≤m ⟫ (Γ ⟪ m≤n ⟫ γ) , z ] ⟩') (subst-subst-sym (rel-comp Γ k≤m m≤n γ)) ⟩
  b ⟨ _ , [ Γ ⟪ k≤m ⟫ (Γ ⟪ m≤n ⟫ γ) , t ] ⟩' ∎)
  where open ≡-Reasoning
{-
func-term-natural : {Γ : Ctx ℓ} {T S : Ty Γ} (f : Tm Γ (T ⇛ S))
                    (m≤n : m ≤ n) {γ : Γ ⟨ n ⟩} (t : T ⟨ m , Γ ⟪ m≤n ⟫ γ ⟩) →
                    f ⟨ n , γ ⟩' $⟨ m≤n ⟩ t ≡
                      subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (rel-id Γ)
                            (f ⟨ m , Γ ⟪ m≤n ⟫ γ ⟩' $⟨ ≤-refl ⟩ (subst (λ x → T ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-id Γ)) t))
func-term-natural {Γ = Γ}{T}{S} f m≤n {γ} t =
  f ⟨ _ , γ ⟩' $⟨ m≤n ⟩ t
      ≡⟨ cong (f ⟨ _ , γ ⟩' $⟨ m≤n ⟩_) (sym (subst-subst-sym (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n))) ⟩
  f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
    subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n)
    (subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (sym (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n)) t)
      ≡⟨ sym (weak-subst-application (λ x y → f ⟨ _ , γ ⟩' $⟨ x ⟩ y) (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n)) ⟩
  subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n)
    (f ⟨ _ , γ ⟩' $⟨ ≤-trans ≤-refl m≤n ⟩
    subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (sym (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n)) t)
      ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n)
                            (f ⟨ _ , γ ⟩' $⟨ ≤-trans ≤-refl m≤n ⟩ z))
              (sym (ctx-≤-trans-sym-left-id Γ (λ x → T ⟨ _ , x ⟩))) ⟩
  subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n)
    (f ⟨ _ , γ ⟩' $⟨ ≤-trans ≤-refl m≤n ⟩
    subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ ≤-refl m≤n))
    (subst (λ x → T ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-id Γ)) t))
      ≡⟨ sym (ctx-≤-trans-left-id Γ (λ x → S ⟨ _ , x ⟩)) ⟩
  subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (rel-id Γ)
    (subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ ≤-refl m≤n)
    (f ⟨ _ , γ ⟩' $⟨ ≤-trans ≤-refl m≤n ⟩
    subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ ≤-refl m≤n))
    (subst (λ x → T ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-id Γ)) t)))
      ≡⟨⟩
  subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (rel-id Γ)
    (((T ⇛ S) ⟪ m≤n , γ ⟫ f ⟨ _ , γ ⟩') $⟨ ≤-refl ⟩
    (subst (λ x → T ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-id Γ)) t))
      ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (rel-id Γ)
                      (z $⟨ ≤-refl ⟩
                      (subst (λ x → T ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-id Γ)) t)))
              (naturality f m≤n γ) ⟩
  subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (rel-id Γ)
    (f ⟨ _ , Γ ⟪ m≤n ⟫ γ ⟩' $⟨ ≤-refl ⟩
    subst (λ x → T ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-id Γ)) t) ∎
  where open ≡-Reasoning
-}

_€⟨_,_⟩_ : {Γ : Ctx ℓ} {T S : Ty Γ} → Tm Γ (T ⇛ S) → (n : ℕ) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ → S ⟨ n , γ ⟩
_€⟨_,_⟩_ {Γ = Γ}{T}{S} f n γ t = subst (λ x → S ⟨ _ , x ⟩) (rel-id Γ γ)
                                  (f ⟨ n , γ ⟩' $⟨ ≤-refl ⟩
                                  subst (λ x → T ⟨ _ , x ⟩) (sym (rel-id Γ γ)) t)

€-natural : {Γ : Ctx ℓ} {T S : Ty Γ} (f : Tm Γ (T ⇛ S)) (m≤n : m ≤ n) (γ : Γ ⟨ n ⟩) (t : T ⟨ n , γ ⟩) →
            S ⟪ m≤n , γ ⟫ (f €⟨ n , γ ⟩ t) ≡ f €⟨ m , Γ ⟪ m≤n ⟫ γ ⟩ (T ⟪ m≤n , γ ⟫ t)
€-natural {Γ = Γ}{T}{S} f m≤n γ t =
  S ⟪ m≤n , γ ⟫ (f €⟨ _ , γ ⟩ t)
      ≡⟨⟩
  S ⟪ m≤n , γ ⟫
    subst (λ x → S ⟨ _ , x ⟩) (rel-id Γ γ)
    (f ⟨ _ , γ ⟩' $⟨ ≤-refl ⟩
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-id Γ γ)) t)
      ≡⟨ sym (subst-application' (λ z → S ⟨ _ , z ⟩) (λ x y → S ⟪ m≤n , x ⟫ y) (rel-id Γ γ)) ⟩
  subst (λ x → S ⟨ _ , x ⟩) (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))
    (S ⟪ m≤n , Γ ⟪ ≤-refl ⟫ γ ⟫
    f ⟨ _ , γ ⟩' $⟨ ≤-refl ⟩
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-id Γ γ)) t)
      ≡⟨ cong (subst (λ x → S ⟨ _ , x ⟩) (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ)))
              (sym (subst-subst-sym (rel-comp Γ m≤n ≤-refl γ))) ⟩
  subst (λ x → S ⟨ _ , x ⟩) (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))
    (subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ m≤n ≤-refl γ)
    (subst (λ x → S ⟨ _ , x ⟩) (sym (rel-comp Γ m≤n ≤-refl γ))
    (S ⟪ m≤n , Γ ⟪ ≤-refl ⟫ γ ⟫
    f ⟨ _ , γ ⟩' $⟨ ≤-refl ⟩
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-id Γ γ)) t)))
      ≡⟨ ctx-≤-trans-right-id Γ (λ x → S ⟨ _ , x ⟩) ⟩
  subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)
    (subst (λ x → S ⟨ _ , x ⟩) (sym (rel-comp Γ m≤n ≤-refl γ))
    (S ⟪ m≤n , Γ ⟪ ≤-refl ⟫ γ ⟫
    f ⟨ _ , γ ⟩' $⟨ ≤-refl ⟩
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-id Γ γ)) t))
      ≡⟨ cong (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n))
              (sym (naturality (f ⟨ _ , γ ⟩') m≤n ≤-refl _)) ⟩
  subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)
    (f ⟨ _ , γ ⟩' $⟨ ≤-trans m≤n ≤-refl ⟩
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ m≤n ≤-refl γ))
    (T ⟪ m≤n , Γ ⟪ ≤-refl ⟫ γ ⟫
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-id Γ γ)) t))
      ≡⟨ weak-subst-application (λ x y → f ⟨ _ , γ ⟩' $⟨ x ⟩ y) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n) ⟩
  f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
    subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)
    (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ m≤n ≤-refl γ))
    (T ⟪ m≤n , Γ ⟪ ≤-refl ⟫ γ ⟫
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-id Γ γ)) t))
      ≡⟨ cong (f ⟨ _ , γ ⟩' $⟨ m≤n ⟩_) (sym (ctx-≤-trans-right-id Γ (λ x → T ⟨ _ , x ⟩))) ⟩
  f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
    subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))
    (subst (λ x → T ⟨ _ , x ⟩) (rel-comp Γ m≤n ≤-refl γ)
    (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ m≤n ≤-refl γ))
    (T ⟪ m≤n , Γ ⟪ ≤-refl ⟫ γ ⟫
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-id Γ γ)) t)))
      ≡⟨ cong (λ z → f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
                      subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ)) z)
              (subst-subst-sym (rel-comp Γ m≤n ≤-refl γ)) ⟩
  f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
    subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))
    (T ⟪ m≤n , Γ ⟪ ≤-refl ⟫ γ ⟫
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-id Γ γ)) t)
      ≡⟨ cong (λ z → f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
                       subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ)) z)
              (sym (subst-application' (λ z → T ⟨ _ , z ⟩) (λ x → T ⟪ m≤n , x ⟫) (sym (rel-id Γ γ)))) ⟩
  f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
    subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))
    (subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ m≤n ⟫) (sym (rel-id Γ γ)))
    (T ⟪ m≤n , γ ⟫ t))
      ≡⟨ cong (λ z → f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
                      subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))
                      (subst (λ x → T ⟨ _ , x ⟩) z
                      (T ⟪ m≤n , γ ⟫ t)))
              (cong-sym (Γ ⟪ m≤n ⟫) (rel-id Γ γ)) ⟩
  f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
    subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))
    (subst (λ x → T ⟨ _ , x ⟩) (sym (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ)))
    (T ⟪ m≤n , γ ⟫ t))
      ≡⟨ cong (f ⟨ _ , γ ⟩' $⟨ m≤n ⟩_) (subst-subst-sym (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))) ⟩
  f ⟨ _ , γ ⟩' $⟨ m≤n ⟩ (T ⟪ m≤n , γ ⟫ t)
      ≡⟨ cong (f ⟨ _ , γ ⟩' $⟨ m≤n ⟩_)
              (sym (subst-subst-sym (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n))) ⟩
  f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
    subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n)
    (subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (sym (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n))
    (T ⟪ m≤n , γ ⟫ t))
      ≡⟨ cong (λ z → f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
                      subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n) z)
              (sym (ctx-≤-trans-sym-left-id Γ λ x → T ⟨ _ , x ⟩)) ⟩
  f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
    subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n)
    (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ ≤-refl m≤n γ))
    (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-id Γ (Γ ⟪ m≤n ⟫ γ)))
    (T ⟪ m≤n , γ ⟫ t)))
      ≡⟨ sym (weak-subst-application (λ x → f ⟨ _ , γ ⟩' $⟨ x ⟩_) (≤-irrelevant (≤-trans (≤-reflexive refl) m≤n) m≤n)) ⟩
  subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n)
    (f ⟨ _ , γ ⟩' $⟨ ≤-trans ≤-refl m≤n ⟩
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ ≤-refl m≤n γ))
    (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-id Γ (Γ ⟪ m≤n ⟫ γ)))
    (T ⟪ m≤n , γ ⟫ t)))
      ≡⟨ sym (ctx-≤-trans-left-id Γ (λ x → S ⟨ _ , x ⟩)) ⟩
  subst (λ x → S ⟨ _ , x ⟩) (rel-id Γ (Γ ⟪ m≤n ⟫ γ))
    (subst (λ x → S ⟨ _ , x ⟩) (rel-comp Γ ≤-refl m≤n γ)
    (f ⟨ _ , γ ⟩' $⟨ ≤-trans ≤-refl m≤n ⟩
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-comp Γ ≤-refl m≤n γ))
    (subst (λ x → T ⟨ _ , x ⟩) (sym (rel-id Γ (Γ ⟪ m≤n ⟫ γ)))
    (T ⟪ m≤n , γ ⟫ t))))
      ≡⟨⟩
  subst (λ x → S ⟨ _ , x ⟩) (rel-id Γ (Γ ⟪ m≤n ⟫ γ))
    (((T ⇛ S) ⟪ m≤n , γ ⟫ f ⟨ _ , γ ⟩') $⟨ ≤-refl ⟩
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-id Γ (Γ ⟪ m≤n ⟫ γ)))
    (T ⟪ m≤n , γ ⟫ t))
      ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x ⟩) (rel-id Γ (Γ ⟪ m≤n ⟫ γ))
                      (z $⟨ ≤-refl ⟩
                      subst (λ x → T ⟨ _ , x ⟩) (sym (rel-id Γ (Γ ⟪ m≤n ⟫ γ)))
                      (T ⟪ m≤n , γ ⟫ t)))
              (naturality f m≤n γ) ⟩
  subst (λ x → S ⟨ _ , x ⟩) (rel-id Γ (Γ ⟪ m≤n ⟫ γ))
    (f ⟨ _ , Γ ⟪ m≤n ⟫ γ ⟩' $⟨ ≤-refl ⟩
    subst (λ x → T ⟨ _ , x ⟩) (sym (rel-id Γ (Γ ⟪ m≤n ⟫ γ)))
    (T ⟪ m≤n , γ ⟫ t))
      ≡⟨⟩
  f €⟨ _ , Γ ⟪ m≤n ⟫ γ ⟩ (T ⟪ m≤n , γ ⟫ t) ∎
  where open ≡-Reasoning

app : {Γ : Ctx ℓ} {T S : Ty Γ} → Tm Γ (T ⇛ S) → Tm Γ T → Tm Γ S
term (app {Γ = Γ}{T}{S} f t) = λ n γ → f €⟨ n , γ ⟩ (t ⟨ n , γ ⟩')
naturality (app {Γ = Γ}{T}{S} f t) {m} {n} m≤n γ =
  S ⟪ m≤n , γ ⟫ (f €⟨ n , γ ⟩ (t ⟨ n , γ ⟩'))
    ≡⟨ €-natural f m≤n γ (t ⟨ n , γ ⟩') ⟩
  f €⟨ m , Γ ⟪ m≤n ⟫ γ ⟩ (T ⟪ m≤n , γ ⟫ (t ⟨ n , γ ⟩'))
    ≡⟨ cong (f €⟨ m , Γ ⟪ m≤n ⟫ γ ⟩_) (naturality t m≤n γ) ⟩
  f €⟨ m , Γ ⟪ m≤n ⟫ γ ⟩ (t ⟨ m , Γ ⟪ m≤n ⟫ γ ⟩') ∎
  where open ≡-Reasoning

{-
-- Another approach to the introduction of function types (based on https://arxiv.org/pdf/1805.08684.pdf).
{-
_⇛_ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ → Ty Γ
type (T ⇛ S) = λ n γ → Tm (𝕪 n ,, (T [ to-𝕪⇒* γ ])) (S [ to-𝕪⇒* γ ⊚ π ])
morph (_⇛_ {Γ = Γ} T S) = λ m≤n γ s → helper (s [ (to-𝕪⇒𝕪 m≤n) ⊹ ]')
  where
    helper : ∀ {m n} {m≤n : m ≤ n} {γ : Γ ⟨ n ⟩} →
             Tm (𝕪 m ,, (T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ])) (S [ to-𝕪⇒* γ ⊚ π ] [ (to-𝕪⇒𝕪 m≤n) ⊹ ]) →
             Tm (𝕪 m ,, (T [ to-𝕪⇒* (Γ ⟪ m≤n ⟫ γ) ])) (S [ to-𝕪⇒* (Γ ⟪ m≤n ⟫ γ) ⊚ π ])
    helper {m} {n} {m≤n} {γ} = subst (λ x → Tm (𝕪 m ,, T [ x ]) (S [ x ⊚ π ])) (𝕪-comp m≤n γ) ∘
                               subst (λ x → Tm (𝕪 m ,, x) (S [ to-𝕪⇒* γ ⊚ to-𝕪⇒𝕪 m≤n ⊚ π {T = x}])) (ty-subst-comp T (to-𝕪⇒* γ) (to-𝕪⇒𝕪 m≤n)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ x ])) (sym (⊚-assoc (to-𝕪⇒* γ) (to-𝕪⇒𝕪 m≤n) π)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ to-𝕪⇒* γ ⊚ x ])) (⊹-π-comm (to-𝕪⇒𝕪 m≤n)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ x ])) (⊚-assoc (to-𝕪⇒* γ) π ((to-𝕪⇒𝕪 m≤n) ⊹)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) x) (ty-subst-comp S (to-𝕪⇒* γ ⊚ π) ((to-𝕪⇒𝕪 m≤n) ⊹))
morph-id (T ⇛ S) = {!!}
morph-comp (T ⇛ S) = {!!}
-}
{-
Π : {Γ : Ctx ℓ} (T : Ty Γ) (S : Ty (Γ ,, T)) → Ty Γ
type (Π T S) = λ n γ → Tm (𝕪 n ,, (T [ to-𝕪⇒* γ ])) (S [ to-𝕪⇒* γ ⊹ ])
morph (Π {Γ = Γ} T S) {m = m} m≤n γ s = subst (λ x → Tm (𝕪 m ,, T [ x ]) (S [ x ⊹ ])) (𝕪-comp m≤n γ)
                                        (subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ⊚ to-𝕪⇒𝕪 m≤n ]) (S [ x ])) {!!} {!s [ (to-𝕪⇒𝕪 m≤n) ⊹ ]'!})
{-  where
    helper : ∀ {m n} {m≤n : m ≤ n} {γ : Γ ⟨ n ⟩} →
             Tm (𝕪 m ,, (T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ])) (S [ to-𝕪⇒* γ ⊹ ] [ to-𝕪⇒𝕪 m≤n ⊹ ]) →
             Tm (𝕪 m ,, (T [ to-𝕪⇒* (Γ ⟪ m≤n ⟫ γ) ])) (S [ to-𝕪⇒* (Γ ⟪ m≤n ⟫ γ) ⊹ ])
    helper {m} {n} {m≤n} {γ} = {!subst (λ x → Tm (𝕪 m ,, T [ x ]) (S [ x ⊚ π ])) (𝕪-comp m≤n γ) ∘
                               subst (λ x → Tm (𝕪 m ,, x) (S [ to-𝕪⇒* γ ⊚ to-𝕪⇒𝕪 m≤n ⊚ π {T = x}])) (ty-subst-comp T (to-𝕪⇒* γ) (to-𝕪⇒𝕪 m≤n)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ x ])) (sym (⊚-assoc (to-𝕪⇒* γ) (to-𝕪⇒𝕪 m≤n) π)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ to-𝕪⇒* γ ⊚ x ])) (⊹-π-comm (to-𝕪⇒𝕪 m≤n)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ x ])) (⊚-assoc (to-𝕪⇒* γ) π ((to-𝕪⇒𝕪 m≤n) ⊹))!} ∘
                               {!subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) x) (ty-subst-comp S (to-𝕪⇒* γ ⊹) (to-𝕪⇒𝕪 m≤n ⊹))!}-}
morph-id (Π T S) = {!!}
morph-comp (Π T S) = {!!}
-}
{-
module _ {Γ : Ctx ℓ} {T S : Ty Γ} where
  lam : Tm (Γ ,, T) (S [ π ]) → Tm Γ (T ⇛ S)
  term (lam b) = λ n γ → subst (λ x → Tm (𝕪 n ,, T [ to-𝕪⇒* γ ]) (S [ x ])) (⊹-π-comm (to-𝕪⇒* γ))
                                (subst (λ x → Tm (𝕪 n ,, T [ to-𝕪⇒* γ ]) x) (ty-subst-comp S π (to-𝕪⇒* γ ⊹))
                                       (b [ to-𝕪⇒* γ ⊹ ]'))
  naturality (lam b) = {!!}

  ap : Tm Γ (T ⇛ S) → Tm (Γ ,, T) (S [ π ])
  term (ap f) = λ n γ → {!term f!}
  naturality (ap f) = {!!}

  app : Tm Γ (T ⇛ S) → Tm Γ T → Tm Γ S
  app f t = {!ap f [ ? ]'!}
-}
-}
