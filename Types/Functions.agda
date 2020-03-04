module Types.Functions where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Function hiding (_⟨_⟩_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

open import Helpers
open import CwF-Structure

--------------------------------------------------
-- (Non-dependent) function types
--------------------------------------------------

record PresheafFunc {ℓ} {Γ : Ctx ℓ} (T S : Ty Γ) (n : ℕ) (γ : Γ ⟨ n ⟩) : Set ℓ where
  constructor MkFunc
  field
    _$⟨_⟩_ : ∀ {m} (ineq : m ≤ n) → T ⟨ m , Γ ⟪ ineq ⟫ γ ⟩ → S ⟨ m , Γ ⟪ ineq ⟫ γ ⟩
    naturality : ∀ {k m} (k≤m : k ≤ m) (m≤n : m ≤ n) →
                 _$⟨_⟩_ (≤-trans k≤m m≤n) ∘ subst (λ x → T ⟨ k , x γ ⟩) (sym (rel-comp Γ k≤m m≤n)) ∘ T ⟪ k≤m , Γ ⟪ m≤n ⟫ γ ⟫ ≡
                   subst (λ x → S ⟨ k , x γ ⟩) (sym (rel-comp Γ k≤m m≤n)) ∘ (S ⟪ k≤m , Γ ⟪ m≤n ⟫ γ ⟫) ∘ _$⟨_⟩_ m≤n
  infix 13 _$⟨_⟩_
open PresheafFunc public

to-pshfun-eq : {Γ : Ctx ℓ} {T S : Ty Γ} {n : ℕ} {γ : Γ ⟨ n ⟩} {f g : PresheafFunc T S n γ} →
               (∀ {m} (ineq : m ≤ n) t → f $⟨ ineq ⟩ t ≡ g $⟨ ineq ⟩ t) →
               f ≡ g
to-pshfun-eq e = cong₂-d MkFunc
  (funextI (funext (λ ineq → funext λ t → e ineq t)))
  (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))

lower-presheaffunc : ∀ {m n} {Γ : Ctx ℓ} {T S : Ty Γ} (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → PresheafFunc T S n γ → PresheafFunc T S m (Γ ⟪ ineq ⟫ γ)
lower-presheaffunc {m = m}{n}{Γ}{T}{S} m≤n γ f = MkFunc g g-nat
  where
    g : ∀ {k} (k≤m : k ≤ m) → T ⟨ k , Γ ⟪ k≤m ⟫ (Γ ⟪ m≤n ⟫ γ) ⟩ → S ⟨ k , Γ ⟪ k≤m ⟫ (Γ ⟪ m≤n ⟫ γ) ⟩
    g k≤m = subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ k≤m m≤n)
            ∘ f $⟨ ≤-trans k≤m m≤n ⟩_
            ∘ subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ k≤m m≤n))
    open ≡-Reasoning
    abstract
      g-nat : ∀ {k l} (k≤l : k ≤ l) (l≤m : l ≤ m) → _
      g-nat k≤l l≤m = funext λ t →
        subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
          (f $⟨ ≤-trans (≤-trans k≤l l≤m) m≤n ⟩
          subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n))
          (subst (λ x → T ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-comp Γ k≤l l≤m))
          (T ⟪ k≤l , Γ ⟪ l≤m ⟫ (Γ ⟪ m≤n ⟫ γ) ⟫ t)))
            ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
                                  (f $⟨ ≤-trans (≤-trans k≤l l≤m) m≤n ⟩ z))
                    (sym (subst-subst-sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))) ⟩
        subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
          (f $⟨ ≤-trans (≤-trans k≤l l≤m) m≤n ⟩
          subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
          (subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
          (subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n))
          (subst (λ x → T ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-comp Γ k≤l l≤m))
          (T ⟪ k≤l , Γ ⟪ l≤m ⟫ (Γ ⟪ m≤n ⟫ γ) ⟫ t)))))
            ≡⟨ cong (subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n))
                    (sym (weak-subst-application (λ x → f $⟨ x ⟩_) (≤-irrelevant _ _))) ⟩
        subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
          (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
          (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
          subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
          (subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n))
          (subst (λ x → T ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-comp Γ k≤l l≤m))
          (T ⟪ k≤l , Γ ⟪ l≤m ⟫ (Γ ⟪ m≤n ⟫ γ) ⟫ t)))))
            ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
                            (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
                            (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩ z)))
                    (sym (ctx-≤-trans-sym-assoc Γ (λ y → T ⟨ _ , y ⟩))) ⟩
        subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
          (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
          (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
          subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n)))
          (subst (λ x → T ⟨ _ , Γ ⟪ k≤l ⟫ (x γ) ⟩) (sym (rel-comp Γ l≤m m≤n))
          (T ⟪ k≤l , Γ ⟪ l≤m ⟫ (Γ ⟪ m≤n ⟫ γ) ⟫ t))))
            ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
                            (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
                            (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
                            subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n))) z)))
                    (weak-subst-application (λ x → T ⟪ k≤l , x γ ⟫) (sym (rel-comp Γ l≤m m≤n))) ⟩
        subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
          (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
          (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
          subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n)))
          (T ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
          subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ l≤m m≤n)) t)))
            ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
                           (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
                           (z
                           (subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ l≤m m≤n)) t))))
                    (naturality f k≤l (≤-trans l≤m m≤n)) ⟩
        subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
          (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
          (subst (λ x → S ⟨ _ , x γ ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n)))
          (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
          (f $⟨ ≤-trans l≤m m≤n ⟩
          subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ l≤m m≤n)) t))))
            ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n) z)
                    (subst-∘ (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))) ⟩
        subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
          (subst (λ x → S ⟨ _ , x γ ⟩) (cong (Γ ⟪_⟫) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
          (subst (λ x → S ⟨ _ , x γ ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n)))
          (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
          (f $⟨ ≤-trans l≤m m≤n ⟩
          subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ l≤m m≤n)) t))))
            ≡⟨ subst-subst (cong (Γ ⟪_⟫) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))) ⟩
        subst (λ x → S ⟨ _ , x γ ⟩)
              (trans (cong (Γ ⟪_⟫) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
                     (rel-comp Γ (≤-trans k≤l l≤m) m≤n))
          (subst (λ x → S ⟨ _ , x γ ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n)))
          (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
          (f $⟨ ≤-trans l≤m m≤n ⟩
          subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ l≤m m≤n)) t)))
            ≡⟨ subst-subst (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n))) ⟩
        subst (λ x → S ⟨ _ , x γ ⟩)
              (trans (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n)))
              (trans (cong (Γ ⟪_⟫) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
                     (rel-comp Γ (≤-trans k≤l l≤m) m≤n)))
          (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
          (f $⟨ ≤-trans l≤m m≤n ⟩
          subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ l≤m m≤n)) t))
            ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x γ ⟩) z
                           (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
                           (f $⟨ ≤-trans l≤m m≤n ⟩
                           subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ l≤m m≤n)) t)))
                    (uip _ (trans (cong (Γ ⟪ k≤l ⟫ ∘_) (rel-comp Γ l≤m m≤n))
                                  (cong (_∘ Γ ⟪ m≤n ⟫) (sym (rel-comp Γ k≤l l≤m))))) ⟩
        subst (λ x → S ⟨ _ , x γ ⟩)
              (trans (cong (Γ ⟪ k≤l ⟫ ∘_) (rel-comp Γ l≤m m≤n))
                     (cong (_∘ Γ ⟪ m≤n ⟫) (sym (rel-comp Γ k≤l l≤m))))
          (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
          (f $⟨ ≤-trans l≤m m≤n ⟩
          subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ l≤m m≤n)) t))
            ≡⟨ sym (subst-subst (cong (Γ ⟪ k≤l ⟫ ∘_) (rel-comp Γ l≤m m≤n))) ⟩
        subst (λ x → S ⟨ _ , x γ ⟩) (cong (_∘ Γ ⟪ m≤n ⟫) (sym (rel-comp Γ k≤l l≤m)))
          (subst (λ x → S ⟨ _ , x γ ⟩) (cong (Γ ⟪ k≤l ⟫ ∘_) (rel-comp Γ l≤m m≤n))
          (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
          (f $⟨ ≤-trans l≤m m≤n ⟩
          subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ l≤m m≤n)) t)))
            ≡⟨ sym (subst-∘ (sym (rel-comp Γ k≤l l≤m))) ⟩
        subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-comp Γ k≤l l≤m))
          (subst (λ x → S ⟨ _ , x γ ⟩) (cong (Γ ⟪ k≤l ⟫ ∘_) (rel-comp Γ l≤m m≤n))
          (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
          (f $⟨ ≤-trans l≤m m≤n ⟩
          subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ l≤m m≤n)) t)))
            ≡⟨ cong (subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-comp Γ k≤l l≤m)))
                    (sym (subst-∘ (rel-comp Γ l≤m m≤n))) ⟩
        subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-comp Γ k≤l l≤m))
          (subst (λ x → S ⟨ _ , Γ ⟪ k≤l ⟫ (x γ) ⟩) (rel-comp Γ l≤m m≤n)
          (S ⟪ k≤l , Γ ⟪ ≤-trans l≤m m≤n ⟫ γ ⟫
          (f $⟨ ≤-trans l≤m m≤n ⟩
          subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ l≤m m≤n)) t)))
            ≡⟨ cong (subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-comp Γ k≤l l≤m)))
                    (weak-subst-application (λ x → S ⟪ k≤l , x γ ⟫) (rel-comp Γ l≤m m≤n)) ⟩
        subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-comp Γ k≤l l≤m))
          (S ⟪ k≤l , Γ ⟪ l≤m ⟫ (Γ ⟪ m≤n ⟫ γ) ⟫
          subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ l≤m m≤n)
          (f $⟨ ≤-trans l≤m m≤n ⟩
          subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ l≤m m≤n)) t)) ∎

_⇛_ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ → Ty Γ
type (_⇛_ {Γ = Γ} T S) = λ n γ → PresheafFunc T S n γ
morph (_⇛_ {Γ = Γ} T S) = lower-presheaffunc
morph-id (_⇛_ {Γ = Γ} T S) = λ γ → funext λ f → to-pshfun-eq λ m≤n t →
  subst (λ x → (T ⇛ S) ⟨ _ , x γ ⟩) (rel-id Γ) ((T ⇛ S) ⟪ ≤-refl , γ ⟫ f) $⟨ m≤n ⟩ t
      ≡⟨ cong (λ z → z t) (sym (weak-subst-application {B = λ x → (T ⇛ S) ⟨ _ , x γ ⟩} (λ x y → y $⟨ m≤n ⟩_) (rel-id Γ))) ⟩
  subst (λ x → T ⟨ _ , Γ ⟪ m≤n ⟫ (x γ) ⟩ → S ⟨ _ , Γ ⟪ m≤n ⟫ (x γ) ⟩) (rel-id Γ) (((T ⇛ S) ⟪ ≤-refl , γ ⟫ f) $⟨ m≤n ⟩_) t
      ≡⟨ function-subst (rel-id Γ) (((T ⇛ S) ⟪ ≤-refl , γ ⟫ f) $⟨ m≤n ⟩_) ⟩
  subst (λ x → S ⟨ _ , Γ ⟪ m≤n ⟫ (x γ) ⟩) (rel-id Γ)
    (((T ⇛ S) ⟪ ≤-refl , γ ⟫ f) $⟨ m≤n ⟩
    (subst (λ x → T ⟨ _ , Γ ⟪ m≤n ⟫ (x γ) ⟩) (sym (rel-id Γ)) t))
      ≡⟨⟩
  subst (λ x → S ⟨ _ , Γ ⟪ m≤n ⟫ (x γ) ⟩) (rel-id Γ)
    (subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ m≤n ≤-refl)
    (f $⟨ ≤-trans m≤n ≤-refl ⟩
    subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ m≤n ≤-refl))
    (subst (λ x → T ⟨ _ , Γ ⟪ m≤n ⟫ (x γ) ⟩) (sym (rel-id Γ)) t)))
      ≡⟨ ctx-≤-trans-right-id Γ (λ x → S ⟨ _ , x ⟩) ⟩
  subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)
    (f $⟨ ≤-trans m≤n ≤-refl ⟩
    subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ m≤n ≤-refl))
    (subst (λ x → T ⟨ _ , Γ ⟪ m≤n ⟫ (x γ) ⟩) (sym (rel-id Γ)) t))
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
morph-comp (_⇛_ {Γ = Γ} T S) = λ l≤m m≤n γ → funext λ f → to-pshfun-eq λ k≤l t →
  (subst (λ x → (T ⇛ S) ⟨ _ , x γ ⟩) (rel-comp Γ l≤m m≤n) ((T ⇛ S) ⟪ ≤-trans l≤m m≤n , γ ⟫ f)) $⟨ k≤l ⟩ t
      ≡⟨ cong (λ z → z t) (sym (weak-subst-application {B = λ x → (T ⇛ S) ⟨ _ , x γ ⟩} (λ x y → y $⟨ k≤l ⟩_) (rel-comp Γ l≤m m≤n))) ⟩
  subst (λ x → T ⟨ _ , Γ ⟪ k≤l ⟫ (x γ) ⟩ → S ⟨ _ , Γ ⟪ k≤l ⟫ (x γ) ⟩) (rel-comp Γ l≤m m≤n) (((T ⇛ S) ⟪ ≤-trans l≤m m≤n , γ ⟫ f) $⟨ k≤l ⟩_) t
      ≡⟨ function-subst (rel-comp Γ l≤m m≤n) (((T ⇛ S) ⟪ ≤-trans l≤m m≤n , γ ⟫ f) $⟨ k≤l ⟩_) ⟩
  subst (λ x → S ⟨ _ , Γ ⟪ k≤l ⟫ (x γ) ⟩) (rel-comp Γ l≤m m≤n)
    (((T ⇛ S) ⟪ ≤-trans l≤m m≤n , γ ⟫ f) $⟨ k≤l ⟩
    (subst (λ x → T ⟨ _ , Γ ⟪ k≤l ⟫ (x γ) ⟩) (sym (rel-comp Γ l≤m m≤n)) t))
      ≡⟨⟩
  subst (λ x → S ⟨ _ , Γ ⟪ k≤l ⟫ (x γ) ⟩) (rel-comp Γ l≤m m≤n)
    (subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ k≤l (≤-trans l≤m m≤n))
    (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
    subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n)))
    (subst (λ x → T ⟨ _ , Γ ⟪ k≤l ⟫ (x γ) ⟩) (sym (rel-comp Γ l≤m m≤n)) t)))
      ≡⟨ ctx-≤-trans-assoc Γ (λ y → S ⟨ _ , y ⟩) ⟩
  subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (rel-comp Γ k≤l l≤m)
    (subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
    (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
    (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
    subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n)))
    (subst (λ x → T ⟨ _ , Γ ⟪ k≤l ⟫ (x γ) ⟩) (sym (rel-comp Γ l≤m m≤n)) t))))
      ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (rel-comp Γ k≤l l≤m)
                      (subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
                      (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
                      (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩ z))))
             (ctx-≤-trans-sym-assoc Γ (λ y → T ⟨ _ , y ⟩)) ⟩
  subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (rel-comp Γ k≤l l≤m)
    (subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
    (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
    (f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) ⟩
    subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
    (subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n))
    (subst (λ x → T ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-comp Γ k≤l l≤m)) t)))))
      ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (rel-comp Γ k≤l l≤m)
                     (subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n) z))
              (weak-subst-application (λ x → f $⟨ x ⟩_) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))) ⟩
  subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (rel-comp Γ k≤l l≤m)
    (subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
    (f $⟨ ≤-trans (≤-trans k≤l l≤m) m≤n ⟩
    subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))
    (subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
    (subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n))
    (subst (λ x → T ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-comp Γ k≤l l≤m)) t)))))
      ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (rel-comp Γ k≤l l≤m)
                     (subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ (≤-trans k≤l l≤m) m≤n)
                     (f $⟨ ≤-trans (≤-trans k≤l l≤m) m≤n ⟩ z)))
              (subst-subst-sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))) ⟩
  ((T ⇛ S) ⟪ l≤m , Γ ⟪ m≤n ⟫ γ ⟫) ((T ⇛ S) ⟪ m≤n , γ ⟫ f) $⟨ k≤l ⟩ t ∎
  where open ≡-Reasoning

lam : {Γ : Ctx ℓ} (T : Ty Γ) {S : Ty Γ} → Tm (Γ ,, T) (S [ π ]) → Tm Γ (T ⇛ S)
term (lam {Γ = Γ} T {S} b) = λ n γ → MkFunc (λ m≤n t → b ⟨ _ , [ Γ ⟪ m≤n ⟫ γ , t ] ⟩')
                                             (λ k≤m m≤n → funext λ t →
  b ⟨ _ , [ Γ ⟪ ≤-trans k≤m m≤n ⟫ γ , subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ k≤m m≤n)) ((T ⟪ k≤m , Γ ⟪ m≤n ⟫ γ ⟫) t) ] ⟩'
    ≡⟨ sym (weak-subst-application (λ x y → b ⟨ _ , [ x γ , y ] ⟩') (sym (rel-comp Γ k≤m m≤n))) ⟩
  subst (λ x → S ⟨ _ , x γ ⟩) (sym (rel-comp Γ k≤m m≤n)) (b ⟨ _ , [ Γ ⟪ k≤m ⟫ (Γ ⟪ m≤n ⟫ γ) , T ⟪ k≤m , Γ ⟪ m≤n ⟫ γ ⟫ t ] ⟩')
    ≡⟨ cong (subst (λ x → S ⟨ _ , x γ ⟩) (sym (rel-comp Γ k≤m m≤n))) (sym (naturality b k≤m [ Γ ⟪ m≤n ⟫ γ , t ])) ⟩
  subst (λ x → S ⟨ _ , x γ ⟩) (sym (rel-comp Γ k≤m m≤n)) (S ⟪ k≤m , Γ ⟪ m≤n ⟫ γ ⟫ (b ⟨ _ , [ Γ ⟪ m≤n ⟫ γ , t ] ⟩')) ∎)
  where open ≡-Reasoning
naturality (lam {Γ = Γ} T {S} b) = λ m≤n γ → to-pshfun-eq (λ k≤m t →
  subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ k≤m m≤n) (b ⟨ _ , [ Γ ⟪ ≤-trans k≤m m≤n ⟫ γ , subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ k≤m m≤n)) t ] ⟩')
    ≡⟨ weak-subst-application (λ x y → b ⟨ _ , [ x γ , y ] ⟩') (rel-comp Γ k≤m m≤n) ⟩
  b ⟨ _ , [ Γ ⟪ k≤m ⟫ (Γ ⟪ m≤n ⟫ γ) , subst (λ x → T ⟨ _ , x γ ⟩) (rel-comp Γ k≤m m≤n) (subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ k≤m m≤n)) t) ] ⟩'
    ≡⟨ cong (λ z → b ⟨ _ , [ Γ ⟪ k≤m ⟫ (Γ ⟪ m≤n ⟫ γ) , z ] ⟩') (subst-subst-sym (rel-comp Γ k≤m m≤n)) ⟩
  b ⟨ _ , [ Γ ⟪ k≤m ⟫ (Γ ⟪ m≤n ⟫ γ) , t ] ⟩' ∎)
  where open ≡-Reasoning

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

app : {Γ : Ctx ℓ} {T S : Ty Γ} → Tm Γ (T ⇛ S) → Tm Γ T → Tm Γ S
term (app {Γ = Γ}{T}{S} f t) = λ n γ → subst (λ x → S ⟨ _ , x γ ⟩) (rel-id Γ)
                                              (f ⟨ n , γ ⟩' $⟨ ≤-refl ⟩ t ⟨ n , Γ ⟪ ≤-refl ⟫ γ ⟩')
naturality (app {Γ = Γ}{T}{S} f t) = λ m≤n γ →
  S ⟪ m≤n , γ ⟫ ((app f t) ⟨ _ , γ ⟩')
      ≡⟨⟩
  S ⟪ m≤n , γ ⟫
    subst (λ x → S ⟨ _ , x γ ⟩) (rel-id Γ)
    (f ⟨ _ , γ ⟩' $⟨ ≤-refl ⟩
    t ⟨ _ , Γ ⟪ ≤-refl ⟫ γ ⟩')
      ≡⟨ sym (weak-subst-application (λ x y → S ⟪ m≤n , x γ ⟫ y) (rel-id Γ)) ⟩
  subst (λ x → S ⟨ _ , Γ ⟪ m≤n ⟫ (x γ) ⟩) (rel-id Γ)
    (S ⟪ m≤n , Γ ⟪ ≤-refl ⟫ γ ⟫
    f ⟨ _ , γ ⟩' $⟨ ≤-refl ⟩
    t ⟨ _ , Γ ⟪ ≤-refl ⟫ γ ⟩')
      ≡⟨ cong (subst (λ x → S ⟨ _ , Γ ⟪ m≤n ⟫ (x γ) ⟩) (rel-id Γ))
              (sym (subst-subst-sym (rel-comp Γ m≤n ≤-refl))) ⟩
  subst (λ x → S ⟨ _ , Γ ⟪ m≤n ⟫ (x γ) ⟩) (rel-id Γ)
    (subst (λ x → S ⟨ _ , x γ ⟩) (rel-comp Γ m≤n ≤-refl)
    (subst (λ x → S ⟨ _ , x γ ⟩) (sym (rel-comp Γ m≤n ≤-refl))
    (S ⟪ m≤n , Γ ⟪ ≤-refl ⟫ γ ⟫
    f ⟨ _ , γ ⟩' $⟨ ≤-refl ⟩
    t ⟨ _ , Γ ⟪ ≤-refl ⟫ γ ⟩')))
      ≡⟨ ctx-≤-trans-right-id Γ (λ x → S ⟨ _ , x ⟩) ⟩
  subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)
    (subst (λ x → S ⟨ _ , x γ ⟩) (sym (rel-comp Γ m≤n ≤-refl))
    (S ⟪ m≤n , Γ ⟪ ≤-refl ⟫ γ ⟫
    f ⟨ _ , γ ⟩' $⟨ ≤-refl ⟩
    t ⟨ _ , Γ ⟪ ≤-refl ⟫ γ ⟩'))
      ≡⟨ cong (subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n))
              (cong-app (sym (naturality (f ⟨ _ , γ ⟩') m≤n ≤-refl)) (t ⟨ _ , Γ ⟪ ≤-refl ⟫ γ ⟩')) ⟩
  subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)
    (f ⟨ _ , γ ⟩' $⟨ ≤-trans m≤n ≤-refl ⟩
    subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ m≤n ≤-refl))
    (T ⟪ m≤n , Γ ⟪ ≤-refl ⟫ γ ⟫
    t ⟨ _ , Γ ⟪ ≤-refl ⟫ γ ⟩'))
      ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)
                      (f ⟨ _ , γ ⟩' $⟨ ≤-trans m≤n ≤-refl ⟩
                      subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ m≤n ≤-refl)) z))
              (naturality t m≤n (rel Γ ≤-refl γ)) ⟩
  subst (λ x → S ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)
    (f ⟨ _ , γ ⟩' $⟨ ≤-trans m≤n ≤-refl ⟩
    subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ m≤n ≤-refl))
    (t ⟨ _ , Γ ⟪ m≤n ⟫ (Γ ⟪ ≤-refl ⟫ γ) ⟩'))
      ≡⟨ weak-subst-application (λ x y → f ⟨ _ , γ ⟩' $⟨ x ⟩ y) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n) ⟩
  f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
    subst (λ x → T ⟨ _ , Γ ⟪ x ⟫ γ ⟩) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)
    (subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ m≤n ≤-refl))
    (t ⟨ _ , Γ ⟪ m≤n ⟫ (Γ ⟪ ≤-refl ⟫ γ) ⟩'))
      ≡⟨ cong (f ⟨ _ , γ ⟩' $⟨ m≤n ⟩_) (sym (ctx-≤-trans-right-id Γ (λ x → T ⟨ _ , x ⟩))) ⟩
  f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
    subst (λ x → T ⟨ _ , Γ ⟪ m≤n ⟫ (x γ) ⟩) (rel-id Γ)
    (subst (λ x → T ⟨ _ , x γ ⟩) (rel-comp Γ m≤n ≤-refl)
    (subst (λ x → T ⟨ _ , x γ ⟩) (sym (rel-comp Γ m≤n ≤-refl))
    (t ⟨ _ , Γ ⟪ m≤n ⟫ (Γ ⟪ ≤-refl ⟫ γ) ⟩')))
      ≡⟨ cong (λ z → f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
                      subst (λ x → T ⟨ _ , Γ ⟪ m≤n ⟫ (x γ) ⟩) (rel-id Γ) z)
              (subst-subst-sym (rel-comp Γ m≤n ≤-refl)) ⟩
  f ⟨ _ , γ ⟩' $⟨ m≤n ⟩
    subst (λ x → T ⟨ _ , Γ ⟪ m≤n ⟫ (x γ) ⟩) (rel-id Γ)
    (t ⟨ _ , Γ ⟪ m≤n ⟫ (Γ ⟪ ≤-refl ⟫ γ) ⟩')
      ≡⟨ cong (f ⟨ _ , γ ⟩' $⟨ m≤n ⟩_) (cong-d (λ x → t ⟨ _ , Γ ⟪ m≤n ⟫ (x γ) ⟩') (rel-id Γ)) ⟩
  f ⟨ _ , γ ⟩' $⟨ m≤n ⟩ t ⟨ _ , Γ ⟪ m≤n ⟫ γ ⟩'
      ≡⟨ func-term-natural f m≤n (t ⟨ _ , Γ ⟪ m≤n ⟫ γ ⟩') ⟩
  subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (rel-id Γ)
    (f ⟨ _ , Γ ⟪ m≤n ⟫ γ ⟩' $⟨ ≤-refl ⟩
    subst (λ x → T ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (sym (rel-id Γ))
    (t ⟨ _ , Γ ⟪ m≤n ⟫ γ ⟩'))
      ≡⟨ cong (λ z → subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (rel-id Γ)
                            (f ⟨ _ , Γ ⟪ m≤n ⟫ γ ⟩' $⟨ ≤-refl ⟩ z))
              (cong-d (λ x → t ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩') (sym (rel-id Γ))) ⟩
  subst (λ x → S ⟨ _ , x (Γ ⟪ m≤n ⟫ γ) ⟩) (rel-id Γ)
    (f ⟨ _ , Γ ⟪ m≤n ⟫ γ ⟩' $⟨ ≤-refl ⟩
    t ⟨ _ , Γ ⟪ ≤-refl ⟫ (Γ ⟪ m≤n ⟫ γ) ⟩')
      ≡⟨⟩
  (app f t) ⟨ _  , Γ ⟪ m≤n ⟫ γ ⟩' ∎
  where open ≡-Reasoning

β-func : {Γ : Ctx ℓ} {T S : Ty Γ}
         (b : Tm (Γ ,, T) (S [ π ])) (t : Tm Γ T) →
         app (lam T b) t ≡ b ⌈ t ⌋
β-func {Γ = Γ}{T}{S} b t = cong₂-d MkTm
  (term (app (lam T b) t)
      ≡⟨ (funext λ n → funext λ γ →
         sym (subst-cong-app (rel-id Γ) (b ⟨ _ , [ Γ ⟪ ≤-refl ⟫ γ , t ⟨ _ , Γ ⟪ ≤-refl ⟫ γ ⟩' ] ⟩'))) ⟩
    (λ n γ → subst (λ x → S ⟨ _ , x ⟩) (cong-app (rel-id Γ) γ)
                    (b ⟨ _ , [ Γ ⟪ ≤-refl ⟫ γ , t ⟨ _ , Γ ⟪ ≤-refl ⟫ γ ⟩' ] ⟩'))
      ≡⟨ (funext λ n → funext λ γ →
         cong-d (λ z → b ⟨ _ , [ z , t ⟨ _ , z ⟩' ] ⟩') (cong-app (rel-id Γ) γ)) ⟩
    term (b [ to-ext-subst (id-subst Γ) (t [ id-subst Γ ]') ]')
      ≡⟨ cong (λ y → subst (λ z → (n : ℕ) (γ : Γ ⟨ n ⟩) → z n γ) y
                             (term (b [ to-ext-subst (id-subst Γ) (t [ id-subst Γ ]') ]')))
              (uip refl (cong type S[π][t]=S)) ⟩
    subst (λ z → (n : ℕ) (γ : Γ ⟨ n ⟩) → z n γ) (cong type S[π][t]=S)
      (term (b [ to-ext-subst (id-subst Γ) (t [ id-subst Γ ]') ]'))
      ≡⟨ sym (subst-∘ S[π][t]=S) ⟩
    subst (λ z → (n : ℕ) (γ : Γ ⟨ n ⟩) → z ⟨ n , γ ⟩) S[π][t]=S
      (term (b [ to-ext-subst (id-subst Γ) (t [ id-subst Γ ]') ]'))
      ≡⟨ weak-subst-application (λ x y → term y) S[π][t]=S ⟩
    term
      (subst (Tm Γ) S[π][t]=S
      (b [ to-ext-subst (id-subst Γ) (t [ id-subst Γ ]') ]')) ∎)
  (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
  where
    open ≡-Reasoning
    S[π][t]=S : S [ π ] [ to-ext-subst (id-subst Γ) (t [ id-subst Γ ]') ] ≡ S
    S[π][t]=S = trans (trans (ty-subst-comp S π (to-ext-subst (id-subst Γ) (t [ id-subst Γ ]')))
                             (trans (cong (_[_] S) (π-ext-comp (id-subst Γ) (t [ id-subst Γ ]'))) refl))
                      (trans (ty-subst-id S) refl)
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
