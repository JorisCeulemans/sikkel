module CwF-Structure where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
open import Function hiding (_⟨_⟩_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers

infixl 15 _,,_
infix 10 _⇒_
infix 15 _⟨_,_⟩
infixr 11 _⟪_,_⟫_
infixl 20 _⊚_

--------------------------------------------------
-- Contexts and substitutions + category structure
--------------------------------------------------

record Ctx ℓ : Set (lsuc ℓ) where
  constructor MkCtx
  field
    set : ℕ → Set ℓ
    rel : ∀ {m n} → m ≤ n → set n → set m
    rel-id : ∀ {n} (γ : set n) → rel (≤-refl) γ ≡ γ
    rel-comp : ∀ {k m n} (k≤m : k ≤ m) (m≤n : m ≤ n) (γ : set n) → rel (≤-trans k≤m m≤n) γ ≡ rel k≤m (rel m≤n γ)
open Ctx public

_⟨_⟩ : Ctx ℓ → ℕ → Set ℓ
Γ ⟨ n ⟩ = set Γ n

_⟪_⟫ : (Γ : Ctx ℓ) (ineq : m ≤ n) → Γ ⟨ n ⟩ → Γ ⟨ m ⟩
Γ ⟪ ineq ⟫ = rel Γ ineq

_⟪_⟫_ : (Γ : Ctx ℓ) (ineq : m ≤ n) → Γ ⟨ n ⟩ → Γ ⟨ m ⟩
Γ ⟪ ineq ⟫ γ = (Γ ⟪ ineq ⟫) γ

record _⇒_ {ℓ} (Δ Γ : Ctx ℓ) : Set ℓ where
  constructor MkSubst
  field
    func : ∀ {n} → Δ ⟨ n ⟩ → Γ ⟨ n ⟩
    naturality : ∀ {m n} {m≤n : m ≤ n} (δ : Δ ⟨ n ⟩) → Γ ⟪ m≤n ⟫ (func δ) ≡ func (Δ ⟪ m≤n ⟫ δ)
open _⇒_ public

to-subst-eq : {Δ Γ : Ctx ℓ} {σ τ : Δ ⇒ Γ} →
              ({n : ℕ} (δ : Δ ⟨ n ⟩) → func σ δ ≡ func τ δ) →
              σ ≡ τ
to-subst-eq e = cong₂-d MkSubst
                        (funextI (funext λ δ → e δ))
                        (funextI (funextI (funextI (funext λ _ → uip _ _))))

id-subst : (Γ : Ctx ℓ) → Γ ⇒ Γ
func (id-subst Γ) = id
naturality (id-subst Γ) = λ _ → refl

_⊚_ : {Δ Γ Θ : Ctx ℓ} → Γ ⇒ Θ → Δ ⇒ Γ → Δ ⇒ Θ
func (τ ⊚ σ) = func τ ∘ func σ
naturality (_⊚_ {Δ = Δ}{Γ}{Θ} τ σ) {m≤n = m≤n} δ =
  Θ ⟪ m≤n ⟫ (func τ (func σ δ)) ≡⟨ naturality τ (func σ δ) ⟩
  func τ (Γ ⟪ m≤n ⟫ func σ δ)   ≡⟨ cong (func τ) (naturality σ δ) ⟩
  func τ (func σ (Δ ⟪ m≤n ⟫ δ)) ∎
  where open ≡-Reasoning

⊚-id-substʳ : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) → σ ⊚ id-subst Δ ≡ σ
⊚-id-substʳ σ = to-subst-eq (λ δ → refl)

⊚-id-substˡ : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) → id-subst Γ ⊚ σ ≡ σ
⊚-id-substˡ σ = to-subst-eq (λ δ → refl)

⊚-assoc : {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx ℓ} (σ₃₄ : Γ₃ ⇒ Γ₄) (σ₂₃ : Γ₂ ⇒ Γ₃) (σ₁₂ : Γ₁ ⇒ Γ₂) → (σ₃₄ ⊚ σ₂₃) ⊚ σ₁₂ ≡ σ₃₄ ⊚ (σ₂₃ ⊚ σ₁₂)
⊚-assoc σ₃₄ σ₂₃ σ₁₂ = to-subst-eq (λ δ → refl)

-- The following proofs are needed to define function types in Hofmann style
-- In each of the proofs, the idea is to rewrite the different substitutions as one subst with a more complex equality proof
-- and then apply uip.
ctx-≤-trans-assoc : (Γ : Ctx ℓ) {k≤l : k ≤ l} {l≤m : l ≤ m} {m≤n : m ≤ n}
                    (A : Γ ⟨ k ⟩ → Set ℓ') {γ : Γ ⟨ n ⟩} {a : A (Γ ⟪ ≤-trans k≤l (≤-trans l≤m m≤n) ⟫ γ)} →
                    subst (λ x → A x) (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ))
                          (subst (λ x → A x) (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ) a)
                    ≡
                    subst (λ x → A x) (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))
                          (subst (λ x → A x) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
                                 (subst (λ x → A (Γ ⟪ x ⟫ γ)) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)) a))
ctx-≤-trans-assoc Γ {k≤l}{l≤m}{m≤n} A {γ}{a} =
  subst (λ x → A x) (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ))
    (subst (λ x → A x) (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ) a)
      ≡⟨ subst-subst (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ) ⟩
  subst (λ x → A x) (trans (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ)
                                (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ)))
        a
      ≡⟨ cong (λ z → subst (λ x → A x) z a)
              (uip (trans (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ)
                          (cong (Γ ⟪ k≤l ⟫) (rel-comp Γ l≤m m≤n γ)))
                   _) ⟩
  subst (λ x → A x) (trans (cong (λ x → Γ ⟪ x ⟫ γ) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
                                (trans (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
                                       (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))))
        a
      ≡⟨ sym (subst-subst (cong (λ x → Γ ⟪ x ⟫ γ) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))) ⟩
  subst (λ x → A x) (trans (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
                                (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ)))
    (subst (λ x → A x) (cong (λ x → Γ ⟪ x ⟫ γ) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))) a)
      ≡⟨ cong (subst (λ x → A x) (trans (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
                                         (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))))
              (sym (subst-∘ (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))) ⟩
  subst (λ x → A x) (trans (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
                            (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ)))
    (subst (λ x → A (Γ ⟪ x ⟫ γ)) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)) a)
      ≡⟨ sym (subst-subst (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)) ⟩
  subst (λ x → A x) (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))
    (subst (λ x → A x) (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ)
    (subst (λ x → A (Γ ⟪ x ⟫ γ)) (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)) a)) ∎
  where open ≡-Reasoning

-- The following result can also be proved using the previous one, but it would probably not be much shorter
ctx-≤-trans-sym-assoc : (Γ : Ctx ℓ) {k≤l : k ≤ l} {l≤m : l ≤ m} {m≤n : m ≤ n}
                        (A : Γ ⟨ k ⟩ → Set ℓ') {γ : Γ ⟨ n ⟩} {a : A (Γ ⟪ k≤l ⟫ (Γ ⟪ l≤m ⟫ (Γ ⟪ m≤n ⟫ γ)))} →
                        subst (λ x → A x) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ))
                          (subst (λ x → A x) (cong (Γ ⟪ k≤l ⟫) (sym (rel-comp Γ l≤m m≤n γ))) a)
                        ≡
                        subst (λ x → A (Γ ⟪ x ⟫ γ)) (sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
                          (subst (λ x → A x) (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ))
                          (subst (λ x → A x) (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))) a))
ctx-≤-trans-sym-assoc Γ {k≤l}{l≤m}{m≤n} A {γ}{a} =
  subst (λ x → A x) (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ))
    (subst (λ x → A x) (cong (Γ ⟪ k≤l ⟫) (sym (rel-comp Γ l≤m m≤n γ))) a)
      ≡⟨ subst-subst (cong (Γ ⟪ k≤l ⟫) (sym (rel-comp Γ l≤m m≤n γ))) ⟩
  subst (λ x → A x)
        (trans (cong (Γ ⟪ k≤l ⟫) (sym (rel-comp Γ l≤m m≤n γ)))
               (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ)))
        a
      ≡⟨ cong (λ z → subst (λ x → A x) z a)
              (uip (trans (cong (Γ ⟪ k≤l ⟫) (sym (rel-comp Γ l≤m m≤n γ)))
                          (sym (rel-comp Γ k≤l (≤-trans l≤m m≤n) γ)))
                   _) ⟩
  subst (λ x → A x)
        (trans (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ)))
               (trans (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ))
                      (cong (λ x → Γ ⟪ x ⟫ γ) (sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))))))
        a
      ≡⟨ sym (subst-subst (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ)))) ⟩
  subst (λ x → A x) (trans (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ))
                                (cong (λ x → Γ ⟪ x ⟫ γ) (sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))))
    (subst (λ x → A x) (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))) a)
      ≡⟨ sym (subst-subst (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ))) ⟩
  subst (λ x → A x) (cong (λ x → Γ ⟪ x ⟫ γ) (sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n))))
    (subst (λ x → A x) (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ))
    (subst (λ x → A x) (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))) a))
      ≡⟨ sym (subst-∘ (sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))) ⟩
  subst (λ x → A (Γ ⟪ x ⟫ γ)) (sym (≤-irrelevant (≤-trans k≤l (≤-trans l≤m m≤n)) (≤-trans (≤-trans k≤l l≤m) m≤n)))
    (subst (λ x → A x) (sym (rel-comp Γ (≤-trans k≤l l≤m) m≤n γ))
    (subst (λ x → A x) (sym (rel-comp Γ k≤l l≤m (Γ ⟪ m≤n ⟫ γ))) a)) ∎
  where open ≡-Reasoning

ctx-≤-trans-right-id : (Γ : Ctx ℓ) {m≤n : m ≤ n}
                       (A : Γ ⟨ m ⟩ → Set ℓ') {γ : Γ ⟨ n ⟩} {a : A (Γ ⟪ ≤-trans m≤n ≤-refl ⟫ γ)} →
                       subst (λ x → A x) (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))
                         (subst (λ x → A x) (rel-comp Γ m≤n ≤-refl γ) a) ≡
                       subst (λ x → A (Γ ⟪ x ⟫ γ)) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n) a
ctx-≤-trans-right-id Γ {m≤n} A {γ} {a} =
  subst (λ x → A x) (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))
    (subst (λ x → A x) (rel-comp Γ m≤n ≤-refl γ) a)
      ≡⟨ subst-subst (rel-comp Γ m≤n ≤-refl γ) ⟩
  subst (λ x → A x) (trans (rel-comp Γ m≤n ≤-refl γ)
                            (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ)))
    a
      ≡⟨ cong (λ z → subst (λ x → A x) z a) (uip _ (cong (Γ ⟪_⟫ γ) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n))) ⟩
  subst (λ x → A x) (cong (Γ ⟪_⟫ γ) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)) a
      ≡⟨ sym (subst-∘ (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)) ⟩
  subst (λ x → A (Γ ⟪ x ⟫ γ)) (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n) a ∎
  where open ≡-Reasoning

-- Again, we can prove this using ctx-≤-trans-right-id, but the resulting proof would be equally long.
ctx-≤-trans-sym-right-id : (Γ : Ctx ℓ) {m≤n : m ≤ n}
                           (A : Γ ⟨ m ⟩ → Set ℓ') {γ : Γ ⟨ n ⟩} {a : A (Γ ⟪ m≤n ⟫ γ)} →
                           subst (λ x → A x) (sym (rel-comp Γ m≤n ≤-refl γ))
                             (subst (λ x → A x) (sym (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))) a) ≡
                           subst (λ x → A (Γ ⟪ x ⟫ γ)) (sym (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)) a
ctx-≤-trans-sym-right-id Γ {m≤n} A {γ} {a} =
  subst (λ x → A x) (sym (rel-comp Γ m≤n ≤-refl γ))
    (subst (λ x → A x) (sym (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))) a)
      ≡⟨ subst-subst (sym (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ))) ⟩
  subst (λ x → A x) (trans (sym (cong (Γ ⟪ m≤n ⟫) (rel-id Γ γ)))
                            (sym (rel-comp Γ m≤n ≤-refl γ)))
    a
      ≡⟨ cong (λ z → subst (λ x → A x) z a) (uip _ (cong (Γ ⟪_⟫ γ) (sym (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)))) ⟩
  subst (λ x → A x) (cong (Γ ⟪_⟫ γ) (sym (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n))) a
      ≡⟨ sym (subst-∘ (sym (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n))) ⟩
  subst (λ x → A (Γ ⟪ x ⟫ γ)) (sym (≤-irrelevant (≤-trans m≤n ≤-refl) m≤n)) a ∎
  where open ≡-Reasoning

ctx-≤-trans-left-id : (Γ : Ctx ℓ) {m≤n : m ≤ n}
                      (A : Γ ⟨ m ⟩ → Set ℓ') {γ : Γ ⟨ n ⟩} {a : A (Γ ⟪ ≤-trans ≤-refl m≤n ⟫ γ)} →
                      subst (λ x → A x) (rel-id Γ (Γ ⟪ m≤n ⟫ γ))
                        (subst (λ x → A x) (rel-comp Γ ≤-refl m≤n γ) a) ≡
                      subst (λ x → A (Γ ⟪ x ⟫ γ)) (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n) a
ctx-≤-trans-left-id Γ {m≤n} A {γ} {a} =
  subst (λ x → A x) (rel-id Γ (Γ ⟪ m≤n ⟫ γ))
    (subst (λ x → A x) (rel-comp Γ ≤-refl m≤n γ) a)
      ≡⟨ subst-subst (rel-comp Γ ≤-refl m≤n γ) ⟩
  subst (λ x → A x) (trans (rel-comp Γ ≤-refl m≤n γ)
                            (rel-id Γ (Γ ⟪ m≤n ⟫ γ)))
    a
      ≡⟨ cong (λ z → subst (λ x → A x) z a) (uip _ (cong (Γ ⟪_⟫ γ) (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n))) ⟩
  subst (λ x → A x) (cong (Γ ⟪_⟫ γ) (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n)) a
      ≡⟨ sym (subst-∘ (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n)) ⟩
  subst (λ x → A (Γ ⟪ x ⟫ γ)) (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n) a ∎
  where open ≡-Reasoning

-- Again, we can prove this using ctx-≤-trans-left-id, but the resulting proof would be equally long.
ctx-≤-trans-sym-left-id : (Γ : Ctx ℓ) {m≤n : m ≤ n}
                          (A : Γ ⟨ m ⟩ → Set ℓ') {γ : Γ ⟨ n ⟩} {a : A (Γ ⟪ m≤n ⟫ γ)} →
                          subst (λ x → A x) (sym (rel-comp Γ ≤-refl m≤n γ))
                            (subst (λ x → A x) (sym (rel-id Γ (Γ ⟪ m≤n ⟫ γ))) a) ≡
                          subst (λ x → A (Γ ⟪ x ⟫ γ)) (sym (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n)) a
ctx-≤-trans-sym-left-id Γ {m≤n} A {γ} {a} =
  subst (λ x → A x) (sym (rel-comp Γ ≤-refl m≤n γ))
    (subst (λ x → A x) (sym (rel-id Γ (Γ ⟪ m≤n ⟫ γ))) a)
      ≡⟨ subst-subst (sym (rel-id Γ (Γ ⟪ m≤n ⟫ γ))) ⟩
  subst (λ x → A x) (trans (sym (rel-id Γ (Γ ⟪ m≤n ⟫ γ)))
                            (sym (rel-comp Γ ≤-refl m≤n γ)))
    a
      ≡⟨ cong (λ z → subst (λ x → A x) z a) (uip _ (cong (Γ ⟪_⟫ γ) (sym (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n)))) ⟩
  subst (λ x → A x) (cong (Γ ⟪_⟫ γ) (sym (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n))) a
      ≡⟨ sym (subst-∘ (sym (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n))) ⟩
  subst (λ x → A (Γ ⟪ x ⟫ γ)) (sym (≤-irrelevant (≤-trans ≤-refl m≤n) m≤n)) a ∎
  where open ≡-Reasoning


--------------------------------------------------
-- Types
--------------------------------------------------

record Ty {ℓ} (Γ : Ctx ℓ) : Set (lsuc ℓ) where
  constructor MkTy
  field
    type : (n : ℕ) (γ : Γ ⟨ n ⟩) → Set ℓ
    morph : ∀ {m n} (m≤n : m ≤ n) (γ : Γ ⟨ n ⟩) → type n γ → type m (Γ ⟪ m≤n ⟫ γ)
    morph-id : ∀ {n} {γ : Γ ⟨ n ⟩} (t : type n γ) →
               subst (λ x → type n x) (rel-id Γ γ) (morph ≤-refl γ t) ≡ t
    morph-comp : ∀ {k m n} (k≤m : k ≤ m) (m≤n : m ≤ n) {γ : Γ ⟨ n ⟩} (t : type n γ) →
                 subst (λ x → type k x) (rel-comp Γ k≤m m≤n γ) (morph (≤-trans k≤m m≤n) γ t) ≡ morph k≤m (Γ ⟪ m≤n ⟫ γ) (morph m≤n γ t)
open Ty public

_⟨_,_⟩ : {Γ : Ctx ℓ} → Ty Γ → (n : ℕ) → Γ ⟨ n ⟩ → Set ℓ
T ⟨ n , γ ⟩ = type T n γ

_⟪_,_⟫ : {Γ : Ctx ℓ} (T : Ty Γ) (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ → T ⟨ m , Γ ⟪ ineq ⟫ γ ⟩
T ⟪ ineq , γ ⟫ = morph T ineq γ

_⟪_,_⟫_ : {Γ : Ctx ℓ} (T : Ty Γ) (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ → T ⟨ m , Γ ⟪ ineq ⟫ γ ⟩
T ⟪ ineq , γ ⟫ t = (T ⟪ ineq , γ ⟫) t

{- TODO: see if it is a good idea using the following way to prove equality of types
   + uniform way to prove type equality
   - using funext to show that type T ≡ type S where refl can be used most of the time
to-ty-eq : {Γ : Ctx ℓ} {T S : Ty Γ} →
           (et : (n : ℕ) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ ≡ S ⟨ n , γ ⟩) →
           ({m n : ℕ} (m≤n : m ≤ n) (γ : Γ ⟨ n ⟩) (t : T ⟨ n , γ ⟩) →
               subst id (et m (Γ ⟪ m≤n ⟫ γ)) (T ⟪ m≤n , γ ⟫ t) ≡ S ⟪ m≤n , γ ⟫ subst id (et n γ) t) →
           T ≡ S
to-ty-eq et em = cong₄-d MkTy
                         (funext λ n → funext λ γ → et n γ)
                         {!!}
                         {!!}
                         {!!}
-}

_[_] : {Δ Γ : Ctx ℓ} → Ty Γ → Δ ⇒ Γ → Ty Δ
type (T [ σ ]) = λ n δ → T ⟨ n , func σ δ ⟩
morph (T [ σ ]) m≤n δ t = subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (T ⟪ m≤n , func σ δ ⟫ t)
morph-id (_[_] {Δ = Δ}{Γ} T σ) {n} {δ} t = proof
  where
     open ≡-Reasoning
     abstract
       proof =
         subst (λ x → T ⟨ _ , func σ x ⟩) (rel-id Δ δ) (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (T ⟪ ≤-refl , func σ δ ⟫ t))
           ≡⟨ subst-∘ (rel-id Δ δ) ⟩
         subst (λ x → T ⟨ _ , x ⟩) (cong (func σ) (rel-id Δ δ)) (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (T ⟪ ≤-refl , func σ δ ⟫ t))
           ≡⟨ subst-subst (naturality σ δ) ⟩
         subst (λ x → T ⟨ _ , x ⟩) (trans (naturality σ δ) (cong (func σ) (rel-id Δ δ))) (T ⟪ ≤-refl , func σ δ ⟫ t)
           ≡⟨ cong (λ y → subst (λ x → T ⟨ _ , x ⟩) y (T ⟪ ≤-refl , func σ δ ⟫ t)) (uip _ (rel-id Γ (func σ δ))) ⟩
             -- Currently this equality is proven using uip. In a setting without uip, we would need to impose an extra coherence requirement
             -- on substitutions, ensuring that trans (naturality σ) (cong (func σ ∘_) (rel-id Δ)) ≡ cong (_∘ func σ) (rel-id Γ).
         subst (λ x → T ⟨ _ , x ⟩) (rel-id Γ (func σ δ)) (T ⟪ ≤-refl , func σ δ ⟫ t)
           ≡⟨ morph-id T t ⟩
         t ∎
morph-comp (_[_] {Δ = Δ}{Γ} T σ) k≤m m≤n {δ} t = proof
  where
     open ≡-Reasoning
     abstract
       proof =
         subst (λ x → T ⟨ _ , func σ x ⟩) (rel-comp Δ k≤m m≤n δ)
           (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ)
             (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
           ≡⟨ subst-∘ (rel-comp Δ k≤m m≤n δ) ⟩
         subst (λ x → T ⟨ _ , x ⟩) (cong (func σ) (rel-comp Δ k≤m m≤n δ))
           (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ)
             (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
           ≡⟨ subst-subst (naturality σ δ) ⟩
         subst (λ x → T ⟨ _ , x ⟩)
           (trans (naturality σ δ) (cong (func σ) (rel-comp Δ k≤m m≤n δ)))
             (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t)
           ≡⟨ cong (λ y → subst (λ x → T ⟨ _ , x ⟩) y (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
                   (uip (trans (naturality σ δ) (cong (func σ) (rel-comp Δ k≤m m≤n δ))) _) ⟩
           -- Again, without uip we would need to include an extra coherence law for substitutions.
         subst (λ x → T ⟨ _ , x ⟩)
           (trans (trans (rel-comp Γ k≤m m≤n (func σ δ)) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ))) (naturality σ (Δ ⟪ m≤n ⟫ δ)))
             (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t)
           ≡⟨ sym (subst-subst (trans (rel-comp Γ k≤m m≤n (func σ δ)) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ)))) ⟩
         subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))
           (subst (λ x → T ⟨ _ , x ⟩) (trans (rel-comp Γ k≤m m≤n (func σ δ)) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ)))
             (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
           ≡⟨ cong (subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))) (sym (subst-subst (rel-comp Γ k≤m m≤n (func σ δ)))) ⟩
         subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))
           (subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ))
             (subst (λ x → T ⟨ _ , x ⟩) (rel-comp Γ k≤m m≤n (func σ δ))
               (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t)))
           ≡⟨ cong (λ y → subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ)) (subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ)) y))
                   (morph-comp T k≤m m≤n t) ⟩
         subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))
           (subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ))
             (T ⟪ k≤m , Γ ⟪ m≤n ⟫ (func σ δ) ⟫ (T ⟪ m≤n , func σ δ ⟫ t)))
           ≡⟨ cong (subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))) (sym (subst-∘ (naturality σ δ))) ⟩
         subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))
           (subst (λ x → T ⟨ _ , Γ ⟪ k≤m ⟫ x ⟩) (naturality σ δ)
             (T ⟪ k≤m , Γ ⟪ m≤n ⟫ (func σ δ) ⟫ (T ⟪ m≤n , func σ δ ⟫ t)))
           ≡⟨ cong (subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ)))
                   (weak-subst-application (λ x y → T ⟪ k≤m , x ⟫ y) (naturality σ δ)) ⟩
         subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))
           (T ⟪ k≤m , func σ (Δ ⟪ m≤n ⟫ δ) ⟫
             (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (T ⟪ m≤n , func σ δ ⟫ t))) ∎

abstract
  ty-subst-id : {Γ : Ctx ℓ} (T : Ty Γ) → T [ id-subst Γ ] ≡ T
  ty-subst-id T = cong₂-d (MkTy _ _)
                          (funextI (funextI (funext (λ _ → uip _ _))))
                          (funextI (funextI (funextI (funext λ _ → funext λ _ → funextI (funext λ _ → uip _ _)))))

  ty-subst-comp : {Δ Γ Θ : Ctx ℓ} (T : Ty Θ) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → T [ τ ] [ σ ] ≡ T [ τ ⊚ σ ]
  ty-subst-comp T τ σ = cong₃-d (MkTy _)
    (funextI (funextI (funext λ ineq → funext λ δ → funext λ t →
        subst (λ x → T ⟨ _ , func τ x ⟩) (naturality σ δ)
        (subst (λ x → T ⟨ _ , x ⟩) (naturality τ (func σ δ))
         (T ⟪ ineq , func τ (func σ δ) ⟫ t))
         ≡⟨ subst-∘ (naturality σ δ)  ⟩
        subst (λ x → T ⟨ _ , x ⟩) (cong (func τ) (naturality σ δ))
        (subst (λ x → T ⟨ _ , x ⟩) (naturality τ (func σ δ))
         (T ⟪ ineq , func τ (func σ δ) ⟫ t))
         ≡⟨ subst-subst (naturality τ (func σ δ))  ⟩
        subst (λ x → T ⟨ _ , x ⟩)
          (trans (naturality τ (func σ δ)) (cong (func τ) (naturality σ δ)))
          (T ⟪ ineq , func τ (func σ δ) ⟫ t)
         ≡⟨ cong
              (λ p →
                 subst (λ x → T ⟨ _ , x ⟩) p
                 (T ⟪ ineq , func τ (func σ δ) ⟫ t))
              (cong (trans (naturality τ (func σ δ))) (sym (trans-reflʳ _))) ⟩
         subst (λ x → T ⟨ _ , x ⟩)
           (trans (naturality τ (func σ δ))
             (trans (cong (func τ) (naturality σ δ))
           refl))
         (T ⟪ ineq , func τ (func σ δ) ⟫ t) ∎
        )))
    (funextI (funextI (funext (λ _ → uip _ _))))
    (funextI (funextI (funextI (funext λ _ → funext λ _ → funextI (funext λ _ → uip _ _)))))
    where open ≡-Reasoning


--------------------------------------------------
-- Terms
--------------------------------------------------

record Tm {ℓ} (Γ : Ctx ℓ) (T : Ty Γ) : Set ℓ where
  constructor MkTm
  field
    term : (n : ℕ) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
    naturality : ∀ {m n} (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟪ ineq , γ ⟫ (term n γ) ≡ term m (Γ ⟪ ineq ⟫ γ)
open Tm public

_⟨_,_⟩' : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → (n : ℕ) → (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
t ⟨ n , γ ⟩' = term t n γ

_⟪_,_⟫' : {Γ : Ctx ℓ} {T : Ty Γ} (t : Tm Γ T) (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟪ ineq , γ ⟫ (t ⟨ n , γ ⟩') ≡ t ⟨ m , Γ ⟪ ineq ⟫ γ ⟩'
t ⟪ ineq , γ ⟫' = naturality t ineq γ

_[_]' : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ])
term (t [ σ ]') = λ n δ → t ⟨ n , func σ δ ⟩'
naturality (_[_]'  {Δ = Δ}{Γ}{T} t σ) ineq δ = 
  (T [ σ ]) ⟪ ineq , δ ⟫ (t [ σ ]' ⟨ _ , δ ⟩')
    ≡⟨⟩
  subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (T ⟪ ineq , func σ δ ⟫ (t ⟨ _ , func σ δ ⟩'))
    ≡⟨ cong (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ)) (t ⟪ ineq , func σ δ ⟫') ⟩
  subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (t ⟨ _ , Γ ⟪ ineq ⟫ (func σ δ) ⟩')
    ≡⟨ cong-d (λ x → t ⟨ _ , x ⟩') (naturality σ δ) ⟩
  t ⟨ _ , func σ (Δ ⟪ ineq ⟫ δ) ⟩'
    ≡⟨⟩
  t [ σ ]' ⟨ _ , Δ ⟪ ineq ⟫ δ ⟩' ∎
  where open ≡-Reasoning

tm-subst-id : {Γ : Ctx ℓ} {T : Ty Γ} (t : Tm Γ T) → subst (Tm Γ) (ty-subst-id T) (t [ id-subst Γ ]') ≡ t
tm-subst-id {Γ = Γ}{T = T} t = cong₂-d MkTm
  (term (subst (Tm Γ) (ty-subst-id T) (t [ id-subst Γ ]'))
      ≡⟨ sym (weak-subst-application {B = Tm Γ} (λ x y → term y) (ty-subst-id T)) ⟩
    subst (λ x → (n : ℕ) (γ : Γ ⟨ n ⟩) → x ⟨ n , γ ⟩) (ty-subst-id T) (term (t [ id-subst Γ ]'))
      ≡⟨ subst-∘ (ty-subst-id T) ⟩
    subst (λ x → (n : ℕ) (γ : Γ ⟨ n ⟩) → x n γ) (cong type (ty-subst-id T)) (term (t [ id-subst Γ ]'))
      ≡⟨ cong {A = type T ≡ type T} (λ y → subst (λ x → (n : ℕ) (γ : Γ ⟨ n ⟩) → x n γ) y (term t)) (uip _ _) ⟩
    subst (λ x → (n : ℕ) (γ : Γ ⟨ n ⟩) → x n γ) {x = type T} refl (term t)
      ≡⟨⟩
    term t ∎)
  (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
  where open ≡-Reasoning

tm-subst-comp : {Δ Γ Θ : Ctx ℓ} {T : Ty Θ} (t : Tm Θ T) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                subst (Tm Δ) (ty-subst-comp T τ σ) (t [ τ ]' [ σ ]') ≡ t [ τ ⊚ σ ]'
tm-subst-comp {Δ = Δ}{Γ}{T = T} t τ σ = cong₂-d MkTm
  (term (subst (Tm Δ) (ty-subst-comp T τ σ) (t [ τ ]' [ σ ]'))
      ≡⟨ sym (weak-subst-application {B = Tm Δ} (λ x y → term y) (ty-subst-comp T τ σ)) ⟩
    subst (λ x → (n : ℕ) (δ : Δ ⟨ n ⟩) → x ⟨ n , δ ⟩) (ty-subst-comp T τ σ) (term (t [ τ ]' [ σ ]'))
      ≡⟨ subst-∘ (ty-subst-comp T τ σ) ⟩
    subst (λ x → (n : ℕ) (δ : Δ ⟨ n ⟩) → x n δ) (cong type (ty-subst-comp T τ σ)) (term (t [ τ ]' [ σ ]'))
      ≡⟨ cong {A = (λ n δ → type T n (func τ (func σ δ))) ≡ (λ n δ → type T n (func τ (func σ δ)))}
              (λ y → subst (λ x → (n : ℕ) (δ : Δ ⟨ n ⟩) → x n δ) y (term (t [ τ ]' [ σ ]')))
              {x = cong type (ty-subst-comp T τ σ)}
              {y = refl}
              (uip _ _) ⟩
    subst (λ x → (n : ℕ) (δ : Δ ⟨ n ⟩) → x n δ) {x = type (T [ τ ⊚ σ ])} refl (term (t [ τ ⊚ σ ]'))
      ≡⟨⟩
    term (t [ τ ⊚ σ ]') ∎)
  (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
  where open ≡-Reasoning


--------------------------------------------------
-- The empty context
--------------------------------------------------

◇ : Ctx ℓ
set ◇ = λ _ → Lift _ ⊤
rel ◇ = λ _ _ → lift tt
rel-id ◇ = λ _ → refl
rel-comp ◇ = λ _ _ _ → refl

empty-subst : (Γ : Ctx ℓ) → Γ ⇒ ◇
func (empty-subst Γ) = λ _ → lift tt
naturality (empty-subst Γ) = λ _ → refl

empty-subst-terminal : (Γ : Ctx ℓ) (σ : Γ ⇒ ◇) → σ ≡ empty-subst Γ
empty-subst-terminal Γ σ = to-subst-eq (λ δ → refl)


--------------------------------------------------
-- Context extension
--------------------------------------------------

_,,_ : (Γ : Ctx ℓ) (T : Ty Γ) → Ctx ℓ
set (Γ ,, T) n = Σ[ γ ∈ Γ ⟨ n ⟩ ] (T ⟨ n , γ ⟩)
rel (Γ ,, T) ineq [ γ , t ] = [ Γ ⟪ ineq ⟫ γ , T ⟪ ineq , γ ⟫ t ]
rel-id (Γ ,, T) [ γ , t ] = to-Σ-eq (rel-id Γ γ) (morph-id T t)
rel-comp (Γ ,, T) k≤m m≤n [ γ , t ] = to-Σ-eq (rel-comp Γ k≤m m≤n γ) (morph-comp T k≤m m≤n t)

π : {Γ : Ctx ℓ} {T : Ty Γ} → Γ ,, T ⇒ Γ
func π = proj₁
naturality π = λ _ → refl

ξ : {Γ : Ctx ℓ} {T : Ty Γ} → Tm (Γ ,, T) (T [ π {T = T} ])
term ξ = λ _ → proj₂
naturality ξ = λ _ _ → refl

from-ext-subst : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Δ ⇒ Γ ,, T → Σ[ σ ∈ Δ ⇒ Γ ] (Tm Δ (T [ σ ]))
from-ext-subst {Δ = Δ}{Γ}{T} τ = [ π ⊚ τ , subst (Tm Δ) (ty-subst-comp T π τ) (ξ [ τ ]') ]

to-ext-subst-Σ : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Σ[ σ ∈ Δ ⇒ Γ ] (Tm Δ (T [ σ ])) → Δ ⇒ Γ ,, T
to-ext-subst-Σ {T = T} [ σ , t ] = MkSubst (λ δ → [ func σ δ , t ⟨ _ , δ ⟩' ])
                                           (λ δ → to-Σ-eq (naturality σ δ)
                                                           (naturality t _ δ))

to-ext-subst : {Δ Γ : Ctx ℓ} {T : Ty Γ} (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ]) → Δ ⇒ Γ ,, T
to-ext-subst σ t = to-ext-subst-Σ [ σ , t ]

ctx-ext-left-inverse : {Δ Γ : Ctx ℓ} {T : Ty Γ} (p : Σ[ σ ∈ Δ ⇒ Γ ] (Tm Δ (T [ σ ]))) → from-ext-subst (to-ext-subst-Σ p) ≡ p
ctx-ext-left-inverse {Δ = Δ} {T = T} [ σ , t ] = to-Σ-eq (to-subst-eq (λ δ → refl))
                                                         (cong₂-d MkTm proof
                                                                       (funextI (funextI (funext λ _ → funext λ _ → uip _ _))))
  where
    open ≡-Reasoning
    α = to-subst-eq (λ δ → refl)
    β = subst (Tm Δ) (ty-subst-comp T π (to-ext-subst-Σ [ σ , t ])) (ξ [ to-ext-subst-Σ [ σ , t ] ]')
    proof = term (subst (λ x → Tm Δ (T [ x ])) α β)
                ≡⟨ cong term {y = subst (Tm Δ) (cong (T [_]) α)
                                        (subst (Tm Δ) (ty-subst-comp T π (to-ext-subst-Σ [ σ , t ]))
                                               (ξ [ to-ext-subst-Σ [ σ , t ] ]'))}
                        (subst-∘ {f = λ x → T [ x ]} α {p = β}) ⟩
              term (subst (Tm Δ) (cong (T [_]) α) (subst (Tm Δ) (ty-subst-comp T π (to-ext-subst-Σ [ σ , t ])) (ξ [ to-ext-subst-Σ [ σ , t ] ]')))
                ≡⟨ cong term {x = subst (Tm Δ) (cong (T [_]) α)
                                        (subst (Tm Δ) (ty-subst-comp T π (to-ext-subst-Σ [ σ , t ]))
                                               (ξ [ to-ext-subst-Σ [ σ , t ] ]'))}
                             {y = subst (Tm Δ) (trans (ty-subst-comp T π (to-ext-subst-Σ [ σ , t ])) (cong (T [_]) α))
                                        (ξ [ to-ext-subst-Σ [ σ , t ] ]')}
                             (subst-subst (ty-subst-comp T π (to-ext-subst-Σ [ σ , t ]))) ⟩
              term (subst (Tm Δ) (trans (ty-subst-comp T π (to-ext-subst-Σ [ σ , t ])) (cong (T [_]) α)) (ξ [ to-ext-subst-Σ [ σ , t ] ]'))
                ≡⟨ sym (weak-subst-application {B = Tm Δ} (λ x y → term y) (trans (ty-subst-comp T π (to-ext-subst-Σ [ σ , t ])) (cong (T [_]) α))) ⟩
              subst (λ z → (n : ℕ) (γ : Δ ⟨ n ⟩) → z ⟨ n , γ ⟩) (trans (ty-subst-comp T π (to-ext-subst-Σ [ σ , t ])) (cong (T [_]) α)) (term (ξ [ to-ext-subst-Σ [ σ , t ] ]'))
                ≡⟨ subst-∘ (trans (ty-subst-comp T π (to-ext-subst-Σ [ σ , t ])) (cong (T [_]) α)) ⟩
              subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) (cong type (trans (ty-subst-comp T π (to-ext-subst-Σ [ σ , t ])) (cong (T [_]) α))) (term (ξ [ to-ext-subst-Σ [ σ , t ] ]'))
                ≡⟨ cong (λ x → subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) x (term (ξ [ to-ext-subst-Σ [ σ , t ] ]')))
                        {x = cong type (trans (ty-subst-comp T π (to-ext-subst-Σ [ σ , t ])) (cong (T [_]) α))}
                        {y = refl}
                        (uip _ _) ⟩
              term t ∎

ctx-ext-right-inverse : {Δ Γ : Ctx ℓ} {T : Ty Γ} (τ : Δ ⇒ Γ ,, T) → to-ext-subst-Σ (from-ext-subst τ) ≡ τ
ctx-ext-right-inverse {Δ = Δ} {T = T} τ = to-subst-eq (λ δ →
  cong [ proj₁ (func τ δ) ,_] (term (proj₂ (from-ext-subst τ)) _ δ
    ≡⟨⟩
  term (subst (Tm Δ) (ty-subst-comp T π τ) (ξ [ τ ]')) _ δ
    ≡⟨ cong (λ z → z _ δ) (sym (weak-subst-application {B = Tm Δ} (λ x y → term y) (ty-subst-comp T π τ))) ⟩
  subst (λ x → (m : ℕ) (δ' : Δ ⟨ m ⟩) → x ⟨ m , δ' ⟩) (ty-subst-comp T π τ) (term (ξ [ τ ]')) _ δ
    ≡⟨ cong (λ z → z _ δ) {x = subst (λ x → (m : ℕ) (δ' : Δ ⟨ m ⟩) → x ⟨ m , δ' ⟩) (ty-subst-comp T π τ) (term (ξ [ τ ]'))}
            (subst-∘ (ty-subst-comp T π τ)) ⟩
  subst (λ x → (m : ℕ) (δ' : Δ ⟨ m ⟩) → x m δ') (cong type (ty-subst-comp T π τ)) (term (ξ [ τ ]')) _ δ
    ≡⟨ cong (λ z → subst (λ x → (m : ℕ) (δ' : Δ ⟨ m ⟩) → x m δ') z (term (ξ [ τ ]')) _ δ)
            {x = cong type (ty-subst-comp T π τ)}
            {y = refl}
            (uip _ _) ⟩
  proj₂ (func τ δ) ∎))
  where
    open ≡-Reasoning

π-ext-comp : {Δ Γ : Ctx ℓ} {T : Ty Γ} (σ : Δ ⇒ Γ ) (t : Tm Δ (T [ σ ])) →
             π ⊚ to-ext-subst σ t ≡ σ
π-ext-comp σ t = to-subst-eq (λ δ → refl)

π-ext-comp-ty-subst : {Δ Γ : Ctx ℓ} {T : Ty Γ} (σ : Δ ⇒ Γ ) (t : Tm Δ (T [ σ ])) (S : Ty Γ) →
                      S [ π ] [ to-ext-subst σ t ] ≡ S [ σ ]
π-ext-comp-ty-subst σ t S =
  S [ π ] [ to-ext-subst σ t ]
    ≡⟨ ty-subst-comp S π (to-ext-subst σ t) ⟩
  S [ π ⊚ to-ext-subst σ t ]
    ≡⟨ cong (S [_]) (π-ext-comp σ t) ⟩
  S [ σ ] ∎
  where open ≡-Reasoning

_⌈_⌋ : {Γ : Ctx ℓ} {T S : Ty Γ} → Tm (Γ ,, T) (S [ π ]) → Tm Γ T → Tm Γ S
_⌈_⌋ {Γ = Γ}{T}{S} s t = subst (Tm Γ) proof (s [ to-ext-subst  (id-subst Γ) (t [ id-subst Γ ]') ]')
  where
    open ≡-Reasoning
    proof : S [ π ] [ to-ext-subst (id-subst Γ) (t [ id-subst Γ ]') ] ≡ S
    proof =
      S [ π ] [ to-ext-subst (id-subst Γ) (t [ id-subst Γ ]') ]
        ≡⟨ π-ext-comp-ty-subst (id-subst Γ) (t [ id-subst Γ ]') S ⟩
      S [ id-subst Γ ]
        ≡⟨ ty-subst-id S ⟩
      S ∎

_⊹ : {Δ Γ : Ctx ℓ} {T : Ty Γ} (σ : Δ ⇒ Γ) → Δ ,, T [ σ ] ⇒ Γ ,, T
_⊹ {Δ = Δ} {T = T} σ = to-ext-subst (σ ⊚ π) (subst (Tm (Δ ,, T [ σ ])) (ty-subst-comp T σ π) ξ)

module _ {Δ Γ : Ctx ℓ} {T : Ty Γ} (σ : Δ ⇒ Γ) where
  ⊹-π-comm : π {T = T} ⊚ (σ ⊹) ≡ σ ⊚ π
  ⊹-π-comm = to-subst-eq (λ δ → refl)
{-
⊹-tm-comp : {Δ Γ Θ : Ctx ℓ} (T : Ty Θ) (S : Ty (Θ ,, T)) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
            Tm (Δ ,, T [ τ ] [ σ ]) (S [ τ ⊹ ] [ σ ⊹ ]) → Tm (Δ ,, T [ τ ⊚ σ ]) (S [ (τ ⊚ σ) ⊹ ])
term (⊹-tm-comp T S τ σ s) n [ δ , t ] = {!s ⟨ n , ? ⟩'!}
naturality (⊹-tm-comp T S τ σ s) = {!!}
-}
