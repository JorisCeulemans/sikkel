module CwF-Structure.Contexts where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Unit using (⊤; tt)
open import Function hiding (_⟨_⟩_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers

infix 10 _⇒_
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
naturality (_⊚_ {Δ = Δ}{Γ}{Θ} τ σ) {m≤n = m≤n} δ = trans (naturality τ (func σ δ))
                                                          (cong (func τ) (naturality σ δ))
{-  Θ ⟪ m≤n ⟫ (func τ (func σ δ)) ≡⟨ naturality τ (func σ δ) ⟩
    func τ (Γ ⟪ m≤n ⟫ func σ δ)   ≡⟨ cong (func τ) (naturality σ δ) ⟩
    func τ (func σ (Δ ⟪ m≤n ⟫ δ)) ∎
    where open ≡-Reasoning -}

⊚-id-substʳ : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) → σ ⊚ id-subst Δ ≡ σ
⊚-id-substʳ σ = to-subst-eq (λ δ → refl)

⊚-id-substˡ : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) → id-subst Γ ⊚ σ ≡ σ
⊚-id-substˡ σ = to-subst-eq (λ δ → refl)

⊚-assoc : {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx ℓ} (σ₃₄ : Γ₃ ⇒ Γ₄) (σ₂₃ : Γ₂ ⇒ Γ₃) (σ₁₂ : Γ₁ ⇒ Γ₂) → (σ₃₄ ⊚ σ₂₃) ⊚ σ₁₂ ≡ σ₃₄ ⊚ (σ₂₃ ⊚ σ₁₂)
⊚-assoc σ₃₄ σ₂₃ σ₁₂ = to-subst-eq (λ δ → refl)

{-
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
-}


--------------------------------------------------
-- The empty context
--------------------------------------------------

◇ : Ctx ℓ
set ◇ = λ _ → Lift _ ⊤
rel ◇ = λ _ _ → lift tt
rel-id ◇ = λ _ → refl
rel-comp ◇ = λ _ _ _ → refl

!◇ : (Γ : Ctx ℓ) → Γ ⇒ ◇
func (!◇ Γ) = λ _ → lift tt
naturality (!◇ Γ) = λ _ → refl

◇-terminal : (Γ : Ctx ℓ) (σ τ : Γ ⇒ ◇) → σ ≡ τ
◇-terminal Γ σ τ = to-subst-eq (λ δ → refl)
