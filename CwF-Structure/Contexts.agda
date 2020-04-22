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

-- TODO: currently to-subst-eq is implemented using funext for the func-part, although this
-- equality holds definitionally (so refl could be used instead of funext refl). Check whether
-- this has an impact on computational behaviour.
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
{-
More detailed version of the above naturality proof. We do not use this as it inserts
refl at the end (and trans eq refl is not definitionally equal to eq).
  Θ ⟪ m≤n ⟫ (func τ (func σ δ)) ≡⟨ naturality τ (func σ δ) ⟩
  func τ (Γ ⟪ m≤n ⟫ func σ δ)   ≡⟨ cong (func τ) (naturality σ δ) ⟩
  func τ (func σ (Δ ⟪ m≤n ⟫ δ)) ∎
  where open ≡-Reasoning
-}

⊚-id-substʳ : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) → σ ⊚ id-subst Δ ≡ σ
⊚-id-substʳ σ = to-subst-eq (λ δ → refl)

⊚-id-substˡ : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) → id-subst Γ ⊚ σ ≡ σ
⊚-id-substˡ σ = to-subst-eq (λ δ → refl)

⊚-assoc : {Γ₁ Γ₂ Γ₃ Γ₄ : Ctx ℓ} (σ₃₄ : Γ₃ ⇒ Γ₄) (σ₂₃ : Γ₂ ⇒ Γ₃) (σ₁₂ : Γ₁ ⇒ Γ₂) → (σ₃₄ ⊚ σ₂₃) ⊚ σ₁₂ ≡ σ₃₄ ⊚ (σ₂₃ ⊚ σ₁₂)
⊚-assoc σ₃₄ σ₂₃ σ₁₂ = to-subst-eq (λ δ → refl)

-- The following proof is needed to define composition of morphisms in the category of elements
-- of Γ and is used e.g. in the definition of types (in general) and function types.
strong-rel-comp : (Γ : Ctx ℓ) {k≤m : k ≤ m} {m≤n : m ≤ n} {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} {γk : Γ ⟨ k ⟩} →
                  (eq-nm : Γ ⟪ m≤n ⟫ γn ≡ γm) (eq-mk : Γ ⟪ k≤m ⟫ γm ≡ γk) →
                  Γ ⟪ ≤-trans k≤m m≤n ⟫ γn ≡ γk
strong-rel-comp Γ {k≤m}{m≤n}{γn} eq-nm eq-mk = trans (rel-comp Γ k≤m m≤n γn)
                                                     (trans (cong (Γ ⟪ k≤m ⟫) eq-nm)
                                                            eq-mk)


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
