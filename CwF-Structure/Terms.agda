module CwF-Structure.Terms where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types

infix 1 _≅ᵗᵐ_

--------------------------------------------------
-- Terms
--------------------------------------------------

record Tm {ℓ} (Γ : Ctx ℓ) (T : Ty Γ) : Set ℓ where
  constructor MkTm
  field
    term : (n : ℕ) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
    naturality : ∀ {m n} (ineq : m ≤ n) {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} (eq : Γ ⟪ ineq ⟫ γn ≡ γm) →
                 T ⟪ ineq , eq ⟫ (term n γn) ≡ term m γm
open Tm public

_⟨_,_⟩' : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → (n : ℕ) → (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
t ⟨ n , γ ⟩' = term t n γ

{-
_⟪_,_⟫' : {Γ : Ctx ℓ} {T : Ty Γ} (t : Tm Γ T) (ineq : m ≤ n) →
          {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} (eq : Γ ⟪ ineq ⟫ γn ≡ γm) →
          T ⟪ ineq , eq ⟫ (t ⟨ n , γn ⟩') ≡ t ⟨ m , γm ⟩'
t ⟪ ineq , eq ⟫' = naturality t ineq eq
-}

record _≅ᵗᵐ_ {Γ : Ctx ℓ} {T : Ty Γ} (t s : Tm Γ T) : Set ℓ where
  field
    eq : ∀ {n} γ → t ⟨ n , γ ⟩' ≡ s ⟨ n , γ ⟩'
open _≅ᵗᵐ_ public

≅ᵗᵐ-refl : {Γ : Ctx ℓ} {T : Ty Γ} {t : Tm Γ T} → t ≅ᵗᵐ t
eq (≅ᵗᵐ-refl {t = t}) _ = refl

≅ᵗᵐ-sym : {Γ : Ctx ℓ} {T : Ty Γ} {t s : Tm Γ T} → t ≅ᵗᵐ s → s ≅ᵗᵐ t
eq (≅ᵗᵐ-sym t=s) γ = sym (eq t=s γ)

≅ᵗᵐ-trans : {Γ : Ctx ℓ} {T : Ty Γ} {t1 t2 t3 : Tm Γ T} → t1 ≅ᵗᵐ t2 → t2 ≅ᵗᵐ t3 → t1 ≅ᵗᵐ t3
eq (≅ᵗᵐ-trans t1=t2 t2=t3) γ = trans (eq t1=t2 γ) (eq t2=t3 γ)

module ≅ᵗᵐ-Reasoning {Γ : Ctx ℓ} {T : Ty Γ} where
  infix  3 _∎
  infixr 2 _≅⟨⟩_ step-≅ step-≅˘
  infix  1 begin_

  begin_ : ∀ {t s : Tm Γ T} → t ≅ᵗᵐ s → t ≅ᵗᵐ s
  begin_ t=s = t=s

  _≅⟨⟩_ : ∀ (t {s} : Tm Γ T) → t ≅ᵗᵐ s → t ≅ᵗᵐ s
  _ ≅⟨⟩ t=s = t=s

  step-≅ : ∀ (t1 {t2 t3} : Tm Γ T) → t1 ≅ᵗᵐ t2 → t2 ≅ᵗᵐ t3 → t1 ≅ᵗᵐ t3
  step-≅ _ t1≅t2 t2≅t3 = ≅ᵗᵐ-trans t1≅t2 t2≅t3

  step-≅˘ : ∀ (t1 {t2 t3} : Tm Γ T) → t2 ≅ᵗᵐ t3 → t2 ≅ᵗᵐ t1 → t1 ≅ᵗᵐ t3
  step-≅˘ _ t2≅t3 t2≅t1 = ≅ᵗᵐ-trans (≅ᵗᵐ-sym t2≅t1) t2≅t3

  _∎ : ∀ (t : Tm Γ T) → t ≅ᵗᵐ t
  _∎ _ = ≅ᵗᵐ-refl

  syntax step-≅  t1 t2≅t3 t1≅t2 = t1 ≅⟨  t1≅t2 ⟩ t2≅t3
  syntax step-≅˘ t1 t2≅t3 t2≅t1 = t1 ≅˘⟨ t2≅t1 ⟩ t2≅t3

convert-term : {Γ : Ctx ℓ} {T S : Ty Γ} → (T ↣ S) → Tm Γ T → Tm Γ S
term (convert-term η t) n γ = func η (t ⟨ n , γ ⟩')
naturality (convert-term {T = T}{S} η t) m≤n eγ =
  begin
    S ⟪ m≤n , eγ ⟫ func η (t ⟨ _ , _ ⟩')
  ≡⟨ naturality η _ ⟩
    func η (T ⟪ m≤n , eγ ⟫ (t ⟨ _ , _ ⟩'))
  ≡⟨ cong (func η) (naturality t _ _) ⟩
    func η (t ⟨ _ , _ ⟩') ∎
  where open ≡-Reasoning

_[_]' : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ])
term (t [ σ ]') n δ = t ⟨ n , func σ δ ⟩'
naturality (t [ σ ]') m≤n eγ = naturality t m≤n _

tm-subst-id : {Γ : Ctx ℓ} {T : Ty Γ} (t : Tm Γ T) → convert-term (from (ty-subst-id T)) (t [ id-subst Γ ]') ≅ᵗᵐ t
eq (tm-subst-id t) _ = refl

{-
tm-subst-id : {Γ : Ctx ℓ} {T : Ty Γ} (t : Tm Γ T) → subst (Tm Γ) (ty-subst-id T) (t [ id-subst Γ ]') ≡ t
tm-subst-id {Γ = Γ}{T} t = cong₂-d MkTm term-proof naturality-proof
  where
    open ≡-Reasoning
    -- Structuring the proof like this (separate term-proof and naturality-proof, specifying lhs and rhs in
    -- naturality-proof) reduces type-checking time with ±10s).
    term-proof = (term (subst (Tm Γ) (ty-subst-id T) (t [ id-subst Γ ]'))
        ≡⟨ sym (weak-subst-application {B = Tm Γ} (λ x y → term y) (ty-subst-id T)) ⟩
      subst (λ x → (n : ℕ) (γ : Γ ⟨ n ⟩) → x ⟨ n , γ ⟩) (ty-subst-id T) (term (t [ id-subst Γ ]'))
        ≡⟨ subst-∘ (ty-subst-id T) ⟩
      subst (λ x → (n : ℕ) (γ : Γ ⟨ n ⟩) → x n γ) (cong type (ty-subst-id T)) (term (t [ id-subst Γ ]'))
        ≡⟨ cong {A = type T ≡ type T} (λ y → subst (λ x → (n : ℕ) (γ : Γ ⟨ n ⟩) → x n γ) y (term t)) (uip _ _) ⟩
      subst (λ x → (n : ℕ) (γ : Γ ⟨ n ⟩) → x n γ) {x = type T} refl (term t)
        ≡⟨⟩
      term t ∎)
    naturality-proof = subst _ term-proof (λ {m}{n} → naturality (subst (Tm Γ) (ty-subst-id T) (t [ id-subst Γ ]')) {m} {n})
        ≡⟨ funextI (funextI (funext λ _ → funextI (funextI (funext λ _ → uip _ _)))) ⟩
      (λ {m}{n} → naturality t {m} {n}) ∎
-}

tm-subst-comp : {Δ Γ Θ : Ctx ℓ} {T : Ty Θ} (t : Tm Θ T) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                convert-term (from (ty-subst-comp T τ σ)) (t [ τ ]' [ σ ]') ≅ᵗᵐ t [ τ ⊚ σ ]'
eq (tm-subst-comp t τ σ) _ = refl

{-
tm-subst-comp : {Δ Γ Θ : Ctx ℓ} {T : Ty Θ} (t : Tm Θ T) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                subst (Tm Δ) (ty-subst-comp T τ σ) (t [ τ ]' [ σ ]') ≡ t [ τ ⊚ σ ]'
tm-subst-comp {Δ = Δ}{Γ}{T = T} t τ σ = cong₂-d MkTm term-proof naturality-proof
  where
    open ≡-Reasoning
    term-proof = (term (subst (Tm Δ) (ty-subst-comp T τ σ) (t [ τ ]' [ σ ]'))
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
    naturality-proof = subst _ term-proof (λ {m}{n} → naturality (subst (Tm Δ) (ty-subst-comp T τ σ) (t [ τ ]' [ σ ]')) {m} {n})
        ≡⟨ funextI (funextI (funext λ _ → funextI (funextI (funext λ _ → uip _ _)))) ⟩
      (λ {m}{n} → naturality (t [ τ ⊚ σ ]') {m} {n}) ∎

{- This does not lead to reduced type-checking time.
  (term (subst (Tm Δ) ζ η)
      ≡⟨ sym (weak-subst-application {B = Tm Δ} (λ x y → term y) ζ) ⟩
    subst (λ x → (n : ℕ) (δ : Δ ⟨ n ⟩) → x ⟨ n , δ ⟩) ζ (term η)
      ≡⟨ subst-∘ ζ ⟩
    subst (λ x → (n : ℕ) (δ : Δ ⟨ n ⟩) → x n δ) (cong type ζ) (term η)
      ≡⟨ cong {A = (λ n δ → type T n (func τ (func σ δ))) ≡ (λ n δ → type T n (func τ (func σ δ)))}
              (λ y → subst (λ x → (n : ℕ) (δ : Δ ⟨ n ⟩) → x n δ) y (term η))
              {x = cong type ζ}
              {y = refl}
              (uip _ _) ⟩
    subst (λ x → (n : ℕ) (δ : Δ ⟨ n ⟩) → x n δ) {x = type (T [ τ ⊚ σ ])} refl (term (t [ τ ⊚ σ ]'))
      ≡⟨⟩
    term (t [ τ ⊚ σ ]') ∎)
  (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
  where
    open ≡-Reasoning
    ζ = ty-subst-comp T τ σ
    η = t [ τ ]' [ σ ]'
-}
-}

tm-subst-cong-tm : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) {T : Ty Γ} {t s : Tm Γ T} → t ≅ᵗᵐ s → t [ σ ]' ≅ᵗᵐ s [ σ ]'
eq (tm-subst-cong-tm σ t=s) δ = eq t=s (func σ δ)

convert-subst-commute : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) {T S : Ty Γ} (η : T ↣ S) (t : Tm Γ T) → convert-term (ty-subst-map σ η) (t [ σ ]') ≅ᵗᵐ (convert-term η t) [ σ ]'
eq (convert-subst-commute σ η t) δ = refl
