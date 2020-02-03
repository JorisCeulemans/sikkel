module OmegaPresheafCategory where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
open import Function hiding (_⟨_⟩_)
open import Level renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

variable
  ℓ : Level
  m n : ℕ

infixl 15 _,,_
infix 10 _⇒_

record Ctx ℓ : Set (lsuc ℓ) where
  field
    set : ℕ → Set ℓ
    rel : ∀ {m n} → m ≤ n → set n → set m
--    rel-id : ∀ {n} → rel {n} (≤-refl) ≡ id
--    rel-comp : ∀ {k m n} (k≤m : k ≤ m) (m≤n : m ≤ n) → rel (≤-trans k≤m m≤n) ≡ rel k≤m ∘ rel m≤n
open Ctx

_⟨_⟩ : Ctx ℓ → ℕ → Set ℓ
Γ ⟨ n ⟩ = set Γ n

_⟪_⟫ : (Γ : Ctx ℓ) (ineq : m ≤ n) → Γ ⟨ n ⟩ → Γ ⟨ m ⟩
Γ ⟪ ineq ⟫ = rel Γ ineq

_⟪_⟫_ : (Γ : Ctx ℓ) (ineq : m ≤ n) → Γ ⟨ n ⟩ → Γ ⟨ m ⟩
Γ ⟪ ineq ⟫ γ = (Γ ⟪ ineq ⟫) γ

◇ : Ctx ℓ
set ◇ = λ _ → Lift _ ⊤
rel ◇ = λ _ _ → lift tt

𝕪 : ℕ → Ctx 0ℓ
set (𝕪 n) = λ m → m ≤ n
rel (𝕪 n) = ≤-trans

record _⇒_ {ℓ} (Δ Γ : Ctx ℓ) : Set ℓ where
  field
    func : ∀ {n} → Δ ⟨ n ⟩ → Γ ⟨ n ⟩
    naturality : ∀ {m n ineq} → (Γ ⟪ ineq ⟫) ∘ func {n} ≡ func {m} ∘ (Δ ⟪ ineq ⟫)
open _⇒_

id-subst : (Γ : Ctx ℓ) → Γ ⇒ Γ
func (id-subst Γ) = id
naturality (id-subst Γ) = refl

_⊚_ : {Δ Γ Θ : Ctx ℓ} → Γ ⇒ Θ → Δ ⇒ Γ → Δ ⇒ Θ
func (τ ⊚ σ) = func τ ∘ func σ
naturality (_⊚_ {Δ = Δ}{Γ}{Θ} τ σ) {ineq = ineq} =
  Θ ⟪ ineq ⟫ ∘ func τ ∘ func σ ≡⟨ cong (_∘ func σ) (naturality τ) ⟩
  func τ ∘ Γ ⟪ ineq ⟫ ∘ func σ ≡⟨ cong (func τ ∘_) (naturality σ) ⟩
  func τ ∘ func σ ∘ Δ ⟪ ineq ⟫ ∎
  where open ≡-Reasoning

empty-subst : (Γ : Ctx ℓ) → Γ ⇒ ◇
func (empty-subst Γ) = λ _ → lift tt
naturality (empty-subst Γ) = refl

record Ty {ℓ} (Γ : Ctx ℓ) : Set (lsuc ℓ) where
  field
    type : (n : ℕ) (γ : Γ ⟨ n ⟩) → Set ℓ
    morph : ∀ {m n} (m≤n : m ≤ n) (γ : Γ ⟨ n ⟩) → type n γ → type m (Γ ⟪ m≤n ⟫ γ)
open Ty

_⟨_,_⟩ : {Γ : Ctx ℓ} → Ty Γ → (n : ℕ) → Γ ⟨ n ⟩ → Set ℓ
T ⟨ n , γ ⟩ = type T n γ

_⟪_,_⟫ : {Γ : Ctx ℓ} (T : Ty Γ) (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ → T ⟨ m , Γ ⟪ ineq ⟫ γ ⟩
T ⟪ ineq , γ ⟫ = morph T ineq γ

_⟪_,_⟫_ : {Γ : Ctx ℓ} (T : Ty Γ) (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ → T ⟨ m , Γ ⟪ ineq ⟫ γ ⟩
T ⟪ ineq , γ ⟫ t = (T ⟪ ineq , γ ⟫) t

_[_] : {Δ Γ : Ctx ℓ} → Ty Γ → Δ ⇒ Γ → Ty Δ
type (T [ σ ]) = λ n δ → T ⟨ n , func σ δ ⟩
morph (T [ σ ]) ineq δ rewrite sym (cong-app (naturality σ {ineq = ineq}) δ) = T ⟪ ineq , func σ δ ⟫

subst-comp : {Δ Γ Θ : Ctx ℓ} {T : Ty Θ} {τ : Γ ⇒ Θ} {σ : Δ ⇒ Γ} → T [ τ ] [ σ ] ≡ T [ τ ⊚ σ ]
subst-comp = {!!}

record Tm {ℓ} (Γ : Ctx ℓ) (T : Ty Γ) : Set ℓ where
  field
    term : (n : ℕ) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
    naturality : ∀ {m n} (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟪ ineq , γ ⟫ (term n γ) ≡ term m (Γ ⟪ ineq ⟫ γ)
open Tm

_⟨_,_⟩' : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → (n : ℕ) → (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
t ⟨ n , γ ⟩' = term t n γ

_⟪_,_⟫' : {Γ : Ctx ℓ} {T : Ty Γ} (t : Tm Γ T) (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟪ ineq , γ ⟫ (t ⟨ n , γ ⟩') ≡ t ⟨ m , Γ ⟪ ineq ⟫ γ ⟩'
t ⟪ ineq , γ ⟫' = naturality t ineq γ

_[_]' : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ])
term (t [ σ ]') = λ n δ → t ⟨ n , func σ δ ⟩'
naturality (t [ σ ]') ineq δ rewrite sym (cong-app (naturality σ {ineq = ineq}) δ) = t ⟪ ineq , func σ δ ⟫'

_,,_ : (Γ : Ctx ℓ) (T : Ty Γ) → Ctx ℓ
set (Γ ,, T) = λ n → Σ[ γ ∈ Γ ⟨ n ⟩ ] (T ⟨ n , γ ⟩)
rel (Γ ,, T) = λ { ineq [ γ , t ] → [ Γ ⟪ ineq ⟫ γ , T ⟪ ineq , γ ⟫ t ] }

π : {Γ : Ctx ℓ} {T : Ty Γ} → Γ ,, T ⇒ Γ
func π = proj₁
naturality π = refl

ξ : {Γ : Ctx ℓ} {T : Ty Γ} → Tm (Γ ,, T) (T [ π ])
term ξ = λ { n [ γ , t ] → t }
naturality ξ = λ _ _ → refl

ctx-ext-subst : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Δ ⇒ Γ ,, T → Σ[ σ ∈ Δ ⇒ Γ ] (Tm Δ (T [ σ ]))
ctx-ext-subst τ = [ π ⊚ τ , {!ξ [ τ ]'!} ]
