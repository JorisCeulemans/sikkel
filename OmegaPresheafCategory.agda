module OmegaPresheafCategory where

open import Axiom.Extensionality.Propositional
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
open import Function hiding (_⟨_⟩_)
open import Level renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

-- postulate
--   funext : Extensionality 0ℓ 0ℓ

variable
  ℓ : Level
  m n : ℕ

-- infixl 15 _,,_
infix 10 _⇒_

record Ctx ℓ : Set (lsuc ℓ) where
  field
    set : ℕ → Set ℓ
    rel : ∀ {m n} → m ≤ n → set n → set m
    rel-id : ∀ {n} → rel {n} (≤-refl) ≡ id
    rel-comp : ∀ {k m n} (k≤m : k ≤ m) (m≤n : m ≤ n) → rel (≤-trans k≤m m≤n) ≡ rel k≤m ∘ rel m≤n
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
rel-id ◇ = refl
rel-comp ◇ = λ _ _ → refl

𝕪 : ℕ → Ctx 0ℓ
set (𝕪 n) = λ m → m ≤ n
rel (𝕪 n) = ≤-trans
rel-id (𝕪 n) = funext (λ _ → ≤-irrelevant _ _)
  where
    postulate funext : Extensionality _ _
rel-comp (𝕪 n) = λ m1≤m2 m2≤m3 → funext (λ _ → ≤-irrelevant _ _)
  where
    postulate funext : Extensionality _ _

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
  constructor MkTy
  field
    type : (n : ℕ) (γ : Γ ⟨ n ⟩) → Set ℓ
    morph : ∀ {m n} (m≤n : m ≤ n) (γ : Γ ⟨ n ⟩) → type n γ → type m (Γ ⟪ m≤n ⟫ γ)
--    morph-id : ∀ {n} (γ : Γ ⟨ n ⟩) → subst (λ f → type n (f γ)) (rel-id Γ {n}) ∘ morph ≤-refl γ ≡ id
--    morph-comp : ∀ {k m n} (k≤m : k ≤ m) (m≤n : m ≤ n) (γ : Γ ⟨ n ⟩) →
--                 subst (λ f → type k (f γ)) (rel-comp Γ k≤m m≤n) ∘ morph (≤-trans k≤m m≤n) γ ≡ morph k≤m (Γ ⟪ m≤n ⟫ γ) ∘ morph m≤n γ
open Ty

_⟨_,_⟩ : {Γ : Ctx ℓ} → Ty Γ → (n : ℕ) → Γ ⟨ n ⟩ → Set ℓ
T ⟨ n , γ ⟩ = type T n γ

_⟪_,_⟫ : {Γ : Ctx ℓ} (T : Ty Γ) (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ → T ⟨ m , Γ ⟪ ineq ⟫ γ ⟩
T ⟪ ineq , γ ⟫ = morph T ineq γ

_⟪_,_⟫_ : {Γ : Ctx ℓ} (T : Ty Γ) (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ → T ⟨ m , Γ ⟪ ineq ⟫ γ ⟩
T ⟪ ineq , γ ⟫ t = (T ⟪ ineq , γ ⟫) t

_[_] : {Δ Γ : Ctx ℓ} → Ty Γ → Δ ⇒ Γ → Ty Δ
type (T [ σ ]) = λ n δ → T ⟨ n , func σ δ ⟩
-- morph (T [ σ ]) ineq δ rewrite sym (cong-app (naturality σ {ineq = ineq}) δ) = T ⟪ ineq , func σ δ ⟫ -- subst (λ x → T ⟨ _ , x ⟩) (cong-app (naturality σ {ineq = ineq}) δ) ∘ (T ⟪ ineq , func σ δ ⟫)
morph (T [ σ ]) ineq δ t = subst (λ x → type T _ (x δ)) (naturality σ {ineq = ineq}) (T ⟪ ineq , func σ δ ⟫ t)
-- morph-id (T [ σ ]) δ = {!!}
-- morph-comp (T [ σ ]) k≤m m≤n δ = {!!}
{-
subst-comp-test : {Δ Γ Θ : Ctx ℓ} {T : Ty Θ} {τ : Γ ⇒ Θ} {σ : Δ ⇒ Γ} (ineq : m ≤ n) (δ : Δ ⟨ n ⟩) (t : T [ τ ] [ σ ] ⟨ n , δ ⟩) → (T [ τ ] [ σ ]) ⟪ ineq , δ ⟫ t ≡ (T [ τ ⊚ σ ]) ⟪ ineq , δ ⟫ t
subst-comp-test {Δ = Δ}{Γ}{Θ}{T}{τ}{σ} ineq δ t = {!!}

subst-comp : {Δ Γ Θ : Ctx ℓ} {T : Ty Θ} {τ : Γ ⇒ Θ} {σ : Δ ⇒ Γ} → T [ τ ] [ σ ] ≡ T [ τ ⊚ σ ]
subst-comp {ℓ} {Δ} {Γ} {Θ} {T} {τ} {σ} = {!!}
{-  (T [ τ ]) [ σ ] ≡⟨ refl ⟩
  record { type = λ n δ → T ⟨ n , func τ (func σ δ) ⟩ ; morph = morph ((T [ τ ]) [ σ ]) } ≡⟨ cong (λ x → record { type = λ n δ → T ⟨ n , func τ (func σ δ) ⟩ ; morph = λ {m n} ineq δ → x m n ineq δ }) α ⟩
  record { type = λ n δ → T ⟨ n , func τ (func σ δ) ⟩ ; morph = morph (T [ τ ⊚ σ ]) } ≡⟨ refl ⟩
  T [ τ ⊚ σ ] ∎
  where
    open ≡-Reasoning
    α : {!!} ≡ {!!}
    α = {!!}-}
-}

subst-trans : ∀ {a p} {A : Set a} {x y z : A} {P : A → Set p} {p : P x} (eq₁ : x ≡ y) (eq₂ : y ≡ z) → subst P (trans eq₁ eq₂) p ≡ subst P eq₂ (subst P eq₁ p)
subst-trans refl refl = refl

subst-comp : {Δ Γ Θ : Ctx ℓ} {T : Ty Θ} {τ : Γ ⇒ Θ} {σ : Δ ⇒ Γ} → T [ τ ] [ σ ] ≡ T [ τ ⊚ σ ]
subst-comp {ℓ} {Δ} {Γ} {Θ} {T} {τ} {σ} =
    cong (MkTy _) (funextI (funextI (funext λ ineq → funext′ λ δ → funext′ λ t →
      subst (λ x → type T _ (func τ (x δ))) (naturality σ)
      (subst (λ x → type T _ (x (func σ δ))) (naturality τ)
       (morph T ineq (func τ (func σ δ)) t))
       ≡⟨ subst-∘ (naturality σ)  ⟩
      subst (λ x → type T _ (x δ)) (cong (func τ ∘_) (naturality σ))
      (subst (λ x → type T _ (x (func σ δ))) (naturality τ)
       (morph T ineq (func τ (func σ δ)) t))
       ≡⟨ cong (subst (λ x → type T _ (x δ)) (cong (func τ ∘_) (naturality σ))) (subst-∘ (naturality τ)) ⟩
      subst (λ x → type T _ (x δ)) (cong (func τ ∘_) (naturality σ))
      (subst (λ x → type T _ (x δ)) (cong (_∘ func σ) (naturality τ))
       (morph T ineq (func τ (func σ δ)) t))
       ≡⟨ subst-subst (cong (_∘ func σ) (naturality τ))  ⟩
      subst (λ x → type T _ (x δ))
        (trans (cong (_∘ func σ) (naturality τ)) (cong (func τ ∘_) (naturality σ)))
        (morph T ineq (func τ (func σ δ)) t)
       ≡⟨ cong
            (λ p →
               subst (λ x → type T _ (x δ)) p
               (morph T ineq (func τ (func σ δ)) t))
            (cong (trans (cong (_∘ func σ) (naturality τ))) (sym (trans-reflʳ (cong (func τ ∘_) (naturality σ))))) ⟩
       subst (λ x → type T _ (x δ))
         (trans (cong (_∘ func σ) (naturality τ))
           (trans (cong (func τ ∘_) (naturality σ))
         refl))
       (morph T ineq (func τ (func σ δ)) t) ∎
      )))
    where
      open ≡-Reasoning
      postulate funext : Extensionality _ _
                funext′ : Extensionality _ _
                funextI : ExtensionalityImplicit _ _

record Tm {ℓ} (Γ : Ctx ℓ) (T : Ty Γ) : Set ℓ where
  field
    term : (n : ℕ) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
    naturality : ∀ {m n} (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟪ ineq , γ ⟫ (term n γ) ≡ term m (Γ ⟪ ineq ⟫ γ)
open Tm

_⟨_,_⟩' : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → (n : ℕ) → (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
t ⟨ n , γ ⟩' = term t n γ

_⟪_,_⟫' : {Γ : Ctx ℓ} {T : Ty Γ} (t : Tm Γ T) (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟪ ineq , γ ⟫ (t ⟨ n , γ ⟩') ≡ t ⟨ m , Γ ⟪ ineq ⟫ γ ⟩'
t ⟪ ineq , γ ⟫' = naturality t ineq γ

-- _[_]' : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ])
-- term (t [ σ ]') = λ n δ → t ⟨ n , func σ δ ⟩'
-- naturality (t [ σ ]') ineq δ rewrite sym (cong-app (naturality σ {ineq = ineq}) δ) = t ⟪ ineq , func σ δ ⟫'

_,,_ : (Γ : Ctx ℓ) (T : Ty Γ) → Ctx ℓ
set (Γ ,, T) = λ n → Σ[ γ ∈ Γ ⟨ n ⟩ ] (T ⟨ n , γ ⟩)
rel (Γ ,, T) = λ { ineq [ γ , t ] → [ Γ ⟪ ineq ⟫ γ , T ⟪ ineq , γ ⟫ t ] }
rel-id (Γ ,, T) = {!!}
rel-comp (Γ ,, T) = {!!}

π : {Γ : Ctx ℓ} {T : Ty Γ} → Γ ,, T ⇒ Γ
func π = proj₁
naturality π = refl

ξ : {Γ : Ctx ℓ} {T : Ty Γ} → Tm (Γ ,, T) (T [ π ])
term ξ = λ { n [ γ , t ] → t }
naturality ξ = λ _ _ → refl

ctx-ext-subst : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Δ ⇒ Γ ,, T → Σ[ σ ∈ Δ ⇒ Γ ] (Tm Δ (T [ σ ]))
ctx-ext-subst τ = [ π ⊚ τ , {!ξ [ τ ]'!} ]

ctx-ext-subst⁻¹ : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Σ[ σ ∈ Δ ⇒ Γ ] (Tm Δ (T [ σ ])) → Δ ⇒ Γ ,, T
func (ctx-ext-subst⁻¹ [ σ , t ]) = λ δ → [ func σ δ , t ⟨ _ , δ ⟩' ]
naturality (ctx-ext-subst⁻¹ [ σ , t ]) = {!!}

▻ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ
type (▻ {Γ = Γ} T) = λ { zero _ → Lift _ ⊤ ; (suc n) γ → T ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩ }
morph (▻ {Γ = Γ} T) = λ { z≤n γ → λ _ → lift tt ; (s≤s ineq) γ → {!T ⟪ ineq , Γ ⟪ n≤1+n _ ⟫ γ ⟫!} }
-- morph-id (▻ T) = {!!}
-- morph-comp (▻ T) = {!!}

next : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → Tm Γ (▻ T)
term (next {Γ = Γ} t) = λ { zero γ → lift tt ; (suc n) γ → t ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩' }
naturality (next t) = λ ineq γ → {!!}
