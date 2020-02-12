module OmegaPresheafCategory where

open import Axiom.Extensionality.Propositional
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Data.Unit using (⊤; tt)
open import Function hiding (_⟨_⟩_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

postulate
  funext : ∀ {ℓ ℓ'} → Extensionality ℓ ℓ'
  funextI : ∀ {ℓ ℓ'} → ExtensionalityImplicit ℓ ℓ'

variable
  ℓ ℓ' : Level
  m n : ℕ

uip : {A : Set ℓ} {x y : A} {e1 e2 : x ≡ y} → e1 ≡ e2
uip {e1 = refl} {refl} = refl

infixl 15 _,,_
infix 10 _⇒_
infix 15 _⟨_,_⟩

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
rel-comp (𝕪 n) = λ m1≤m2 m2≤m3 → funext (λ _ → ≤-irrelevant _ _)

record _⇒_ {ℓ} (Δ Γ : Ctx ℓ) : Set ℓ where
  constructor MkSubst
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

-- Currently implemented by pattern matching on both e1 and e2. Can also be implemented
-- with option --without-K enabled since A → Lift ℓ ⊤ has decidable equality (Hedberg's theorem).
to-⊤-hset : {A : Set ℓ'} {f g : A → Lift ℓ ⊤} (e1 e2 : f ≡ g) → e1 ≡ e2
to-⊤-hset refl refl = refl

empty-subst-terminal : (Γ : Ctx ℓ) (σ : Γ ⇒ ◇) → σ ≡ empty-subst Γ
empty-subst-terminal Γ σ = cong (MkSubst _) (funextI (funextI (funextI λ {ineq} → to-⊤-hset _ _)))

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
morph (T [ σ ]) ineq δ t = subst (λ x → T ⟨ _ , (x δ) ⟩) (naturality σ {ineq = ineq}) (T ⟪ ineq , func σ δ ⟫ t)
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

ty-subst-id : {Γ : Ctx ℓ} (T : Ty Γ) → T [ id-subst Γ ] ≡ T
ty-subst-id T = refl

subst-trans : ∀ {a p} {A : Set a} {x y z : A} {P : A → Set p} {p : P x} (eq₁ : x ≡ y) (eq₂ : y ≡ z) → subst P (trans eq₁ eq₂) p ≡ subst P eq₂ (subst P eq₁ p)
subst-trans refl refl = refl

ty-subst-comp : {Δ Γ Θ : Ctx ℓ} (T : Ty Θ) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → T [ τ ] [ σ ] ≡ T [ τ ⊚ σ ]
ty-subst-comp T τ σ =
    cong (MkTy _) (funextI (funextI (funext λ ineq → funext λ δ → funext λ t →
      subst (λ x → T ⟨ _ , func τ (x δ) ⟩) (naturality σ)
      (subst (λ x → T ⟨ _ , x (func σ δ) ⟩) (naturality τ)
       (T ⟪ ineq , func τ (func σ δ) ⟫ t))
       ≡⟨ subst-∘ (naturality σ)  ⟩
      subst (λ x → T ⟨ _ , x δ ⟩) (cong (func τ ∘_) (naturality σ))
      (subst (λ x → T ⟨ _ , x (func σ δ) ⟩) (naturality τ)
       (T ⟪ ineq , func τ (func σ δ) ⟫ t))
       ≡⟨ cong (subst (λ x → T ⟨ _  , x δ ⟩) (cong (func τ ∘_) (naturality σ))) (subst-∘ (naturality τ)) ⟩
      subst (λ x → T ⟨ _ , x δ ⟩) (cong (func τ ∘_) (naturality σ))
      (subst (λ x → T ⟨ _ , x δ ⟩) (cong (_∘ func σ) (naturality τ))
       (T ⟪ ineq , func τ (func σ δ) ⟫ t))
       ≡⟨ subst-subst (cong (_∘ func σ) (naturality τ))  ⟩
      subst (λ x → T ⟨ _ , x δ ⟩)
        (trans (cong (_∘ func σ) (naturality τ)) (cong (func τ ∘_) (naturality σ)))
        (T ⟪ ineq , func τ (func σ δ) ⟫ t)
       ≡⟨ cong
            (λ p →
               subst (λ x → T ⟨ _ , x δ ⟩) p
               (T ⟪ ineq , func τ (func σ δ) ⟫ t))
            (cong (trans (cong (_∘ func σ) (naturality τ))) (sym (trans-reflʳ (cong (func τ ∘_) (naturality σ))))) ⟩
       subst (λ x → T ⟨ _ , x δ ⟩)
         (trans (cong (_∘ func σ) (naturality τ))
           (trans (cong (func τ ∘_) (naturality σ))
         refl))
       (T ⟪ ineq , func τ (func σ δ) ⟫ t) ∎
      )))
    where
      open ≡-Reasoning

record Tm {ℓ} (Γ : Ctx ℓ) (T : Ty Γ) : Set ℓ where
  constructor MkTm
  field
    term : (n : ℕ) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
    naturality : ∀ {m n} (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟪ ineq , γ ⟫ (term n γ) ≡ term m (Γ ⟪ ineq ⟫ γ)
open Tm

_⟨_,_⟩' : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → (n : ℕ) → (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
t ⟨ n , γ ⟩' = term t n γ

_⟪_,_⟫' : {Γ : Ctx ℓ} {T : Ty Γ} (t : Tm Γ T) (ineq : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟪ ineq , γ ⟫ (t ⟨ n , γ ⟩') ≡ t ⟨ m , Γ ⟪ ineq ⟫ γ ⟩'
t ⟪ ineq , γ ⟫' = naturality t ineq γ

cong-d : {A : Set ℓ} {B : A → Set ℓ'}
         (f : (x : A) → B x)
         {a a' : A} (e : a ≡ a') →
         subst B e (f a) ≡ f a'
cong-d f refl = refl

_[_]' : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ])
term (t [ σ ]') = λ n δ → t ⟨ n , func σ δ ⟩'
naturality (_[_]'  {Δ = Δ}{Γ}{T} t σ) ineq δ = 
  (T [ σ ]) ⟪ ineq , δ ⟫ (t [ σ ]' ⟨ _ , δ ⟩')
        ≡⟨⟩
  subst (λ x → T ⟨ _ , (x δ) ⟩) (naturality σ {ineq = ineq}) (T ⟪ ineq , func σ δ ⟫ (t ⟨ _ , func σ δ ⟩'))
        ≡⟨ cong (subst (λ x → T ⟨ _ , (x δ) ⟩) (naturality σ {ineq = ineq})) (t ⟪ ineq , func σ δ ⟫') ⟩
  subst (λ x → T ⟨ _ , (x δ) ⟩) (naturality σ {ineq = ineq}) (t ⟨ _ , Γ ⟪ ineq ⟫ (func σ δ) ⟩')
        ≡⟨ cong-d (λ x → t ⟨ _ , x δ ⟩') (naturality σ) ⟩
  t ⟨ _ , func σ (Δ ⟪ ineq ⟫ δ) ⟩' ∎
  where open ≡-Reasoning

tm-subst-id : {Γ : Ctx ℓ} {T : Ty Γ} (t : Tm Γ T) → t [ id-subst Γ ]' ≡ t
tm-subst-id t = cong (MkTm _) (funextI (funextI (funext λ ineq → funext λ δ →
                               trans (trans-reflʳ _) (cong-id _))))

subst2 : ∀ {a b c} {A : Set a} {B : A → Set b} (C : (x : A) → B x → Set c)
         {x x' : A} {y : B x} {y' : B x'}
         (ex : x ≡ x') (ey : subst B ex y ≡ y') →
         C x y → C x' y'
subst2 C refl refl c = c

cong₃-d : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} {D : A → Set d}
         (f : (x : A) (y : B x) → C x y → D x)
         {x x' : A} {y : B x} {y' : B x'} {z : C x y} {z' : C x' y'}
         (ex : x ≡ x') (ey : subst B ex y ≡ y') (ez : subst2 C ex ey z ≡ z') →
         subst D ex (f x y z) ≡ f x' y' z'
cong₃-d f refl refl refl = refl

subst₂-∘ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c}
           (f : (x : A) (y : B x) → C x y)
           {x x' : A} {y : B x} {y' : B x'}
           (ex : x ≡ x') (ey : subst B ex y ≡ y') →
           subst (λ x → (y : B x) → C x y) ex (λ y → f x y) y' ≡ subst2 C ex ey (f x y)
subst₂-∘ = {!!}

test : {A : Set ℓ} {B C : Set ℓ'} (f : A → B) (e : B ≡ C) (a : A) →
       subst (λ x → A → x) e f a ≡ subst id e (f a)
test f refl a = refl
{-
tm-subst-comp : {Δ Γ Θ : Ctx ℓ} {T : Ty Θ} (t : Tm Θ T) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                subst (Tm Δ) (ty-subst-comp T τ σ) (t [ τ ]' [ σ ]') ≡ t [ τ ⊚ σ ]'
tm-subst-comp {T = T} t τ σ = cong₂-d (λ S → MkTm {T = S}) (ty-subst-comp T τ σ) (funext (λ n → funext λ δ → {!!})) (funextI (funextI λ {_} → funext λ _ → funext λ _ → uip)) -- cong₂-d MkTm {!!} {!!}
-}
_,,_ : (Γ : Ctx ℓ) (T : Ty Γ) → Ctx ℓ
set (Γ ,, T) = λ n → Σ[ γ ∈ Γ ⟨ n ⟩ ] (T ⟨ n , γ ⟩)
rel (Γ ,, T) = λ { ineq [ γ , t ] → [ Γ ⟪ ineq ⟫ γ , T ⟪ ineq , γ ⟫ t ] }
rel-id (Γ ,, T) = funext λ { [ γ , t ] → {!!} }
rel-comp (Γ ,, T) = λ k≤m m≤n → funext λ { [ γ , t ] → {!!} }

π : {Γ : Ctx ℓ} {T : Ty Γ} → Γ ,, T ⇒ Γ
func π = proj₁
naturality π = refl

ξ : {Γ : Ctx ℓ} {T : Ty Γ} → Tm (Γ ,, T) (T [ π ])
term ξ = λ _ → proj₂
naturality ξ = λ _ _ → refl

ctx-ext-subst : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Δ ⇒ Γ ,, T → Σ[ σ ∈ Δ ⇒ Γ ] (Tm Δ (T [ σ ]))
ctx-ext-subst {Δ = Δ}{Γ}{T} τ = [ π ⊚ τ , subst (Tm Δ) (ty-subst-comp T π τ) (ξ {Γ = Γ} [ τ ]') ]

ctx-ext-subst⁻¹ : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Σ[ σ ∈ Δ ⇒ Γ ] (Tm Δ (T [ σ ])) → Δ ⇒ Γ ,, T
func (ctx-ext-subst⁻¹ [ σ , t ]) = λ δ → [ func σ δ , t ⟨ _ , δ ⟩' ]
naturality (ctx-ext-subst⁻¹ [ σ , t ]) = funext (λ δ → {!!})


--------------------------------------------------
-- (Non-dependent) product types
--------------------------------------------------

_×'_ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ → Ty Γ
type (T ×' S) = λ n γ → T ⟨ n , γ ⟩ × S ⟨ n , γ ⟩
morph (T ×' S) = λ { ineq γ [ t , s ] → [ T ⟪ ineq , γ ⟫ t , S ⟪ ineq , γ ⟫ s ] }

module _ {Γ : Ctx ℓ} {T S : Ty Γ} where
  pair : Tm Γ T → Tm Γ S → Tm Γ (T ×' S)
  term (pair t s) = λ n γ → [ t ⟨ n , γ ⟩' , s ⟨ n , γ ⟩' ]
  naturality (pair t s) = λ ineq γ → cong₂ [_,_] (t ⟪ ineq , γ ⟫') (s ⟪ ineq , γ ⟫')

  fst : Tm Γ (T ×' S) → Tm Γ T
  term (fst p) = λ n γ → proj₁ (p ⟨ n , γ ⟩')
  naturality (fst p) = λ ineq γ →
    T ⟪ ineq , γ ⟫ ((fst p) ⟨ _ , γ ⟩') ≡⟨ cong proj₁ (p ⟪ _ , γ ⟫') ⟩
    fst p ⟨ _ , Γ ⟪ ineq ⟫ γ ⟩' ∎
    where open ≡-Reasoning

  snd : Tm Γ (T ×' S) → Tm Γ S
  term (snd p) = λ n γ → proj₂ (p ⟨ n , γ ⟩')
  naturality (snd p) = λ ineq γ → cong proj₂ (p ⟪ _ , γ ⟫')

--------------------------------------------------
-- Sum types
--------------------------------------------------

_⊎'_ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ → Ty Γ
type (T ⊎' S) = λ n γ → T ⟨ n , γ ⟩ ⊎ S ⟨ n , γ ⟩
morph (T ⊎' S) = λ { ineq γ (inl t) → inl (T ⟪ ineq , γ ⟫ t) ; ineq γ (inr s) → inr (S ⟪ ineq , γ ⟫ s) }

module _ {Γ : Ctx ℓ} {T S : Ty Γ} where
  inl' : Tm Γ T → Tm Γ (T ⊎' S)
  term (inl' t) = λ n γ → inl (t ⟨ n , γ ⟩')
  naturality (inl' t) = λ ineq γ → cong inl (t ⟪ ineq , γ ⟫')

  inr' : Tm Γ S → Tm Γ (T ⊎' S)
  term (inr' s) = λ n γ → inr (s ⟨ n , γ ⟩')
  naturality (inr' s) = λ ineq γ → cong inr (s ⟪ ineq , γ ⟫')


--------------------------------------------------
-- Discrete types
--------------------------------------------------

cong₂-d : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
          (f : (x : A) → B x → C)
          {x x' : A} {y : B x} {y' : B x'}
          (ex : x ≡ x') (ey : subst B ex y ≡ y') →
          f x y ≡ f x' y'
cong₂-d f refl refl = refl

Discr : (A : Set ℓ) → Ty ◇
type (Discr A) = λ _ _ → A
morph (Discr A) = λ _ _ → id

discr : {A : Set ℓ} → A → Tm ◇ (Discr A)
term (discr a) = λ _ _ → a
naturality (discr a) = λ _ _ → refl

undiscr : {A : Set ℓ} → Tm ◇ (Discr A) → A
undiscr t = t ⟨ 0 , lift tt ⟩'

undiscr-discr : {A : Set ℓ} (a : A) → undiscr (discr a) ≡ a
undiscr-discr a = refl

discr-undiscr : {A : Set ℓ} (t : Tm ◇ (Discr A)) → discr (undiscr t) ≡ t
discr-undiscr t = cong₂-d MkTm
                          (sym (funext λ n → funext λ γ → t ⟪ z≤n , lift tt ⟫'))
                          (funextI (funextI (funext λ ineq → funext λ _ → uip)))

Unit' : Ty ◇
Unit' = Discr ⊤

tt' : Tm ◇ Unit'
tt' = discr tt

Bool' : Ty ◇
Bool' = Discr Bool

true' : Tm ◇ Bool'
true' = discr true

false' : Tm ◇ Bool'
false' = discr false

if'_then'_else'_ : {Γ : Ctx 0ℓ} {T : Ty Γ} → Tm Γ (Bool' [ empty-subst Γ ]) → Tm Γ T → Tm Γ T → Tm Γ T
term (if' c then' t else' f) = λ n γ → if c ⟨ n , γ ⟩' then t ⟨ n , γ ⟩' else f ⟨ n , γ ⟩'
naturality (if'_then'_else'_ {Γ = Γ} c t f) {m} {n} ineq γ with c ⟨ m , Γ ⟪ ineq ⟫ γ ⟩' | c ⟨ n , γ ⟩' | c ⟪ ineq , γ ⟫'
naturality (if'_then'_else'_ {Γ} c t f) {m} {n} ineq γ | false | .false | refl = f ⟪ ineq , γ ⟫'
naturality (if'_then'_else'_ {Γ} c t f) {m} {n} ineq γ | true  | .true  | refl = t ⟪ ineq , γ ⟫'

Nat' : Ty ◇
Nat' = Discr ℕ

zero' : Tm ◇ Nat'
zero' = discr zero

suc' : Tm ◇ Nat' → Tm ◇ Nat'
suc' t = discr (suc (undiscr t))


--------------------------------------------------
-- Later modality for types
--------------------------------------------------

▻ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ
type (▻ {Γ = Γ} T) = λ { zero _ → Lift _ ⊤ ; (suc n) γ → T ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩ }
morph (▻ {Γ = Γ} T) = λ { z≤n γ → λ _ → lift tt ; (s≤s ineq) γ → {!T ⟪ ineq , Γ ⟪ n≤1+n _ ⟫ γ ⟫!} }
-- morph-id (▻ T) = {!!}
-- morph-comp (▻ T) = {!!}

next : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → Tm Γ (▻ T)
term (next {Γ = Γ} t) = λ { zero γ → lift tt ; (suc n) γ → t ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩' }
naturality (next t) = λ ineq γ → {!!}
