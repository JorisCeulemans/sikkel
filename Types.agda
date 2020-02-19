module Types where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat hiding (_⊔_)
open import Data.Product using (proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Data.Unit using (⊤; tt)
open import Function hiding (_⟨_⟩_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

open import Helpers
open import CwF-Structure

--------------------------------------------------
-- (Non-dependent) product types
--------------------------------------------------

subst-× : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c}
          {x x' : A} (e : x ≡ x')
          (p : B x × C x) →
          subst (λ x → B x × C x) e p ≡ [ subst B e (proj₁ p) , subst C e (proj₂ p) ]
subst-× refl p = refl

_×'_ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ → Ty Γ
_×'_ {Γ = Γ} T S = MkTy (λ n γ → T ⟨ n , γ ⟩ × S ⟨ n , γ ⟩)
                   (λ { ineq γ [ t , s ] → [ T ⟪ ineq , γ ⟫ t , S ⟪ ineq , γ ⟫ s ] })
                   (λ γ → funext λ { [ t , s ] → trans (subst-× (rel-id Γ) _)
                                                            (cong₂ [_,_] (cong-app (morph-id T γ) t)
                                                                         (cong-app (morph-id S γ) s)) })
                   (λ k≤m m≤n γ → funext λ { [ t , s ] → trans (subst-× (rel-comp Γ k≤m m≤n) _)
                                                                 (cong₂ [_,_] (cong-app (morph-comp T k≤m m≤n γ) t)
                                                                              (cong-app (morph-comp S k≤m m≤n γ) s)) })

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

module _ {Δ Γ : Ctx ℓ} {T S : Ty Γ} (σ : Δ ⇒ Γ) where
  abstract
    ×'-natural : (T ×' S) [ σ ] ≡ (T [ σ ]) ×' (S [ σ ])
    ×'-natural = cong₃-d (MkTy _)
                         (funextI (funextI (funext λ ineq → funext λ δ → funext λ { [ t , s ] →
                           subst-× (naturality σ) [ T ⟪ ineq , func σ δ ⟫ t , S ⟪ ineq , func σ δ ⟫ s ] })))
                         (funextI (funext (λ _ → uip _ _)))
                         (funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _))))

  pair-natural : (t : Tm Γ T) (s : Tm Γ S) → subst (Tm Δ) ×'-natural ((pair t s) [ σ ]') ≡ pair (t [ σ ]') (s [ σ ]')
  pair-natural t s = cong₂-d MkTm
    (term (subst (Tm Δ) ×'-natural (pair t s [ σ ]'))
        ≡⟨ sym (weak-subst-application {B = Tm Δ} (λ x y → term y) ×'-natural) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z ⟨ n , δ ⟩) ×'-natural (term (pair t s [ σ ]'))
        ≡⟨ subst-∘ ×'-natural ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) (cong type ×'-natural) (term (pair t s [ σ ]'))
        ≡⟨ cong (λ y → subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) y (term (pair t s [ σ ]'))) {x = cong type ×'-natural} {y = refl} (uip _ _) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) {x = type ((T ×' S) [ σ ])} refl (term (pair (t [ σ ]') (s [ σ ]')))
        ≡⟨⟩
      term (pair (t [ σ ]') (s [ σ ]')) ∎)
    (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
    where open ≡-Reasoning

  fst-natural : (p : Tm Γ (T ×' S)) → (fst p) [ σ ]' ≡ fst (subst (Tm Δ) ×'-natural (p [ σ ]'))
  fst-natural p = cong₂-d MkTm
    (term (fst p [ σ ]')
        ≡⟨ cong (λ z → λ n δ → proj₁ (subst (λ z → (n₁ : ℕ) (γ : Δ ⟨ n₁ ⟩) → z n₁ γ) z (term (p [ σ ]')) n δ)) {x = refl} {y = cong type ×'-natural} (uip _ _) ⟩
      (λ n δ → proj₁ (subst (λ z → (n₁ : ℕ) (γ : Δ ⟨ n₁ ⟩) → z n₁ γ) (cong type ×'-natural) (term (p [ σ ]')) n δ))
        ≡⟨ cong (λ z n δ → proj₁ (z n δ)) (sym (subst-∘ {P = λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ} {f = type} ×'-natural)) ⟩
      (λ n δ → proj₁ (subst (λ z → (n₁ : ℕ) (γ : Δ ⟨ n₁ ⟩) → z ⟨ n₁ , γ ⟩) ×'-natural (term (p [ σ ]')) n δ))
        ≡⟨ cong (λ z n δ → proj₁ (z n δ)) (weak-subst-application {B = Tm Δ} (λ x y → term y) ×'-natural) ⟩
      term (fst (subst (Tm Δ) ×'-natural (p [ σ ]'))) ∎)
    (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
    where open ≡-Reasoning

  snd-natural : (p : Tm Γ (T ×' S)) → (snd p) [ σ ]' ≡ snd (subst (Tm Δ) ×'-natural (p [ σ ]'))
  snd-natural p = cong₂-d MkTm
    (term (snd p [ σ ]')
        ≡⟨ cong (λ z → λ n δ → proj₂ (subst (λ z → (n₁ : ℕ) (γ : Δ ⟨ n₁ ⟩) → z n₁ γ) z (term (p [ σ ]')) n δ)) {x = refl} {y = cong type ×'-natural} (uip _ _) ⟩
      (λ n δ → proj₂ (subst (λ z → (n₁ : ℕ) (γ : Δ ⟨ n₁ ⟩) → z n₁ γ) (cong type ×'-natural) (term (p [ σ ]')) n δ))
        ≡⟨ cong (λ z n δ → proj₂ (z n δ)) (sym (subst-∘ {P = λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ} {f = type} ×'-natural)) ⟩
      (λ n δ → proj₂ (subst (λ z → (n₁ : ℕ) (γ : Δ ⟨ n₁ ⟩) → z ⟨ n₁ , γ ⟩) ×'-natural (term (p [ σ ]')) n δ))
        ≡⟨ cong (λ z n δ → proj₂ (z n δ)) (weak-subst-application {B = Tm Δ} (λ x y → term y) ×'-natural) ⟩
      term (snd (subst (Tm Δ) ×'-natural (p [ σ ]'))) ∎)
    (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
    where open ≡-Reasoning

--------------------------------------------------
-- Sum types
--------------------------------------------------

subst-⊎ˡ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c}
           {x x' : A} (e : x ≡ x') {y : B x} →
           subst (λ x → B x ⊎ C x) e (inl y) ≡ inl (subst B e y)
subst-⊎ˡ e = weak-subst-application (λ _ w → inl w) e

subst-⊎ʳ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c}
           {x x' : A} (e : x ≡ x') {z : C x} →
           subst (λ x → B x ⊎ C x) e (inr z) ≡ inr (subst C e z)
subst-⊎ʳ e = weak-subst-application (λ _ w → inr w) e

_⊎'_ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ → Ty Γ
_⊎'_ {Γ = Γ} T S = MkTy (λ n γ → T ⟨ n , γ ⟩ ⊎ S ⟨ n , γ ⟩)
                         (λ { ineq γ (inl t) → inl (T ⟪ ineq , γ ⟫ t) ; ineq γ (inr s) → inr (S ⟪ ineq , γ ⟫ s) })
                         (λ γ → funext λ { (inl t) → trans (subst-⊎ˡ _) (cong inl (cong-app (morph-id T γ) t))
                                          ; (inr s) → trans (subst-⊎ʳ _) (cong inr (cong-app (morph-id S γ) s)) })
                         (λ k≤m m≤n γ → funext λ { (inl t) → trans (subst-⊎ˡ _) (cong inl (cong-app (morph-comp T k≤m m≤n γ) t))
                                                  ; (inr s) → trans (subst-⊎ʳ _) (cong inr (cong-app (morph-comp S k≤m m≤n γ) s)) })
{-
type (T ⊎' S) = λ n γ → T ⟨ n , γ ⟩ ⊎ S ⟨ n , γ ⟩
morph (T ⊎' S) = λ { ineq γ (inl t) → inl (T ⟪ ineq , γ ⟫ t) ; ineq γ (inr s) → inr (S ⟪ ineq , γ ⟫ s) }
morph-id (T ⊎' S) = λ γ → funext λ { (inl t) → {!trans ? ?!} ; (inr s) → {!!} }
morph-comp (T ⊎' S) = {!!}
-}

module _ {Γ : Ctx ℓ} {T S : Ty Γ} where
  inl' : Tm Γ T → Tm Γ (T ⊎' S)
  term (inl' t) = λ n γ → inl (t ⟨ n , γ ⟩')
  naturality (inl' t) = λ ineq γ → cong inl (t ⟪ ineq , γ ⟫')

  inr' : Tm Γ S → Tm Γ (T ⊎' S)
  term (inr' s) = λ n γ → inr (s ⟨ n , γ ⟩')
  naturality (inr' s) = λ ineq γ → cong inr (s ⟪ ineq , γ ⟫')

inl'⟨_⟩_ : {Γ : Ctx ℓ} {T : Ty Γ} (S : Ty Γ) (t : Tm Γ T) → Tm Γ (T ⊎' S)
inl'⟨ S ⟩ t = inl' {S = S} t

inr'⟨_⟩_ : {Γ : Ctx ℓ} (T : Ty Γ) {S : Ty Γ} (s : Tm Γ S) → Tm Γ (T ⊎' S)
inr'⟨ T ⟩ s = inr' {T = T} s

module _ {Δ Γ : Ctx ℓ} {T S : Ty Γ} (σ : Δ ⇒ Γ) where
  abstract
    ⊎'-natural : (T ⊎' S) [ σ ] ≡ (T [ σ ]) ⊎' (S [ σ ])
    ⊎'-natural = cong₃-d (MkTy _)
                          (funextI (funextI (funext λ ineq → funext λ δ → funext λ {
                            (inl t) → subst-⊎ˡ (naturality σ) ;
                            (inr s) → subst-⊎ʳ (naturality σ) })))
                          (funextI (funext (λ _ → uip _ _)))
                          (funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _))))

  inl'-natural : (t : Tm Γ T) → subst (Tm Δ) ⊎'-natural ((inl' t) [ σ ]') ≡ inl' (t [ σ ]')
  inl'-natural t = cong₂-d MkTm
    (term (subst (Tm Δ) ⊎'-natural (inl' t [ σ ]'))
        ≡⟨ sym (weak-subst-application {B = Tm Δ} (λ x y → term y) ⊎'-natural) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z ⟨ n , δ ⟩) ⊎'-natural (term (inl'⟨ S [ σ ] ⟩ (t [ σ ]')))
        ≡⟨ subst-∘ ⊎'-natural ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) (cong type ⊎'-natural) (term (inl'⟨ S [ σ ] ⟩ (t [ σ ]')))
        ≡⟨ cong (λ y → subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) y (term (inl'⟨ S [ σ ] ⟩ (t [ σ ]')))) {x = cong type ⊎'-natural} {y = refl} (uip _ _) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) {x = type ((T ⊎' S) [ σ ])} refl (term (inl'⟨ S [ σ ] ⟩ (t [ σ ]')))
        ≡⟨⟩
      term (inl'⟨ S [ σ ] ⟩ (t [ σ ]')) ∎)
    (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
    where open ≡-Reasoning

  inr'-natural : (s : Tm Γ S) → subst (Tm Δ) ⊎'-natural ((inr' s) [ σ ]') ≡ inr' (s [ σ ]')
  inr'-natural s = cong₂-d MkTm
    (term (subst (Tm Δ) ⊎'-natural (inr' s [ σ ]'))
        ≡⟨ sym (weak-subst-application {B = Tm Δ} (λ x y → term y) ⊎'-natural) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z ⟨ n , δ ⟩) ⊎'-natural (term (inr'⟨ T [ σ ] ⟩ (s [ σ ]')))
        ≡⟨ subst-∘ ⊎'-natural ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) (cong type ⊎'-natural) (term (inr'⟨ T [ σ ] ⟩ (s [ σ ]')))
        ≡⟨ cong (λ y → subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) y (term (inr'⟨ T [ σ ] ⟩ (s [ σ ]')))) {x = cong type ⊎'-natural} {y = refl} (uip _ _) ⟩
      subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) {x = type ((T ⊎' S) [ σ ])} refl (term (inr'⟨ T [ σ ] ⟩ (s [ σ ]')))
        ≡⟨⟩
      term (inr'⟨ T [ σ ] ⟩ (s [ σ ]')) ∎)
    (funextI (funextI (funext λ _ → funext λ _ → uip _ _)))
    where open ≡-Reasoning


--------------------------------------------------
-- Discrete types
--------------------------------------------------

Discr : (A : Set ℓ) → Ty ◇
type (Discr A) = λ _ _ → A
morph (Discr A) = λ _ _ → id
morph-id (Discr A) = λ _ → refl
morph-comp (Discr A) = λ _ _ _ → refl

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
                          (funextI (funextI (funext λ ineq → funext λ _ → uip _ _)))

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
