module StreamsExample where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
open import Data.Vec.Base hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)
open import Level renaming (zero to lzero; suc to lsuc)

open import Helpers
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import Later

first-≤ : ∀ {m n} {A : Set ℓ} → m ≤ n → Vec A n → Vec A m
first-≤ z≤n as = []
first-≤ (s≤s ineq) (a ∷ as) = a ∷ first-≤ ineq as

first-≤-refl : ∀ {n} {A : Set ℓ} {as : Vec A n} → first-≤ (≤-refl) as ≡ as
first-≤-refl {n = zero} {as = []} = refl
first-≤-refl {n = suc n} {as = a ∷ as} = cong (a ∷_) first-≤-refl

first-≤-trans : ∀ {k m n} {A : Set ℓ} (k≤m : k ≤ m) (m≤n : m ≤ n) (as : Vec A n) →
                first-≤ (≤-trans k≤m m≤n) as ≡ first-≤ k≤m (first-≤ m≤n as)
first-≤-trans z≤n m≤n as = refl
first-≤-trans (s≤s k≤m) (s≤s m≤n) (a ∷ as) = cong (a ∷_) (first-≤-trans k≤m m≤n as)

first-≤-head : ∀ {m n} {A : Set ℓ} (m≤n : m ≤ n) (as : Vec A (suc n)) →
               head as ≡ head (first-≤ (s≤s m≤n) as)
first-≤-head m≤n (a ∷ as) = refl

first-≤-tail : ∀ {m n} {A : Set ℓ} (m≤n : m ≤ n) (as : Vec A (suc n)) →
               first-≤ m≤n (tail as) ≡ tail (first-≤ (s≤s m≤n) as)
first-≤-tail m≤n (a ∷ as) = refl

Stream : Ty {0ℓ} ◇
type Stream = λ n _ → Vec ℕ (suc n)
morph Stream = λ m≤n _ → first-≤ (s≤s m≤n)
morph-id Stream = λ _ → funext λ xs → first-≤-refl
morph-comp Stream = λ k≤m m≤n _ → funext λ xs → first-≤-trans (s≤s k≤m) (s≤s m≤n) xs

str-head : {Γ : Ctx 0ℓ} → Tm Γ (Stream [ empty-subst Γ ]) → Tm Γ (Nat' [ empty-subst Γ ])
term (str-head s) n γ = head (s ⟨ n , γ ⟩')
naturality (str-head {Γ = Γ} s) {m}{n} m≤n γ =
  head (s ⟨ n , γ ⟩')
    ≡⟨ first-≤-head m≤n (s ⟨ n , γ ⟩') ⟩
  head (Stream ⟪ m≤n , _ ⟫ (s ⟨ n , γ ⟩'))
    ≡⟨ cong head (s ⟪ m≤n , γ ⟫') ⟩
  head (s ⟨ m , Γ ⟪ m≤n ⟫ γ ⟩') ∎
  where open ≡-Reasoning

str-tail : {Γ : Ctx 0ℓ} → Tm Γ (Stream [ empty-subst Γ ]) → Tm Γ (▻ Stream [ empty-subst Γ ])
term (str-tail s) zero _ = lift tt
term (str-tail s) (suc n) γ = tail (s ⟨ suc n , γ ⟩')
naturality (str-tail s) z≤n _ = refl
naturality (str-tail {Γ = Γ} s) {suc m}{suc n} (s≤s m≤n) γ =
  subst (λ _ → Vec ℕ (suc m)) (ctx-m≤1+n-app ◇ m≤n _) (first-≤ (s≤s m≤n) (tail (s ⟨ suc n , γ ⟩')))
    ≡⟨ subst-const (ctx-m≤1+n-app ◇ m≤n (lift tt)) _ ⟩
  first-≤ (s≤s m≤n) (tail (s ⟨ suc n , γ ⟩'))
    ≡⟨ first-≤-tail (s≤s m≤n) (s ⟨ suc n , γ ⟩') ⟩
  tail (first-≤ (s≤s (s≤s m≤n)) (s ⟨ suc n , γ ⟩'))
    ≡⟨ cong tail (s ⟪ s≤s m≤n , γ ⟫') ⟩
  tail (s ⟨ suc m , Γ ⟪ s≤s m≤n ⟫ γ ⟩') ∎
  where open ≡-Reasoning

str-cons : {Γ : Ctx 0ℓ} → Tm Γ ((Nat' [ empty-subst Γ ]) ×' (▻ Stream [ empty-subst Γ ])) → Tm Γ (Stream [ empty-subst Γ ])
term (str-cons t) zero γ = fst t ⟨ zero , γ ⟩' ∷ []
term (str-cons t) (suc n) γ = (fst t ⟨ suc n , _ ⟩') ∷ (snd t ⟨ suc n , γ ⟩')
naturality (str-cons t) {zero} {zero} z≤n γ = cong (λ x → proj₁ x ∷ []) (t ⟪ z≤n , γ ⟫')
naturality (str-cons t) {zero} {suc n} z≤n γ = cong (λ x → proj₁ x ∷ []) (t ⟪ z≤n , γ ⟫')
naturality (str-cons {Γ = Γ} t) {suc m}{suc n} (s≤s m≤n) γ = cong₂ _∷_ (cong proj₁ (t ⟪ s≤s m≤n , γ ⟫'))
  (first-≤ (s≤s m≤n) (snd t ⟨ suc n , γ ⟩')
    ≡⟨ sym (subst-const (ctx-m≤1+n-app ◇ m≤n _) _) ⟩
  subst (λ x → Vec ℕ (suc m)) (ctx-m≤1+n-app ◇ m≤n _) (first-≤ (s≤s m≤n) (snd t ⟨ suc n , γ ⟩'))
    ≡⟨⟩
  ▻ Stream ⟪ s≤s m≤n , _ ⟫ (snd t ⟨ suc n , γ ⟩')
    ≡⟨ snd t ⟪ s≤s m≤n , _ ⟫' ⟩
  snd t ⟨ suc m , Γ ⟪ s≤s m≤n ⟫ γ ⟩' ∎)
  where open ≡-Reasoning

zeros : Tm ◇ Stream
zeros = Löb (lam (▻ Stream) (str-cons (pair (zero' [ empty-subst _ ]') ξ)))
