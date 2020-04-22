module StreamsExample where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
open import Data.Vec.Base hiding ([_]; _⊛_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)
open import Level renaming (zero to lzero; suc to lsuc)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension
open import CwF-Structure.SubstitutionSequence
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

Stream-prim : Ty (◇ {0ℓ})
type Stream-prim n _ = Vec ℕ (suc n)
morph Stream-prim m≤n _ = first-≤ (s≤s m≤n)
morph-id Stream-prim _ = first-≤-refl
morph-comp Stream-prim k≤m m≤n _ _ = first-≤-trans (s≤s k≤m) (s≤s m≤n)

Stream : {Γ : Ctx 0ℓ} → Ty Γ
Stream {Γ = Γ} = Stream-prim [ !◇ Γ ]
{-
Stream : {Γ : Ctx 0ℓ} → Ty Γ
type Stream n _ = Vec ℕ (suc n)
morph Stream m≤n _ = first-≤ (s≤s m≤n)
morph-id (Stream {Γ = Γ}) xs = trans (subst-const (rel-id Γ _) _)
                                     first-≤-refl
morph-comp (Stream {Γ = Γ}) k≤m m≤n xs = trans (subst-const (rel-comp Γ k≤m m≤n _) _)
                                               (first-≤-trans (s≤s k≤m) (s≤s m≤n) xs)
-}
str-head : {Γ : Ctx 0ℓ} → Tm Γ Stream → Tm Γ Nat'
term (str-head s) n γ = head (s ⟨ n , γ ⟩')
naturality (str-head {Γ = Γ} s) {m}{n} m≤n {γ}{γ'} eq =
  head (s ⟨ n , γ ⟩')
    ≡⟨ first-≤-head m≤n (s ⟨ n , γ ⟩') ⟩
  head (Stream {Γ = Γ} ⟪ m≤n , eq ⟫ (s ⟨ n , γ ⟩'))
    ≡⟨ cong head (naturality s m≤n eq) ⟩
  head (s ⟨ m , γ' ⟩') ∎
  where open ≡-Reasoning

str-tail : {Γ : Ctx 0ℓ} → Tm Γ Stream → Tm Γ (▻ Stream)
term (str-tail s) zero _ = lift tt
term (str-tail s) (suc n) γ = tail (s ⟨ suc n , γ ⟩')
naturality (str-tail s) z≤n _ = refl
naturality (str-tail {Γ = Γ} s) {suc m}{suc n} (s≤s m≤n) {γ}{γ'} eq =
  first-≤ (s≤s m≤n) (tail (s ⟨ suc n , γ ⟩'))
    ≡⟨ first-≤-tail (s≤s m≤n) (s ⟨ suc n , γ ⟩') ⟩
  tail (first-≤ (s≤s (s≤s m≤n)) (s ⟨ suc n , γ ⟩'))
    ≡⟨ cong tail (naturality s (s≤s m≤n) eq) ⟩
  tail (s ⟨ suc m , γ' ⟩') ∎
  where open ≡-Reasoning

str-cons : {Γ : Ctx 0ℓ} → Tm Γ (Nat' ⊠ (▻ Stream)) → Tm Γ Stream
term (str-cons t) zero γ = fst t ⟨ zero , γ ⟩' ∷ []
term (str-cons t) (suc n) γ = (fst t ⟨ suc n , _ ⟩') ∷ (snd t ⟨ suc n , γ ⟩')
naturality (str-cons t) {zero} {zero} z≤n eq = cong (λ x → proj₁ x ∷ []) (naturality t z≤n eq)
naturality (str-cons t) {zero} {suc n} z≤n eq = cong (λ x → proj₁ x ∷ []) (naturality t z≤n eq)
naturality (str-cons {Γ = Γ} t) {suc m}{suc n} (s≤s m≤n) eq =
  cong₂ _∷_ (cong proj₁ (naturality t (s≤s m≤n) eq)) (naturality (snd t) (s≤s m≤n) eq)

to-str[_]_ : {Δ Γ : Ctx 0ℓ} (σ : Δ ⇒ Γ) → Tm Δ Stream → Tm Δ (Stream [ σ ])
to-str[_]_ {Δ = Δ}{Γ} σ s = convert-subst (!◇ Δ ◼) (!◇ Γ ∷ σ ◼) (◇-terminal Δ _ _) s

str-snd : {Γ : Ctx 0ℓ} → Tm Γ Stream → Tm Γ (▻ Nat')
str-snd s = next (str-head (prev (str-tail s)))

str-thrd : {Γ : Ctx 0ℓ} → Tm Γ Stream → Tm Γ (▻ (▻ Nat'))
str-thrd s = next (next (str-head (prev (str-tail (prev (str-tail s))))))

zeros : Tm ◇ Stream
zeros = {!Löb Stream (lam (▻' Stream) (to-str[ π ] str-cons (pair zero' (α ξ))))!}
  where
    α : Tm (◇ ,, ▻' Stream) (▻' Stream [ π {T = ▻' Stream} ]) → Tm (◇ ,, ▻' Stream) (▻ Stream)
    α t = {!!}

str-map : Tm ◇ (Nat' ⇛ Nat') → Tm ◇ (Stream ⇛ Stream)
str-map f = Löb (Stream ⇛ Stream) (lam (▻' (Stream ⇛ Stream)) {!lam Stream ?!})

generate : Tm ◇ (Nat' ⇛ Nat') → Tm ◇ (Nat' ⇛ Stream)
generate f = {!!}

nats : Tm ◇ Stream
nats = app (generate (lam Nat' {!suc' ξ!})) zero'
