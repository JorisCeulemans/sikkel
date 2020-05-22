module StreamsExample where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
open import Data.Vec.Base hiding ([_]; _⊛_)
open import Function
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
first-≤-refl {as = []} = refl
first-≤-refl {as = a ∷ as} = cong (a ∷_) first-≤-refl

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

str-head : {Γ : Ctx 0ℓ} → Tm Γ Stream → Tm Γ Nat'
term (str-head s) n γ = head (s ⟨ n , γ ⟩')
naturality (str-head {Γ = Γ} s) {m}{n} m≤n {γ}{γ'} eγ =
  head (s ⟨ n , γ ⟩')
    ≡⟨ first-≤-head m≤n (s ⟨ n , γ ⟩') ⟩
  head (Stream {Γ = Γ} ⟪ m≤n , eγ ⟫ (s ⟨ n , γ ⟩'))
    ≡⟨ cong head (naturality s m≤n eγ) ⟩
  head (s ⟨ m , γ' ⟩') ∎
  where open ≡-Reasoning

str-tail : {Γ : Ctx 0ℓ} → Tm Γ Stream → Tm Γ (▻ Stream)
term (str-tail s) zero _ = lift tt
term (str-tail s) (suc n) γ = tail (s ⟨ suc n , γ ⟩')
naturality (str-tail s) z≤n _ = refl
naturality (str-tail {Γ = Γ} s) {suc m}{suc n} (s≤s m≤n) {γ}{γ'} eγ =
  first-≤ (s≤s m≤n) (tail (s ⟨ suc n , γ ⟩'))
    ≡⟨ first-≤-tail (s≤s m≤n) (s ⟨ suc n , γ ⟩') ⟩
  tail (first-≤ (s≤s (s≤s m≤n)) (s ⟨ suc n , γ ⟩'))
    ≡⟨ cong tail (naturality s (s≤s m≤n) eγ) ⟩
  tail (s ⟨ suc m , γ' ⟩') ∎
  where open ≡-Reasoning

str-cons : {Γ : Ctx 0ℓ} → Tm Γ (Nat' ⊠ (▻ Stream)) → Tm Γ Stream
term (str-cons t) zero γ = fst t ⟨ zero , γ ⟩' ∷ []
term (str-cons t) (suc n) γ = (fst t ⟨ suc n , _ ⟩') ∷ (snd t ⟨ suc n , γ ⟩')
naturality (str-cons t) {zero} {zero} z≤n eγ = cong (λ x → proj₁ x ∷ []) (naturality t z≤n eγ)
naturality (str-cons t) {zero} {suc n} z≤n eγ = cong (λ x → proj₁ x ∷ []) (naturality t z≤n eγ)
naturality (str-cons {Γ = Γ} t) {suc m}{suc n} (s≤s m≤n) eγ =
  cong₂ _∷_ (cong proj₁ (naturality t (s≤s m≤n) eγ)) (naturality (snd t) (s≤s m≤n) eγ)

stream-subst : {Δ Γ : Ctx 0ℓ} (σ : Δ ⇒ Γ) → Stream [ σ ] ≅ᵗʸ Stream
from (stream-subst σ) = record { func = id ; naturality = λ _ → refl }
to (stream-subst σ) = record { func = id ; naturality = λ _ → refl }
eq (isoˡ (stream-subst σ)) _ = refl
eq (isoʳ (stream-subst σ)) _ = refl

str-snd : {Γ : Ctx 0ℓ} → Tm Γ Stream → Tm Γ (▻ Nat')
str-snd s = next (str-head (prev (str-tail s)))

str-thrd : {Γ : Ctx 0ℓ} → Tm Γ Stream → Tm Γ (▻ (▻ Nat'))
str-thrd s = next (next (str-head (prev (str-tail (prev (str-tail s))))))

zeros : Tm ◇ Stream
zeros = löb Stream (lam (▻' {Γ = ◇} Stream) (ι[ stream-subst {Γ = ◇} (π {T = ▻' Stream}) ] str-cons (pair {T = Nat'} {S = ▻ Stream} zero' (α (ξ {Γ = ◇} {T = ▻' Stream})))))
  where
    Γ = ◇ ,, ▻' Stream
    open ≅ᵗʸ-Reasoning
    β : ▻ {Γ = Γ} Stream ≅ᵗʸ (▻' {Γ = ◇} Stream [ π {Γ = ◇} {T = ▻' Stream} ])
    β = begin
          ▻ {Γ = Γ} Stream
        ≅˘⟨ ▻-cong {Γ = Γ} (stream-subst {Δ = ◄ Γ} {Γ = ◇} (from-earlier ◇ ⊚ ◄-subst (π {Γ = ◇} {T = ▻' Stream}))) ⟩
          ▻ {Γ = Γ} (Stream [ from-earlier ◇ ⊚ ◄-subst (π {Γ = ◇} {T = ▻' Stream}) ])
        ≅˘⟨ ▻-cong {Γ = Γ} {T = Stream [ from-earlier ◇ ] [ ◄-subst (π {Γ = ◇} {T = ▻' Stream}) ]} {T' = Stream [ from-earlier ◇ ⊚ ◄-subst (π {Γ = ◇} {T = ▻' Stream}) ]} (ty-subst-comp (Stream {Γ = ◇}) (from-earlier ◇) (◄-subst (π {Γ = ◇} {T = ▻' Stream}))) ⟩
          ▻ {Γ = Γ} (Stream [ from-earlier ◇ ] [ ◄-subst (π {Γ = ◇} {T = ▻' Stream}) ])
        ≅˘⟨ ▻-natural (π {Γ = ◇} {T = ▻' Stream}) {T = Stream [ from-earlier ◇ ]} ⟩
          (▻ {Γ = ◇} (Stream [ from-earlier ◇ ])) [ π {Γ = ◇} {T = ▻' Stream} ]
        ≅⟨⟩
          (▻' {Γ = ◇} Stream) [ π {Γ = ◇} {T = ▻' Stream} ] ∎
    α : Tm Γ ((▻' {Γ = ◇} Stream) [ π {T = ▻' Stream} ]) → Tm Γ (▻ Stream)
    α t = ι[ β ] t

{-
str-map : Tm ◇ (Nat' ⇛ Nat') → Tm ◇ (Stream ⇛ Stream)
str-map f = Löb (Stream ⇛ Stream) (lam (▻' (Stream ⇛ Stream)) {!lam Stream ?!})

generate : Tm ◇ (Nat' ⇛ Nat') → Tm ◇ (Nat' ⇛ Stream)
generate f = {!!}

nats : Tm ◇ Stream
nats = app (generate (lam Nat' {!suc' ξ!})) zero'
-}
