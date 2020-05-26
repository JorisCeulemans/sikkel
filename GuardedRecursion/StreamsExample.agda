--------------------------------------------------
-- Examples with guarded streams
--------------------------------------------------

module GuardedRecursion.StreamsExample where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
open import Data.Vec.Base hiding ([_]; _⊛_)
open import Function using (id)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open import Level renaming (zero to lzero; suc to lsuc)

open import Categories
open import Helpers
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import GuardedRecursion.Later


--------------------------------------------------
-- Some basic operations and proves regarding vectors

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


--------------------------------------------------
-- Definition of guarded streams.

-- Just as with discrete types, guarded streams are first defined in the
-- empty context and then in any context using the terminal substitution.
Stream-prim : Ty (◇ {ω} {0ℓ})
type Stream-prim n _ = Vec ℕ (suc n)
morph Stream-prim m≤n _ = first-≤ (s≤s m≤n)
morph-id Stream-prim _ = first-≤-refl
morph-comp Stream-prim k≤m m≤n _ _ = first-≤-trans (s≤s k≤m) (s≤s m≤n)

Stream : {Γ : Ctx ω 0ℓ} → Ty Γ
Stream {Γ = Γ} = Stream-prim [ !◇ Γ ]

str-head : {Γ : Ctx ω 0ℓ} → Tm Γ Stream → Tm Γ Nat'
term (str-head s) n γ = head (s ⟨ n , γ ⟩')
naturality (str-head {Γ = Γ} s) {m}{n} m≤n {γ}{γ'} eγ =
  head (s ⟨ n , γ ⟩')
    ≡⟨ first-≤-head m≤n (s ⟨ n , γ ⟩') ⟩
  head (Stream {Γ = Γ} ⟪ m≤n , eγ ⟫ (s ⟨ n , γ ⟩'))
    ≡⟨ cong head (naturality s m≤n eγ) ⟩
  head (s ⟨ m , γ' ⟩') ∎
  where open ≡-Reasoning

str-tail : {Γ : Ctx ω 0ℓ} → Tm Γ Stream → Tm Γ (▻ Stream)
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

str-cons : {Γ : Ctx ω 0ℓ} → Tm Γ (Nat' ⊠ (▻ Stream)) → Tm Γ Stream
term (str-cons t) zero γ = fst t ⟨ zero , γ ⟩' ∷ []
term (str-cons t) (suc n) γ = (fst t ⟨ suc n , _ ⟩') ∷ (snd t ⟨ suc n , γ ⟩')
naturality (str-cons t) {zero} {zero} z≤n eγ = cong (λ x → proj₁ x ∷ []) (naturality t z≤n eγ)
naturality (str-cons t) {zero} {suc n} z≤n eγ = cong (λ x → proj₁ x ∷ []) (naturality t z≤n eγ)
naturality (str-cons {Γ = Γ} t) {suc m}{suc n} (s≤s m≤n) eγ =
  cong₂ _∷_ (cong proj₁ (naturality t (s≤s m≤n) eγ)) (naturality (snd t) (s≤s m≤n) eγ)

stream-subst : {Δ Γ : Ctx ω 0ℓ} (σ : Δ ⇒ Γ) → Stream [ σ ] ≅ᵗʸ Stream
from (stream-subst σ) = record { func = id ; naturality = λ _ → refl }
to (stream-subst σ) = record { func = id ; naturality = λ _ → refl }
eq (isoˡ (stream-subst σ)) _ = refl
eq (isoʳ (stream-subst σ)) _ = refl


--------------------------------------------------
-- Some operations on guarded streams

str-snd : {Γ : Ctx ω 0ℓ} → Tm Γ Stream → Tm Γ (▻ Nat')
str-snd s = next (str-head (prev (str-tail s)))

str-thrd : {Γ : Ctx ω 0ℓ} → Tm Γ Stream → Tm Γ (▻ (▻ Nat'))
str-thrd s = next (next (str-head (prev (str-tail (prev (str-tail s))))))

zeros : Tm ◇ Stream
zeros = löb Stream (lam (▻' Stream) (
  ι[ stream-subst {Γ = ◇} (π {T = ▻' Stream}) ] (str-cons (pair zero' (ι[ β ] (ξ {Γ = ◇} {T = ▻' Stream}))))))
  where
    open ≅ᵗʸ-Reasoning
    β : ▻ Stream ≅ᵗʸ ▻' Stream [ π {Γ = ◇} {T = ▻' Stream} ]
    β = begin
          ▻ Stream
        ≅˘⟨ ▻-cong (stream-subst (from-earlier ◇ ⊚ ◄-subst (π {Γ = ◇} {T = ▻' Stream}))) ⟩
          ▻ (Stream [ from-earlier ◇ ⊚ ◄-subst (π {Γ = ◇} {T = ▻' Stream}) ])
        ≅˘⟨ ▻-cong {Γ = ◇ ,, ▻' Stream}
                    (ty-subst-comp Stream (from-earlier ◇) (◄-subst (π {Γ = ◇} {T = ▻' Stream}))) ⟩
          ▻ (Stream [ from-earlier ◇ ] [ ◄-subst (π {Γ = ◇} {T = ▻' Stream}) ])
        ≅˘⟨ ▻-natural (π {Γ = ◇} {T = ▻' Stream}) ⟩
          (▻ (Stream [ from-earlier ◇ ])) [ π {Γ = ◇} {T = ▻' Stream} ]
        ≅⟨⟩
          (▻' Stream) [ π {Γ = ◇} {T = ▻' Stream} ] ∎

{-
-- We should be able to write the following functions using Löb induction (and we probably can do so).
-- However, in these cases proofs of type equivalence such as β in the definition of zeros above
-- become even more complex. We will therefore first try to find out if these proofs can somehow
-- be generated automatically in order to make the system more user-friendly.

str-map : Tm (◇ {C = ω}) (Nat' ⇛ Nat') → Tm ◇ (Stream ⇛ Stream)
str-map f = löb (Stream ⇛ Stream) (lam (▻' (Stream ⇛ Stream)) {!lam Stream ?!})

generate : Tm (◇ {C = ω}) (Nat' ⇛ Nat') → Tm ◇ (Nat' ⇛ Stream)
generate f = {!!}

nats : Tm ◇ Stream
nats = app (generate (lam Nat' (ι[ Discr-subst ℕ (π {T = Nat'}) ] (suc' (ι⁻¹[ Discr-subst ℕ (π {T = Nat'}) ] (ξ {T = Nat'}))))))
           zero'
-}
