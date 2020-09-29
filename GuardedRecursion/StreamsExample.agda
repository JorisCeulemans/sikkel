{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- Examples with guarded streams of natural numbers
--------------------------------------------------

module GuardedRecursion.StreamsExample where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec.Base hiding ([_]; _⊛_)
open import Function using (id)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; subst)
open import Level renaming (zero to lzero; suc to lsuc)

open import Categories
open import Helpers
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import GuardedRecursion.Later
open import Reflection.Naturality
open import Reflection.NaturalityTactic

private
  variable
    Γ Δ : Ctx ω ℓ


--------------------------------------------------
-- Some basic operations and proofs regarding vectors

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

Stream : Ty Γ 0ℓ
type Stream n _ = Vec ℕ (suc n)
morph Stream m≤n _ = first-≤ (s≤s m≤n)
morph-id Stream _ = first-≤-refl
morph-comp Stream k≤m m≤n _ _ = first-≤-trans (s≤s k≤m) (s≤s m≤n)

str-head : Tm Γ Stream → Tm Γ Nat'
term (str-head s) n γ = head (s ⟨ n , γ ⟩')
naturality (str-head {Γ = Γ} s) {m}{n} m≤n {γ}{γ'} eγ =
  begin
    head (s ⟨ n , γ ⟩')
  ≡⟨ first-≤-head m≤n (s ⟨ n , γ ⟩') ⟩
    head (Stream {Γ = Γ} ⟪ m≤n , eγ ⟫ (s ⟨ n , γ ⟩'))
  ≡⟨ cong head (naturality s m≤n eγ) ⟩
    head (s ⟨ m , γ' ⟩') ∎
  where open ≡-Reasoning

str-tail : Tm Γ Stream → Tm Γ (▻' Stream)
term (str-tail s) zero _ = tt
term (str-tail s) (suc n) γ = tail (s ⟨ suc n , γ ⟩')
naturality (str-tail s) z≤n _ = refl
naturality (str-tail {Γ = Γ} s) {suc m}{suc n} (s≤s m≤n) {γ}{γ'} eγ =
  begin
    first-≤ (s≤s m≤n) (tail (s ⟨ suc n , γ ⟩'))
  ≡⟨ first-≤-tail (s≤s m≤n) (s ⟨ suc n , γ ⟩') ⟩
    tail (first-≤ (s≤s (s≤s m≤n)) (s ⟨ suc n , γ ⟩'))
  ≡⟨ cong tail (naturality s (s≤s m≤n) eγ) ⟩
    tail (s ⟨ suc m , γ' ⟩') ∎
  where open ≡-Reasoning

str-cons : Tm Γ (Nat' ⊠ (▻' Stream)) → Tm Γ Stream
term (str-cons t) zero γ = fst t ⟨ zero , γ ⟩' ∷ []
term (str-cons t) (suc n) γ = (fst t ⟨ suc n , _ ⟩') ∷ (snd t ⟨ suc n , γ ⟩')
naturality (str-cons t) {zero} {zero} z≤n eγ = cong (λ x → proj₁ x ∷ []) (naturality t z≤n eγ)
naturality (str-cons t) {zero} {suc n} z≤n eγ = cong (λ x → proj₁ x ∷ []) (naturality t z≤n eγ)
naturality (str-cons {Γ = Γ} t) {suc m}{suc n} (s≤s m≤n) eγ =
  cong₂ _∷_ (cong proj₁ (naturality t (s≤s m≤n) eγ)) (naturality (snd t) (s≤s m≤n) eγ)

stream-natural : (σ : Δ ⇒ Γ) → Stream [ σ ] ≅ᵗʸ Stream
from (stream-natural σ) = record { func = id ; naturality = λ _ → refl }
to (stream-natural σ) = record { func = id ; naturality = λ _ → refl }
eq (isoˡ (stream-natural σ)) _ = refl
eq (isoʳ (stream-natural σ)) _ = refl


--------------------------------------------------
-- Declarations needed for the naturality solver
-- This shows that it is easy to extend the solver to work with custom types
-- and type operations (even the ones that are only definable in a particular
-- base category).

instance
  stream-nul : IsNullaryNatural Stream
  natural-nul {{stream-nul}} = stream-natural

  ▻'-un : IsUnaryNatural ▻'
  natural-un {{▻'-un}} = ▻'-natural
  cong-un {{▻'-un}} = ▻'-cong

  ◄-functor : IsCtxFunctor ◄
  ctx-map {{◄-functor}} = ◄-subst
  ctx-map-id {{◄-functor}} = ◄-subst-id
  ctx-map-⊚ {{◄-functor}} = ◄-subst-⊚

  ▻-un : IsUnaryNatural ▻
  natural-un {{▻-un}} = ▻-natural
  cong-un {{▻-un}} = ▻-cong


--------------------------------------------------
-- Some operations on guarded streams

str-snd : Tm Γ Stream → Tm Γ (▻' Nat')
str-snd s = next' (lamι Stream (str-head (varι 0))) ⊛' str-tail s

str-thrd : Tm Γ Stream → Tm Γ (▻' (▻' Nat'))
str-thrd s = next' (lamι Stream (str-snd (varι 0))) ⊛' str-tail s

zeros : Tm Γ Stream
zeros = löb Stream
            (lamι (▻' Stream) (
                  str-cons (pair zero' (varι 0))))

private
  module _ {Γ : Ctx ω ℓ} where
    zeros-test : str-head {Γ = Γ} zeros ≅ᵗᵐ zero'
    eq zeros-test {x = zero}  _ = refl
    eq zeros-test {x = suc n} _ = refl

    zeros-test2 : str-snd {Γ = Γ} zeros ≅ᵗᵐ next' zero'
    eq zeros-test2 {x = zero}        _ = refl
    eq zeros-test2 {x = suc zero}    _ = refl
    eq zeros-test2 {x = suc (suc n)} _ = refl

str-map : Tm Γ (Nat' ⇛ Nat') → Tm Γ (Stream ⇛ Stream)
str-map f = löb (Stream ⇛ Stream)
                (lamι (▻' (Stream ⇛ Stream)) (
                      lamι Stream (
                           str-cons (pair (app (ι[ by-naturality ] ((f [ π ]') [ π ]')) (str-head (varι 0)))
                                          (varι 1 ⊛' str-tail (varι 0))))))

iterate : Tm Γ (Nat' ⇛ Nat') → Tm Γ (Nat' ⇛ Stream)
iterate f = löb (Nat' ⇛ Stream)
                (lamι (▻' (Nat' ⇛ Stream)) (
                      lamι Nat' (
                           str-cons (pair (varι 0)
                                          (varι 1 ⊛' next' (app (ι[ by-naturality ] ((f [ π ]') [ π ]')) (varι 0)))))))

iterate' : Tm Γ (Nat' ⇛ Nat') → Tm Γ (Nat' ⇛ Stream)
iterate' f = lamι Nat' (
                  löb Stream
                      (lamι (▻' Stream) (
                            str-cons (pair (varι 1)
                                           (next' (ι[ by-naturality ] ((str-map f [ π ]') [ π ]')) ⊛' varι 0)))))

suc-func : Tm Γ (Nat' ⇛ Nat')
suc-func = discr-func suc

nats : Tm Γ Stream
nats = app (iterate suc-func) zero'

private
  module _ {Γ : Ctx ω ℓ} where
    nats-test : str-head {Γ = Γ} nats ≅ᵗᵐ zero'
    eq nats-test {x = zero}  _ = refl
    eq nats-test {x = suc n} _ = refl

    nats-test2 : str-snd {Γ = Γ} nats ≅ᵗᵐ next' (suc' zero')
    eq nats-test2 {x = zero}        _ = refl
    eq nats-test2 {x = suc zero}    _ = refl
    eq nats-test2 {x = suc (suc n)} _ = refl

    nats-test3 : str-thrd {Γ = Γ} nats ≅ᵗᵐ next' (next' (suc' (suc' zero')))
    eq nats-test3 {x = zero}              _ = refl
    eq nats-test3 {x = suc zero}          _ = refl
    eq nats-test3 {x = suc (suc zero)}    _ = refl
    eq nats-test3 {x = suc (suc (suc n))} _ = refl

    map-test : str-head {Γ = Γ} (app (str-map suc-func) zeros) ≅ᵗᵐ discr 1
    eq map-test {x = zero}  _ = refl
    eq map-test {x = suc x} _ = refl

    map-test2 : str-thrd {Γ = Γ} (app (str-map suc-func) (app (str-map suc-func) nats)) ≅ᵗᵐ next' (next' (discr 4))
    eq map-test2 {x = zero}              _ = refl
    eq map-test2 {x = suc zero}          _ = refl
    eq map-test2 {x = suc (suc zero)}    _ = refl
    eq map-test2 {x = suc (suc (suc n))} _ = refl

mergef : Tm Γ (Nat' ⇛ Nat' ⇛ ▻' Stream ⇛ Stream) → Tm Γ (Stream ⇛ Stream ⇛ Stream)
mergef f = löb (Stream ⇛ Stream ⇛ Stream)
               (lamι (▻' (Stream ⇛ Stream ⇛ Stream)) (
                     lamι Stream (
                          lamι Stream (
                               let xs = varι 1
                                   ys = varι 0
                               in
                               app (app (app (ι[ by-naturality ] (((f [ π ]') [ π ]') [ π ]'))
                                             (str-head xs))
                                        (str-head ys))
                                   (varι 2 ⊛' str-tail xs ⊛' str-tail ys)))))
