{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- Examples with guarded streams of natural numbers
--
-- Note that the option omega-in-omega is used to
-- make the type GStream an instance of IsNullaryNatural.
-- This code should typecheck without this option in Agda
-- 2.6.2 once released.
--------------------------------------------------

module GuardedRecursion.GuardedStreams where

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
open import Reflection.Naturality.Instances
open import Reflection.Tactic.Lambda
open import Reflection.Tactic.LobInduction

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

GStream : Ty Γ 0ℓ
type GStream n _ = Vec ℕ (suc n)
morph GStream m≤n _ = first-≤ (s≤s m≤n)
morph-cong GStream refl = refl
morph-id GStream _ = first-≤-refl
morph-comp GStream k≤m m≤n _ _ = first-≤-trans (s≤s k≤m) (s≤s m≤n)

{-
g-head : Tm Γ GStream → Tm Γ Nat'
term (g-head s) n γ = head (s ⟨ n , γ ⟩')
naturality (g-head {Γ = Γ} s) {m}{n} m≤n {γ}{γ'} eγ =
  begin
    head (s ⟨ n , γ ⟩')
  ≡⟨ first-≤-head m≤n (s ⟨ n , γ ⟩') ⟩
    head (GStream {Γ = Γ} ⟪ m≤n , eγ ⟫ (s ⟨ n , γ ⟩'))
  ≡⟨ cong head (naturality s m≤n eγ) ⟩
    head (s ⟨ m , γ' ⟩') ∎
  where open ≡-Reasoning
-}

g-head : Tm Γ (GStream ⇛ Nat')
_$⟨_,_⟩_ (term g-head n γn) _ _ = head
naturality (term g-head n γn) _ _ v = sym (first-≤-head _ v)
naturality g-head m≤n eγ = to-pshfun-eq (λ _ _ _ → refl)

{-
g-tail : Tm Γ GStream → Tm Γ (▻' GStream)
term (g-tail s) zero _ = tt
term (g-tail s) (suc n) γ = tail (s ⟨ suc n , γ ⟩')
naturality (g-tail s) z≤n _ = refl
naturality (g-tail {Γ = Γ} s) {suc m}{suc n} (s≤s m≤n) {γ}{γ'} eγ =
  begin
    first-≤ (s≤s m≤n) (tail (s ⟨ suc n , γ ⟩'))
  ≡⟨ first-≤-tail (s≤s m≤n) (s ⟨ suc n , γ ⟩') ⟩
    tail (first-≤ (s≤s (s≤s m≤n)) (s ⟨ suc n , γ ⟩'))
  ≡⟨ cong tail (naturality s (s≤s m≤n) eγ) ⟩
    tail (s ⟨ suc m , γ' ⟩') ∎
  where open ≡-Reasoning
-}

g-tail : Tm Γ (GStream ⇛ ▻' GStream)
_$⟨_,_⟩_ (term g-tail n γn) z≤n       _ = λ _ → tt
_$⟨_,_⟩_ (term g-tail n γn) (s≤s m≤n) _ = tail
naturality (term g-tail n γn) {ρ-xy = z≤n}     {ρ-yz = m≤n}     _ _ _ = refl
naturality (term g-tail n γn) {ρ-xy = s≤s k≤m} {ρ-yz = s≤s m≤n} _ _ v = sym (first-≤-tail (s≤s k≤m) v)
naturality g-tail z≤n       eγ = to-pshfun-eq λ { z≤n _ _ → refl }
naturality g-tail (s≤s m≤n) eγ = to-pshfun-eq λ { z≤n _ _ → refl ; (s≤s k≤m) _ _ → refl }

{-
g-cons : Tm Γ (Nat' ⊠ (▻' GStream)) → Tm Γ GStream
term (g-cons t) zero γ = fst t ⟨ zero , γ ⟩' ∷ []
term (g-cons t) (suc n) γ = (fst t ⟨ suc n , _ ⟩') ∷ (snd t ⟨ suc n , γ ⟩')
naturality (g-cons t) {zero} {zero} z≤n eγ = cong (λ x → proj₁ x ∷ []) (naturality t z≤n eγ)
naturality (g-cons t) {zero} {suc n} z≤n eγ = cong (λ x → proj₁ x ∷ []) (naturality t z≤n eγ)
naturality (g-cons {Γ = Γ} t) {suc m}{suc n} (s≤s m≤n) eγ =
  cong₂ _∷_ (cong proj₁ (naturality t (s≤s m≤n) eγ)) (naturality (snd t) (s≤s m≤n) eγ)
-}

g-cons : Tm Γ (Nat' ⊠ ▻' GStream ⇛ GStream)
_$⟨_,_⟩_ (term g-cons n γn) z≤n       _ [ h , _ ] = h ∷ []
_$⟨_,_⟩_ (term g-cons n γn) (s≤s m≤n) _ [ h , t ] = h ∷ t
naturality (term g-cons n γn) {ρ-xy = z≤n}     {ρ-yz = z≤n}     _ _ _ = refl
naturality (term g-cons n γn) {ρ-xy = z≤n}     {ρ-yz = s≤s m≤n} _ _ _ = refl
naturality (term g-cons n γn) {ρ-xy = s≤s k≤m} {ρ-yz = s≤s m≤n} _ _ _ = refl
naturality g-cons z≤n       _ = to-pshfun-eq λ { z≤n _ _ → refl }
naturality g-cons (s≤s m≤n) _ = to-pshfun-eq λ { z≤n _ _ → refl ; (s≤s k≤m) _ _ → refl }

gstream-natural : (σ : Δ ⇒ Γ) → GStream [ σ ] ≅ᵗʸ GStream
func (from (gstream-natural σ)) = id
naturality (from (gstream-natural σ)) _ = refl
func (to (gstream-natural σ)) = id
naturality (to (gstream-natural σ)) _ = refl
eq (isoˡ (gstream-natural σ)) _ = refl
eq (isoʳ (gstream-natural σ)) _ = refl


--------------------------------------------------
-- Declarations needed for the naturality solver
-- This shows that it is easy to extend the solver to work with custom types
-- and type operations (even the ones that are only definable in a particular
-- base category).

instance
  gstream-nul : IsNullaryNatural GStream
  natural-nul {{gstream-nul}} = gstream-natural

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
--
-- Most functions are an implementation of the examples on pages 8-10 of the paper
--   Ranald Clouston, Aleš Bizjak, Hans Bugge Grathwohl, and Lars Birkedal.
--   The guarded lambda-calculus: Programming and reasoning with guarded recursion for coinductive types.
--   Logical Methods of Computer Science (LMCS), 12(3), 2016.

{-
g-snd : Tm Γ GStream → Tm Γ (▻' Nat')
g-snd s = next' (lamι GStream (g-head $ varι 0)) ⊛' g-tail $ s
-}

g-snd : Tm Γ (GStream ⇛ ▻' Nat')
g-snd = lamι GStream (next' g-head ⊛' (g-tail $ varι 0))

{-
g-thrd : Tm Γ GStream → Tm Γ (▻' (▻' Nat'))
g-thrd s = next' (lamι GStream (g-snd (varι 0))) ⊛' g-tail $ s
-}

g-thrd : Tm Γ (GStream ⇛ ▻' (▻' Nat'))
g-thrd = lamι GStream (next' g-snd ⊛' (g-tail $ varι 0))

g-zeros : Tm Γ GStream
g-zeros = löbι GStream (g-cons $ pair zero' (varι 0))

private
  module _ {Γ : Ctx ω ℓ} where
    zeros-test : g-head {Γ = Γ} $ g-zeros ≅ᵗᵐ zero'
    eq zeros-test {x = zero}  _ = refl
    eq zeros-test {x = suc n} _ = refl

    zeros-test2 : g-snd {Γ = Γ} $ g-zeros ≅ᵗᵐ next' zero'
    eq zeros-test2 {x = zero}        _ = refl
    eq zeros-test2 {x = suc zero}    _ = refl
    eq zeros-test2 {x = suc (suc n)} _ = refl

{-
g-map' : Tm Γ (Nat' ⇛ Nat') → Tm Γ (GStream ⇛ GStream)
g-map' f = löbι (GStream ⇛ GStream) (
                lamι GStream (
                     g-cons $ (pair (app (↑ι⟨ 2 ⟩ f) (g-head $ varι 0))
                                    (varι 1 ⊛' g-tail $ varι 0))))
-}

g-map : Tm Γ ((Nat' ⇛ Nat') ⇛ GStream ⇛ GStream)
g-map = lamι (Nat' ⇛ Nat') (
             löbι (GStream ⇛ GStream) (
                  lamι GStream
                       (g-cons $ pair (varι 2 $ (g-head $ varι 0))
                                      (varι 1 ⊛' (g-tail $ varι 0)))))

{-
g-iterate : Tm Γ (Nat' ⇛ Nat') → Tm Γ (Nat' ⇛ GStream)
g-iterate f = löbι (Nat' ⇛ GStream) (
                   lamι Nat' (
                        g-cons $ (pair (varι 0)
                                       (varι 1 ⊛' next' (app (↑ι⟨ 2 ⟩ f) (varι 0))))))
-}

g-iterate-func : Tm Γ ((Nat' ⇛ Nat') ⇛ Nat' ⇛ GStream)
g-iterate-func = lamι (Nat' ⇛ Nat') (
                      löbι (Nat' ⇛ GStream) (
                           lamι Nat' (
                                g-cons $ pair (varι 0)
                                              (varι 1 ⊛' next' (varι 2 $ varι 0)))))

{-
g-iterate' : Tm Γ (Nat' ⇛ Nat') → Tm Γ (Nat' ⇛ GStream)
g-iterate' f = lamι Nat' (
                    löbι GStream (
                         g-cons $ (pair (varι 1)
                                        (next' (↑ι⟨ 2 ⟩ (g-map $ f)) ⊛' varι 0))))
-}

g-iterate'-func : Tm Γ ((Nat' ⇛ Nat') ⇛ Nat' ⇛ GStream)
g-iterate'-func = lamι (Nat' ⇛ Nat') (
                       lamι Nat' (
                            löbι GStream (
                                 g-cons $ pair (varι 1)
                                               (next' (g-map $ varι 2) ⊛' varι 0))))

suc-func : Tm Γ (Nat' ⇛ Nat')
suc-func = discr-func suc

g-nats : Tm Γ GStream
g-nats = g-iterate'-func $ suc-func $ zero'

private
  module _ {Γ : Ctx ω ℓ} where
    nats-test : g-head {Γ = Γ} $ g-nats ≅ᵗᵐ zero'
    eq nats-test {x = zero}  _ = refl
    eq nats-test {x = suc n} _ = refl

    nats-test2 : g-snd {Γ = Γ} $ g-nats ≅ᵗᵐ next' (suc' zero')
    eq nats-test2 {x = zero}        _ = refl
    eq nats-test2 {x = suc zero}    _ = refl
    eq nats-test2 {x = suc (suc n)} _ = refl

    nats-test3 : g-thrd {Γ = Γ} $ g-nats ≅ᵗᵐ next' (next' (suc' (suc' zero')))
    eq nats-test3 {x = zero}              _ = refl
    eq nats-test3 {x = suc zero}          _ = refl
    eq nats-test3 {x = suc (suc zero)}    _ = refl
    eq nats-test3 {x = suc (suc (suc n))} _ = refl

    map-test : g-head {Γ = Γ} $ (g-map $ suc-func $ g-zeros) ≅ᵗᵐ discr 1
    eq map-test {x = zero}  _ = refl
    eq map-test {x = suc x} _ = refl

    map-test2 : g-thrd {Γ = Γ} $ (g-map $ suc-func $ (g-map $ suc-func $ g-nats)) ≅ᵗᵐ next' (next' (discr 4))
    eq map-test2 {x = zero}              _ = refl
    eq map-test2 {x = suc zero}          _ = refl
    eq map-test2 {x = suc (suc zero)}    _ = refl
    eq map-test2 {x = suc (suc (suc n))} _ = refl

g-interleave : Tm Γ (GStream ⇛ ▻' GStream ⇛ GStream)
g-interleave = löbι (GStream ⇛ ▻' GStream ⇛ GStream)
                    (lamι GStream
                          (lamι (▻' GStream)
                                (g-cons $ (pair (g-head $ varι 1)
                                                (varι 2 ⊛' varι 0 ⊛' next' (g-tail $ varι 1))))))

g-toggle : Tm Γ GStream
g-toggle = löbι GStream
                (g-cons $ pair (suc' zero')
                               (next' (g-cons $ pair zero' (varι 0))))

g-paperfolds : Tm Γ GStream
g-paperfolds = löbι GStream (g-interleave $ g-toggle $ varι 0)

module _ (T-op : NullaryTypeOp ω ℓ) {{_ : IsNullaryNatural T-op}} where
  T : Ty Γ ℓ
  T = ⟦ nul T-op ⟧exp

  g-initial : Tm Γ ((Nat' ⊠ ▻' T ⇛ T) ⇛ GStream ⇛ T)
  g-initial = löbι ((Nat' ⊠ ▻' T ⇛ T) ⇛ GStream ⇛ T)
                   (lamι (Nat' ⊠ ▻' T ⇛ T)
                         (lamι GStream
                               (varι 1 $ (pair (g-head $ varι 0)
                                               (varι 2 ⊛' next' (varι 1) ⊛' (g-tail $ varι 0))))))

  g-final : Tm Γ ((T ⇛ Nat' ⊠ ▻' T) ⇛ T ⇛ GStream)
  g-final = löbι ((T ⇛ Nat' ⊠ ▻' T) ⇛ T ⇛ GStream)
                 (lamι (T ⇛ Nat' ⊠ ▻' T)
                       (lamι T let x = varι 1 $ varι 0
                               in g-cons $ (pair (fst x)
                                                 (varι 2 ⊛' next' (varι 1) ⊛' snd x))))

-- This is an implementation of an example on page 3 of the paper
--   Robert Atkey, and Conor McBride.
--   Productive Coprogramming with Guarded Recursion.
--   ICFP 2013.
g-mergef : Tm Γ (Nat' ⇛ Nat' ⇛ ▻' GStream ⇛ GStream) → Tm Γ (GStream ⇛ GStream ⇛ GStream)
g-mergef f = löbι (GStream ⇛ GStream ⇛ GStream) (
                  lamι GStream (
                       lamι GStream (
                            let xs = varι 1
                                ys = varι 0
                            in app (app (app (↑ι⟨ 3 ⟩ f)
                                             (g-head $ xs))
                                        (g-head $ ys))
                                   (varι 2 ⊛' (g-tail $ xs) ⊛' (g-tail $ ys)))))

{-
g-mergef : Tm Γ ((Nat' ⇛ Nat' ⇛ ▻' GStream ⇛ GStream) ⇛ GStream ⇛ GStream ⇛ GStream)
g-mergef = lamι (Nat' ⇛ Nat' ⇛ ▻' GStream ⇛ GStream) (
                löbι (GStream ⇛ GStream ⇛ GStream) (
                     lamι GStream (
                          lamι GStream (
                               let xs = varι 1
                                   ys = varι 0
                               in varι 3 $ (g-head $ xs)
                                         $ (g-head $ ys)
                                         $ (varι 2 ⊛' (g-tail $ xs) ⊛' (g-tail $ ys))))))
-}

-- Examples that were not taken from a paper.
g-zipWith : Tm Γ (Nat' ⇛ Nat' ⇛ Nat') → Tm Γ (GStream ⇛ GStream ⇛ GStream)
g-zipWith f = g-mergef (
  lamι Nat' (
       lamι Nat' (
            lamι (▻' GStream) (
                 g-cons $ (pair (app (app (↑ι⟨ 3 ⟩ f) (varι 2)) (varι 1))
                                (varι 0))))))

{-
nat-sum : Tm Γ (Nat' ⇛ Nat' ⇛ Nat')
nat-sum = nat-elim (Nat' ⇛ Nat')
                   (lamι Nat' (varι 0))
                   (lamι (Nat' ⇛ Nat') (
                         lamι Nat' (suc' (app (varι 1) (varι 0)))))
-}

prim-nat-sum : Tm Γ Nat' → Tm Γ Nat' → Tm Γ Nat'
term (prim-nat-sum t s) n γ = t ⟨ n , γ ⟩' + s ⟨ n , γ ⟩'
naturality (prim-nat-sum t s) m≤n eγ = cong₂ _+_ (naturality t m≤n eγ) (naturality s m≤n eγ)

nat-sum : Tm Γ (Nat' ⇛ Nat' ⇛ Nat')
nat-sum = lamι Nat' (lamι Nat' (prim-nat-sum (varι 0) (varι 1)))

pair' : Tm Γ (Nat' ⇛ ▻' GStream ⇛ Nat' ⊠ ▻' GStream)
pair' = lamι Nat' (lamι (▻' GStream) (pair (varι 1) (varι 0)))

one' : Tm Γ Nat'
one' = suc' zero'

g-fibs : Tm Γ GStream
g-fibs = löbι GStream (
  g-cons $ pair one' (
  g-cons ⟨$⟩' ((pair' $ one') ⟨$⟩' (
  (f $ varι 0) ⟨$⟩' (g-tail ⟨$⟩' varι 0)))))
  where
    f : Tm Γ (▻' GStream ⇛ ▻' GStream ⇛ ▻' GStream)
    f = lamι (▻' GStream) (
             lamι (▻' GStream) (
                  g-zipWith nat-sum ⟨$⟩' varι 1 ⊛' varι 0))

private
  module _ where
    fibs-test : g-thrd {Γ = Γ} $ g-fibs ≅ᵗᵐ next' (next' (discr 2))
    eq fibs-test {x = zero} _ = refl
    eq fibs-test {x = suc zero} _ = refl
    eq fibs-test {x = suc (suc zero)} _ = refl
    eq fibs-test {x = suc (suc (suc x))} _ = refl
