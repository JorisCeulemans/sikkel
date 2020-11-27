{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- Examples with guarded streams of natural numbers in mode ω
--
-- Note that the option omega-in-omega is used to
-- make the type GStream an instance of IsNullaryNatural.
-- This code should typecheck without this option in Agda
-- 2.6.2 once released.
--------------------------------------------------

module GuardedRecursion.Streams.Guarded where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
--open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec hiding ([_]; _⊛_)
open import Data.Vec.Properties
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; subst)
open import Level renaming (zero to lzero; suc to lsuc)

open import Categories
open import Helpers
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import GuardedRecursion.Modalities
open import Reflection.Naturality
open import Reflection.Naturality.Instances
open import Reflection.Naturality.GuardedRecursion.Instances
open import Reflection.Tactic.Lambda
open import Reflection.Tactic.LobInduction

private
  variable
    ℓa ℓc : Level
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

map-first-≤ : ∀ {m n} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (m≤n : m ≤ n) (as : Vec A n) →
              map f (first-≤ m≤n as) ≡ first-≤ m≤n (map f as)
map-first-≤ f z≤n       as       = refl
map-first-≤ f (s≤s m≤n) (a ∷ as) = cong (f a ∷_) (map-first-≤ f m≤n as)

first-≤-head : ∀ {m n} {A : Set ℓ} (m≤n : m ≤ n) (as : Vec A (suc n)) →
               head (first-≤ (s≤s m≤n) as) ≡ head as
first-≤-head m≤n (a ∷ as) = refl

map-head : ∀ {n} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (as : Vec A (suc n)) →
           head (map f as) ≡ f (head as)
map-head f (a ∷ as) = refl

first-≤-tail : ∀ {m n} {A : Set ℓ} (m≤n : m ≤ n) (as : Vec A (suc n)) →
               tail (first-≤ (s≤s m≤n) as) ≡ first-≤ m≤n (tail as)
first-≤-tail m≤n (a ∷ as) = refl

map-tail : ∀ {n} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (as : Vec A (suc n)) →
           tail (map f as) ≡ map f (tail as)
map-tail f (a ∷ as) = refl

map-map-cong : ∀ {n ℓa ℓb ℓc ℓd} {A : Set ℓa} {B : Set ℓb} {C : Set ℓc} {D : Set ℓd}
               {f : A → B} {g : B → D} {f' : A → C} {g' : C → D} (e : g ∘ f ≗ g' ∘ f')
               (as : Vec A n) →
               map g (map f as) ≡ map g' (map f' as)
map-map-cong {f = f}{g}{f'}{g'} e as =
  begin
    map g (map f as)
  ≡˘⟨ map-∘ g f as ⟩
    map (g ∘ f) as
  ≡⟨ map-cong e as ⟩
    map (g' ∘ f') as
  ≡⟨ map-∘ g' f' as ⟩
    map g' (map f' as) ∎
  where open ≡-Reasoning

map-inverse : ∀ {n} {A : Set ℓ} {B : Set ℓ'}
              {f : A → B} {g : B → A} (e : g ∘ f ≗ id)
              (as : Vec A n) →
              map g (map f as) ≡ as
map-inverse {f = f}{g} e as =
  begin
    map g (map f as)
  ≡˘⟨ map-∘ g f as ⟩
    map (g ∘ f) as
  ≡⟨ map-cong e as ⟩
    map id as
  ≡⟨ map-id as ⟩
    as ∎
  where open ≡-Reasoning


--------------------------------------------------
-- Definition of guarded streams.

GStream : Ty (now Γ) ℓ → Ty Γ ℓ
type (GStream {Γ = Γ} A) n γ = Vec (timeless-ty A ⟨ n , γ ⟩) (suc n)
morph (GStream A) m≤n eγ v = map (timeless-ty A ⟪ m≤n , eγ ⟫) (first-≤ (s≤s m≤n) v)
morph-cong (GStream A) refl = map-cong (λ _ → morph-cong A refl) _
morph-id (GStream A) v =
  begin
    map (timeless-ty A ⟪ ≤-refl , _ ⟫_) (first-≤ (s≤s ≤-refl) v)
  ≡⟨ map-cong (λ a → morph-id (timeless-ty A) a) (first-≤ (s≤s ≤-refl) v) ⟩
    map id (first-≤ (s≤s ≤-refl) v)
  ≡⟨ map-id (first-≤ (s≤s ≤-refl) v) ⟩
    first-≤ (s≤s ≤-refl) v
  ≡⟨ first-≤-refl ⟩
    v ∎
  where open ≡-Reasoning
morph-comp (GStream A) k≤m m≤n eγ-zy eγ-yx v =
  begin
    map (timeless-ty A ⟪ ≤-trans k≤m m≤n , _ ⟫_) (first-≤ (s≤s (≤-trans k≤m m≤n)) v)
  ≡⟨ cong (map (timeless-ty A ⟪ ≤-trans k≤m m≤n , _ ⟫_)) (first-≤-trans (s≤s k≤m) (s≤s m≤n) v) ⟩
    map (timeless-ty A ⟪ ≤-trans k≤m m≤n , _ ⟫_) (first-≤ (s≤s k≤m) (first-≤ (s≤s m≤n) v))
  ≡⟨ map-cong (λ a → morph-comp (timeless-ty A) k≤m m≤n eγ-zy eγ-yx a) _ ⟩
    map (timeless-ty A ⟪ k≤m , eγ-yx ⟫_ ∘ timeless-ty A ⟪ m≤n , eγ-zy ⟫_) (first-≤ (s≤s k≤m) (first-≤ (s≤s m≤n) v))
  ≡⟨ map-∘ (timeless-ty A ⟪ k≤m , eγ-yx ⟫_) (timeless-ty A ⟪ m≤n , eγ-zy ⟫_) _ ⟩
    map (timeless-ty A ⟪ k≤m , eγ-yx ⟫_) (map (timeless-ty A ⟪ m≤n , eγ-zy ⟫_)
      (first-≤ (s≤s k≤m) (first-≤ (s≤s m≤n) v)))
  ≡⟨ cong (map (timeless-ty A ⟪ k≤m , eγ-yx ⟫_)) (map-first-≤ (timeless-ty A ⟪ m≤n , eγ-zy ⟫_) (s≤s k≤m) _) ⟩
    map (timeless-ty A ⟪ k≤m , eγ-yx ⟫_) (first-≤ (s≤s k≤m)
      (map (timeless-ty A ⟪ m≤n , eγ-zy ⟫_) (first-≤ (s≤s m≤n) v))) ∎
  where open ≡-Reasoning

module _ {A : Ty (now Γ) ℓ} where
  g-head : Tm Γ (GStream A ⇛ timeless-ty A)
  _$⟨_,_⟩_ (term g-head n γn) _ _ = head
  naturality (term g-head n γn) _ _ v =
    begin
      head (map (timeless-ty A ⟪ _ , _ ⟫_) (first-≤ (s≤s _) v))
    ≡⟨ map-head (timeless-ty A ⟪ _ , _ ⟫_) (first-≤ (s≤s _) v) ⟩
      timeless-ty A ⟪ _ , _ ⟫ (head (first-≤ (s≤s _) v))
    ≡⟨ cong (timeless-ty A ⟪ _ , _ ⟫_) (first-≤-head _ v) ⟩
      timeless-ty A ⟪ _ , _ ⟫ head v ∎
    where open ≡-Reasoning
  naturality g-head m≤n eγ = to-pshfun-eq λ _ _ _ → refl

  g-tail : Tm Γ (GStream A ⇛ ▻' (GStream A))
  _$⟨_,_⟩_ (term g-tail n γn) z≤n       _ = λ _ → _ -- = tt
  _$⟨_,_⟩_ (term g-tail n γn) (s≤s m≤n) _ = map (timeless-ty A ⟪ n≤1+n _ , refl ⟫_) ∘ tail
  naturality (term g-tail n γn) {ρ-xy = z≤n}     {ρ-yz = m≤n}     _ _ _ = refl
  naturality (term g-tail n γn) {ρ-xy = s≤s k≤m} {ρ-yz = s≤s m≤n} _ _ v = -- {!sym (first-≤-tail (s≤s k≤m) v)!}
    begin
      map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_) (tail (map (timeless-ty A ⟪ s≤s k≤m , _ ⟫_) (first-≤ (s≤s (s≤s k≤m)) v)))
    ≡⟨ cong (map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_)) (map-tail (timeless-ty A ⟪ s≤s k≤m , _ ⟫_) (first-≤ (s≤s (s≤s k≤m)) v)) ⟩
      map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_) (map (timeless-ty A ⟪ s≤s k≤m , _ ⟫_) (tail (first-≤ (s≤s (s≤s k≤m)) v)))
    ≡⟨ map-map-cong (λ _ → morph-cong-2-2 (timeless-ty A) (≤-irrelevant _ _)) _ ⟩
      map (timeless-ty A ⟪ k≤m , _ ⟫_) (map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_) (tail (first-≤ (s≤s (s≤s k≤m)) v)))
    ≡⟨ cong (map (timeless-ty A ⟪ k≤m , _ ⟫_) ∘ map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_)) (first-≤-tail (s≤s k≤m) v) ⟩
      map (timeless-ty A ⟪ k≤m , _ ⟫_) (map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_) (first-≤ (s≤s k≤m) (tail v)))
    ≡⟨ cong (map (timeless-ty A ⟪ k≤m , _ ⟫_)) (map-first-≤ (timeless-ty A ⟪ n≤1+n _ , _ ⟫_) (s≤s k≤m) (tail v)) ⟩
      map (timeless-ty A ⟪ k≤m , _ ⟫_) (first-≤ (s≤s k≤m) (map (timeless-ty A ⟪ n≤1+n _ , _ ⟫_) (tail v))) ∎
    where open ≡-Reasoning
  naturality g-tail z≤n       eγ = to-pshfun-eq λ { z≤n _ _ → refl }
  naturality g-tail (s≤s m≤n) eγ = to-pshfun-eq λ { z≤n _ _ → refl ; (s≤s k≤m) _ _ → refl }

  g-cons : Tm Γ (timeless-ty A ⊠ ▻' (GStream A) ⇛ GStream A)
  _$⟨_,_⟩_ (term g-cons n γn) z≤n       _ [ h , _ ] = h ∷ []
  _$⟨_,_⟩_ (term g-cons n γn) (s≤s m≤n) _ [ h , t ] = h ∷ map (ctx-element-subst A (sym (rel-comp Γ z≤n (n≤1+n _) _))) t
  naturality (term g-cons n γn) {ρ-xy = z≤n}     {ρ-yz = z≤n}     _ _ _         = refl
  naturality (term g-cons n γn) {ρ-xy = z≤n}     {ρ-yz = s≤s m≤n} _ _ _         = refl
  naturality (term g-cons n γn) {ρ-xy = s≤s k≤m} {ρ-yz = s≤s m≤n} _ _ [ a , v ] = cong (timeless-ty A ⟪ s≤s k≤m , _ ⟫ a ∷_) (
    begin
      map (ctx-element-subst A _) (map (timeless-ty A ⟪ k≤m , _ ⟫_) (first-≤ (s≤s k≤m) v))
    ≡⟨ map-map-cong (λ _ → morph-cong-2-2 A refl) _ ⟩
      map (timeless-ty A ⟪ s≤s k≤m , _ ⟫_) (map (ctx-element-subst A _) (first-≤ (s≤s k≤m) v))
    ≡⟨ cong (map (timeless-ty A ⟪ s≤s k≤m , _ ⟫_)) (map-first-≤ (ctx-element-subst A _) (s≤s k≤m) v) ⟩
      map (timeless-ty A ⟪ s≤s k≤m , _ ⟫_) (first-≤ (s≤s k≤m) (map (ctx-element-subst A _) v)) ∎)
    where open ≡-Reasoning
  naturality g-cons z≤n       _ = to-pshfun-eq λ { z≤n _ _ → refl }
  naturality g-cons (s≤s m≤n) _ = to-pshfun-eq λ { z≤n _ _ → refl ; (s≤s k≤m) _ _ → refl }

  gstream-natural : (σ : Δ ⇒ Γ) → (GStream A) [ σ ] ≅ᵗʸ GStream (A [ now-subst σ ])
  func (from (gstream-natural σ)) = map (ctx-element-subst A (naturality σ _))
  naturality (from (gstream-natural σ)) v =
    begin
      map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) (map (A ⟪ tt , _ ⟫_) v))
    ≡˘⟨ cong (map (A ⟪ tt , _ ⟫_)) (map-first-≤ _ (s≤s _) v) ⟩
      map (A ⟪ tt , _ ⟫_) (map (A ⟪ tt , _ ⟫) (first-≤ (s≤s _) v))
    ≡⟨ map-map-cong (λ _ → morph-cong-2-2 A refl) (first-≤ (s≤s _) v) ⟩
      map (ctx-element-subst A _) (map (A ⟪ tt , _ ⟫) (first-≤ (s≤s _) v)) ∎
    where open ≡-Reasoning
  func (to (gstream-natural σ)) = map (ctx-element-subst A (sym (naturality σ _)))
  naturality (to (gstream-natural σ)) v =
    begin
      map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) (map (A ⟪ tt , _ ⟫_) v))
    ≡˘⟨ cong (map (A ⟪ tt , _ ⟫_)) (map-first-≤ _ (s≤s _) v) ⟩
      map (A ⟪ tt , _ ⟫_) (map (A ⟪ tt , _ ⟫) (first-≤ (s≤s _) v))
    ≡⟨ map-map-cong (λ _ → morph-cong-2-2 A refl) (first-≤ (s≤s _) v) ⟩
      map (ctx-element-subst A _) (map (A ⟪ tt , _ ⟫) (first-≤ (s≤s _) v)) ∎
    where open ≡-Reasoning
  eq (isoˡ (gstream-natural σ)) = map-inverse (ctx-element-subst-inverseˡ A)
  eq (isoʳ (gstream-natural σ)) = map-inverse (ctx-element-subst-inverseʳ A)

gstream-cong : {A : Ty (now Γ) ℓ} {A' : Ty (now Γ) ℓ'} →
               A ≅ᵗʸ A' → GStream A ≅ᵗʸ GStream A'
func (from (gstream-cong A=A')) = map (func (from A=A'))
naturality (from (gstream-cong {A = A}{A' = A'} A=A')) v =
  begin
    map (A' ⟪ tt , _ ⟫_) (first-≤ (s≤s _) (map (func (from A=A')) v))
  ≡˘⟨ cong (map (A' ⟪ tt , _ ⟫_)) (map-first-≤ _ (s≤s _) v) ⟩
    map (A' ⟪ tt , _ ⟫_) (map (func (from A=A')) (first-≤ (s≤s _) v))
  ≡⟨ map-map-cong (naturality (from A=A')) (first-≤ (s≤s _) v) ⟩
    map (func (from A=A')) (map (A ⟪ tt , _ ⟫) (first-≤ (s≤s _) v)) ∎
  where open ≡-Reasoning
func (to (gstream-cong A=A')) = map (func (to A=A'))
naturality (to (gstream-cong {A = A}{A' = A'} A=A')) v =
  begin
    map (A ⟪ tt , _ ⟫_) (first-≤ (s≤s _) (map (func (to A=A')) v))
  ≡˘⟨ cong (map (A ⟪ tt , _ ⟫_)) (map-first-≤ _ (s≤s _) v) ⟩
    map (A ⟪ tt , _ ⟫_) (map (func (to A=A')) (first-≤ (s≤s _) v))
  ≡⟨ map-map-cong (naturality (to A=A')) (first-≤ (s≤s _) v) ⟩
    map (func (to A=A')) (map (A' ⟪ tt , _ ⟫) (first-≤ (s≤s _) v)) ∎
  where open ≡-Reasoning
eq (isoˡ (gstream-cong A=A')) = map-inverse (eq (isoˡ A=A'))
eq (isoʳ (gstream-cong A=A')) = map-inverse (eq (isoʳ A=A'))


--------------------------------------------------
-- Declaration needed for the naturality solver
-- This shows that it is easy to extend the solver to work with custom types
-- and type operations (even the ones that are only definable in a particular
-- base category).

instance
  gstream-un : IsUnaryNatural GStream
  natural-un {{gstream-un}} σ = gstream-natural σ
  cong-un {{gstream-un}} = gstream-cong


--------------------------------------------------
-- Some operations on guarded streams
--
-- Most functions are an implementation of the examples on pages 8-10 of the paper
--   Ranald Clouston, Aleš Bizjak, Hans Bugge Grathwohl, and Lars Birkedal.
--   The guarded lambda-calculus: Programming and reasoning with guarded recursion for coinductive types.
--   Logical Methods of Computer Science (LMCS), 12(3), 2016.

open import Reflection.Tactic.Naturality

module _ {A : NullaryTypeOp ★ ℓa} {{_ : IsNullaryNatural A}} where
  
  g-snd : Tm Γ (GStream A ⇛ ▻' (timeless-ty A))
  g-snd = lamι (GStream A) (g-head ⟨$⟩' (g-tail $ varι 0))

  g-thrd : Tm Γ (GStream A ⇛ ▻' (▻' (timeless-ty A)))
  g-thrd = lamι (GStream A) (g-snd ⟨$⟩' (g-tail $ varι 0))

g-zeros : Tm Γ (GStream Nat')
g-zeros = löbι (GStream Nat') (g-cons $ pair (timeless-tm zero') (varι 0))

private
  module _ {Γ : Ctx ω ℓ} where
    zeros-test : g-head {Γ = Γ} $ g-zeros ≅ᵗᵐ timeless-tm zero'
    eq zeros-test {x = zero}  _ = refl
    eq zeros-test {x = suc n} _ = refl

    zeros-test2 : g-snd {Γ = Γ} $ g-zeros ≅ᵗᵐ next' (timeless-tm zero')
    eq zeros-test2 {x = zero}        _ = refl
    eq zeros-test2 {x = suc zero}    _ = refl
    eq zeros-test2 {x = suc (suc n)} _ = refl

{-
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
-}
