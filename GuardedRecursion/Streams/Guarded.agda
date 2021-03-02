--------------------------------------------------
-- Definition and examples of guarded streams mode ω
--------------------------------------------------

module GuardedRecursion.Streams.Guarded where

open import Data.Bool using (if_then_else_; true; false)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (proj₁; proj₂) renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
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
open import Types.Instances
open import Modalities
open import GuardedRecursion.Modalities
open import Reflection.Naturality.TypeOperations
open import Reflection.Tactic.Lambda
open import Reflection.Tactic.LobInduction

private
  variable
    ℓ ℓ' : Level
    Γ Δ : Ctx ω


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

GStream : Ty (now Γ) → Ty Γ
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

module _ {A : Ty (now Γ)} where
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

  prim-g-cons : Tm (Γ ,, timeless-ty A ,, (▻' (GStream A)) [ π ]) (((GStream A) [ π ]) [ π ])
  term prim-g-cons zero    [ [ γn , a ] , t ] = a ∷ []
  term prim-g-cons (suc n) [ [ γn , a ] , t ] = a ∷ map (ctx-element-subst A (sym (rel-comp Γ z≤n (n≤1+n n) _))) t
  naturality prim-g-cons {y = zero}  z≤n       refl = refl
  naturality prim-g-cons {y = suc n} z≤n       refl = refl
  naturality prim-g-cons             (s≤s m≤n) refl = cong (timeless-ty A ⟪ s≤s m≤n , refl ⟫ _ ∷_) (sym (
    begin
      map (ctx-element-subst A _) (map (timeless-ty A ⟪ m≤n , _ ⟫_) (first-≤ (s≤s m≤n) _))
    ≡⟨ map-map-cong (λ _ → morph-cong-2-2 A refl) _ ⟩
      map (timeless-ty A ⟪ s≤s m≤n , refl ⟫_) (map (ctx-element-subst A _) (first-≤ (s≤s m≤n) _))
    ≡⟨ cong (map (timeless-ty A ⟪ s≤s m≤n , refl ⟫_)) (map-first-≤ (ctx-element-subst A _) (s≤s m≤n) _) ⟩
      map (timeless-ty A ⟪ s≤s m≤n , refl ⟫_) (first-≤ (s≤s m≤n) (map (ctx-element-subst A _) _)) ∎))
    where open ≡-Reasoning

  g-cons : Tm Γ (timeless-ty A ⇛ ▻' (GStream A) ⇛ GStream A)
  g-cons = lam (timeless-ty A) (ι[ ⇛-natural π ]
               lam (▻' (GStream A) [ π ])
                   prim-g-cons)

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

gstream-cong : {A : Ty (now Γ)} {A' : Ty (now Γ)} →
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
-- Example from the introduction and section 3.1 of the ICFP submission

g-map : {A B : ClosedType ★} → {{IsClosedNatural A}} → {{IsClosedNatural B}} →
        Tm Γ (timeless-ty (A ⇛ B) ⇛ GStream A ⇛ GStream B)
g-map {A = A}{B} =
  lamι[ "f" ∈ timeless-ty (A ⇛ B) ]
    löbι[ "m" ∈▻' (GStream A ⇛ GStream B) ]
      lamι[ "s" ∈ GStream A ]
        g-cons $ varι "f" ⊛⟨ timeless ⟩ (g-head $ varι "s")
               $ varι "m" ⊛' (g-tail $ varι "s")

g-nats : Tm Γ (GStream Nat')
g-nats = löbι[ "s" ∈▻' GStream Nat' ] g-cons $ timeless-tm zero'
                                             $ (g-map $ timeless-tm suc') ⟨$⟩' varι "s"


--------------------------------------------------
-- Examples of functions on guarded streams implemented in Sikkel


-- The follwing definitions are an implementation of all examples involving streams on pages 8-10 of the paper
--   Ranald Clouston, Aleš Bizjak, Hans Bugge Grathwohl, and Lars Birkedal.
--   The Guarded Lambda-Calculus: Programming and Reasoning with Guarded Recursion for Coinductive Types.
--   Logical Methods of Computer Science (LMCS), 12(3), 2016.
--   https://doi.org/10.2168/LMCS-12(3:7)2016

module _ {A : ClosedType ★} {{_ : IsClosedNatural A}} where
  
  g-snd : Tm Γ (GStream A ⇛ ▻' (timeless-ty A))
  g-snd = lamι[ "s" ∈ GStream A ] g-head ⟨$⟩' (g-tail $ varι "s")

  g-thrd : Tm Γ (GStream A ⇛ ▻' (▻' (timeless-ty A)))
  g-thrd = lamι[ "s" ∈ GStream A ] g-snd ⟨$⟩' (g-tail $ varι "s")

g-zeros : Tm Γ (GStream Nat')
g-zeros = löbι[ "s" ∈▻' GStream Nat' ] g-cons $ timeless-tm zero' $ varι "s"

private
  module _ {Γ : Ctx ω} where
    zeros-test : g-head {Γ = Γ} $ g-zeros ≅ᵗᵐ timeless-tm zero'
    eq zeros-test {x = zero}  _ = refl
    eq zeros-test {x = suc n} _ = refl

    zeros-test2 : g-snd {Γ = Γ} $ g-zeros ≅ᵗᵐ next' (timeless-tm zero')
    eq zeros-test2 {x = zero}        _ = refl
    eq zeros-test2 {x = suc zero}    _ = refl
    eq zeros-test2 {x = suc (suc n)} _ = refl

g-iterate' : {A : ClosedType ★} {{_ : IsClosedNatural A}} →
            Tm Γ (timeless-ty (A ⇛ A) ⇛ timeless-ty A ⇛ GStream A)
g-iterate' {A = A} =
  lamι[ "f" ∈ timeless-ty (A ⇛ A) ]
    löbι[ "g" ∈▻' (timeless-ty A ⇛ GStream A) ]
      lamι[ "x" ∈ timeless-ty A ]
        g-cons $ varι "x"
               $ varι "g" ⊛' next' (varι "f" ⊛⟨ timeless ⟩ varι "x")

-- This is a more general definition of iterate since the generating function of type
-- timeless-ty (A ⇛ A) appears under ▻'. The implementation itself applies g-map to
-- its corecursive call (represented by the variable "s"), which would not be allowed
-- in a definition of standard Agda streams by copattern matching.
g-iterate : {A : ClosedType ★} {{_ : IsClosedNatural A}} →
             Tm Γ (▻' (timeless-ty (A ⇛ A)) ⇛ timeless-ty A ⇛ GStream A)
g-iterate {A = A} =
  lamι[ "f" ∈ ▻' (timeless-ty (A ⇛ A)) ]
    lamι[ "a" ∈ timeless-ty A ]
      löbι[ "s" ∈▻' GStream A ]
        g-cons $ varι "a"
               $ g-map ⟨$⟩' varι "f" ⊛' varι "s"

-- Alternative definition of g-nats making use of g-iterate.
g-nats' : Tm Γ (GStream Nat')
g-nats' = g-iterate $ next' (timeless-tm suc') $ timeless-tm zero'

g-interleave : {A : ClosedType ★} {{_ : IsClosedNatural A}} →
               Tm Γ (GStream A ⇛ ▻' (GStream A) ⇛ GStream A)
g-interleave {A = A} =
  löbι[ "g" ∈▻' (GStream A ⇛ ▻' (GStream A) ⇛ GStream A) ]
    lamι[ "s" ∈ GStream A ]
      lamι[ "t" ∈ ▻' (GStream A) ]
        g-cons $ (g-head $ varι "s")
               $ varι "g" ⊛' varι "t" ⊛' next' (g-tail $ varι "s")

g-toggle : Tm Γ (GStream Nat')
g-toggle = löbι[ "s" ∈▻' GStream Nat' ]
             g-cons $ timeless-tm one'
                    $ next' (g-cons $ timeless-tm zero' $ varι "s")

g-paperfolds : Tm Γ (GStream Nat')
g-paperfolds = löbι[ "s" ∈▻' GStream Nat' ] g-interleave $ g-toggle $ varι "s"

module _
  (A : ClosedType ★) {{_ : IsClosedNatural A}}
  (T : ClosedType ω) {{_ : IsClosedNatural T}}
  where
  g-initial : Tm Γ (((timeless-ty A ⊠ ▻' T) ⇛ T) ⇛ GStream A ⇛ T)
  g-initial =
    löbι[ "g" ∈▻' (((timeless-ty A ⊠ ▻' T) ⇛ T) ⇛ GStream A ⇛ T) ]
      lamι[ "f" ∈ (timeless-ty A ⊠ ▻' T) ⇛ T ]
        lamι[ "s" ∈ GStream A ]
          varι "f" $ pair (g-head $ varι "s")
                          (varι "g" ⊛' next' (varι "f") ⊛' (g-tail $ varι "s"))

  g-final : Tm Γ ((T ⇛ (timeless-ty A ⊠ ▻' T)) ⇛ T ⇛ GStream A)
  g-final =
    löbι[ "g" ∈▻' ((T ⇛ (timeless-ty A ⊠ ▻' T)) ⇛ T ⇛ GStream A) ]
      lamι[ "f" ∈ T ⇛ (timeless-ty A ⊠ ▻' T) ]
        lamι[ "x" ∈ T ]
          g-cons $ fst (varι "f" $ varι "x")
                 $ varι "g" ⊛' next' (varι "f") ⊛' snd (varι "f" $ varι "x")


-- In the next two definitions of guarded streams, we will need a modal version of
-- the eliminator for booleans. This version works with the timeless modality, but in
-- principle it could be implemented for any modality from that departs from ★.
modal-if'_then'_else'_ : {T : Ty Γ} → Tm (now Γ) Bool' → Tm Γ T → Tm Γ T → Tm Γ T
term (modal-if' c then' t else' f) n γ = if timeless-tm c ⟨ n , γ ⟩' then t ⟨ n , γ ⟩' else f ⟨ n , γ ⟩'
naturality (modal-if'_then'_else'_ c t f) {m} {n} m≤n {γ} {γ'} eγ with timeless-tm c ⟨ m , γ' ⟩' | timeless-tm c ⟨ n , γ ⟩' | naturality (timeless-tm c) m≤n eγ
naturality (modal-if'_then'_else'_ c t f) {m} {n} m≤n {γ} {γ'} eγ | false | .false | refl = naturality f m≤n eγ
naturality (modal-if'_then'_else'_ c t f) {m} {n} m≤n {γ} {γ'} eγ | true  | .true  | refl = naturality t m≤n eγ

-- The follwing two definitions are an implementation of the examples on page 12 of the
-- paper by Clouston et al. cited above.
thue-morse : Tm Γ (GStream Bool')
thue-morse = löbι[ "t-m" ∈▻' GStream Bool' ]
  g-cons $ timeless-tm false' $ (
  g-cons $ timeless-tm true') ⟨$⟩' (
  lift▻' (lift▻' h) $ (g-tail ⟨$⟩' (lift▻' h $ varι "t-m")))
  where
    h : Tm Δ (GStream Bool' ⇛ GStream Bool')
    h = löbι[ "g" ∈▻' GStream Bool' ⇛ GStream Bool' ]
          lamι[ "s" ∈ GStream Bool' ] (
            modal-if' untimeless-tm (g-head $ varι "s")
            then' (g-cons $ timeless-tm true'  $ next' (g-cons $ timeless-tm false' $ varι "g" ⊛' (g-tail $ varι "s")))
            else' (g-cons $ timeless-tm false' $ next' (g-cons $ timeless-tm true'  $ varι "g" ⊛' (g-tail $ varι "s"))))

fibonacci-word : Tm Γ (GStream Bool')
fibonacci-word = löbι[ "fw" ∈▻' GStream Bool' ]
  g-cons $ timeless-tm false' $ (
  g-cons $ timeless-tm true') ⟨$⟩' (
  lift▻' (lift▻' f) $ (g-tail ⟨$⟩' (lift▻' f $ varι "fw")))
  where
    f : Tm Δ (GStream Bool' ⇛ GStream Bool')
    f = löbι[ "g" ∈▻' GStream Bool' ⇛ GStream Bool' ]
          lamι[ "s" ∈ GStream Bool' ] (
            modal-if' untimeless-tm (g-head $ varι "s")
            then' (g-cons $ timeless-tm false' $ varι "g" ⊛' (g-tail $ varι "s"))
            else' (g-cons $ timeless-tm false' $ next' (g-cons $ timeless-tm true'  $ varι "g" ⊛' (g-tail $ varι "s"))))


-- This is an implementation of an example from the end of section 1.1 of the paper
--   Robert Atkey, and Conor McBride.
--   Productive Coprogramming with Guarded Recursion.
--   ICFP 2013.
--   https://doi.org/10.1145/2544174.2500597
g-mergef : {A B C : ClosedType ★} → {{IsClosedNatural A}} → {{IsClosedNatural B}} → {{IsClosedNatural C}} →
           Tm Γ (timeless-ty A ⇛ timeless-ty B ⇛ ▻' (GStream C) ⇛ GStream C) →
           Tm Γ (GStream A ⇛ GStream B ⇛ GStream C)
g-mergef {A = A}{B}{C} f =
  löbι[ "g" ∈▻' (GStream A ⇛ GStream B ⇛ GStream C) ]
    lamι[ "xs" ∈ GStream A ]
      lamι[ "ys" ∈ GStream B ]
        (↑ι⟨ 3 ⟩ f) $ (g-head $ varι "xs")
                    $ (g-head $ varι "ys")
                    $ (varι "g" ⊛' (g-tail $ varι "xs") ⊛' (g-tail $ varι "ys"))


-- The remaining examples were not taken from a paper.
g-zipWith : {A B C : ClosedType ★} → {{IsClosedNatural A}} → {{IsClosedNatural B}} → {{IsClosedNatural C}} →
            Tm Γ (timeless-ty (A ⇛ B ⇛ C)) → Tm Γ (GStream A ⇛ GStream B ⇛ GStream C)
g-zipWith {A = A}{B}{C} f =
  löbι[ "g" ∈▻' (GStream A ⇛ GStream B ⇛ GStream C) ]
    lamι[ "as" ∈ GStream A ]
      lamι[ "bs" ∈ GStream B ]
        g-cons $ ↑ι⟨ 3 ⟩ f ⊛⟨ timeless ⟩ (g-head $ varι "as") ⊛⟨ timeless ⟩ (g-head $ varι "bs")
               $ varι "g" ⊛' (g-tail $ varι "as") ⊛' (g-tail $ varι "bs")

prim-nat-sum : {Γ : Ctx ★} → Tm Γ Nat' → Tm Γ Nat' → Tm Γ Nat'
term (prim-nat-sum t s) n γ = t ⟨ n , γ ⟩' + s ⟨ n , γ ⟩'
naturality (prim-nat-sum t s) m≤n eγ = cong₂ _+_ (naturality t m≤n eγ) (naturality s m≤n eγ)

nat-sum : {Γ : Ctx ★} → Tm Γ (Nat' ⇛ Nat' ⇛ Nat')
nat-sum = lamι[ "m" ∈ Nat' ] lamι[ "n" ∈ Nat' ] prim-nat-sum (varι "m") (varι "n")

-- The stream of fibonacci numbers.
g-fibs : Tm Γ (GStream Nat')
g-fibs = löbι[ "s" ∈▻' GStream Nat' ]
  g-cons $ timeless-tm one' $ (
  (g-cons $ timeless-tm one') ⟨$⟩'
  ((lift2▻' (g-zipWith (timeless-tm nat-sum)) $ varι "s") ⟨$⟩' (g-tail ⟨$⟩' varι "s")))

-- g-flipFst flips the first two elements of a guarded stream.
g-flipFst : {A : ClosedType ★} → {{IsClosedNatural A}} →
            Tm Γ (GStream A ⇛ ▻' (GStream A))
g-flipFst {A = A}= lamι[ "s" ∈ GStream A ]
                     g-cons ⟨$⟩' (g-snd $ varι "s") ⊛' next' (
                     g-cons ⟨$⟩' next' (g-head $ varι "s") ⊛' (g-tail ⟨$⟩' (g-tail $ varι "s")))
