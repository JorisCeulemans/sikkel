{-# OPTIONS --irrelevant-projections #-}

--------------------------------------------------
-- Types
--------------------------------------------------

open import Categories

module CwF-Structure.Types {C : Category} where

open import Function hiding (_⟨_⟩_; _↣_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality) renaming (subst to transport)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.ContextEquivalence

open Category C

infix 10 _↣_
infix 1 _≅ⁿ_ -- _≅ᵗʸ_
infixl 20 _⊙_

private
  variable
    x y z w : Ob
    Δ Γ Θ : Ctx C


--------------------------------------------------
-- Definition of types in a context

-- A type in context Γ is defined as a presheaf over the category of elements of Γ.
-- A morphism in the category of elements of Γ from (x, γx) to (y, γy) consists of
--   a morphism f : Hom x y together with a proof that Γ ⟪ f ⟫ γy ≡ γx. This explains
--   the type of the field morph (representing the action of the presheaf on morphisms).

record Ty (Γ : Ctx C) : Set₁ where
  constructor MkTy
  -- no-eta-equality

  field
    type : (x : Ob) (γ : Γ ⟨ x ⟩) → Set
    morph : ∀ {x y} (f : Hom x y) {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} → .(Γ ⟪ f ⟫ γy ≡ γx) → type y γy → type x γx
    .ty-cong : {f f' : Hom x y} (e-hom : f ≡ f')
               {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} {eγ : Γ ⟪ f ⟫ γy ≡ γx} {eγ' : Γ ⟪ f' ⟫ γy ≡ γx}
               {t : type y γy} →
               morph f eγ t ≡ morph f' eγ' t
    .ty-id : ∀ {x} {γ : Γ ⟨ x ⟩} {t : type x γ} → morph hom-id (ctx-id Γ) t ≡ t
    .ty-comp : ∀ {x y z} {f : Hom x y} {g : Hom y z} {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} →
               {eγ-zy : Γ ⟪ g ⟫ γz ≡ γy} {eγ-yx : Γ ⟪ f ⟫ γy ≡ γx} {t : type z γz} →
               morph (g ∙ f) (strong-ctx-comp Γ eγ-zy eγ-yx) t ≡ morph f eγ-yx (morph g eγ-zy t)
open Ty public renaming (type to infix 15 _⟨_,_⟩; morph to infixr 11 _⟪_,_⟫_)

private
  variable
    T S R : Ty Γ

.strong-ty-id : (T : Ty Γ) {γ : Γ ⟨ x ⟩} {eγ : Γ ⟪ hom-id ⟫ γ ≡ γ} {t : T ⟨ x , γ ⟩} →
                T ⟪ hom-id , eγ ⟫ t ≡ t
strong-ty-id T = trans (ty-cong T refl) (ty-id T)

.strong-ty-comp : (T : Ty Γ) {f : Hom x y} {g : Hom y z} {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
                  {eγ-zx : Γ ⟪ g ∙ f ⟫ γz ≡ γx} {eγ-zy : Γ ⟪ g ⟫ γz ≡ γy} {eγ-yx : Γ ⟪ f ⟫ γy ≡ γx}
                  {t : T ⟨ z , γz ⟩} →
                  T ⟪ g ∙ f , eγ-zx ⟫ t ≡ T ⟪ f , eγ-yx ⟫ T ⟪ g , eγ-zy ⟫ t
strong-ty-comp T = trans (ty-cong T refl) (ty-comp T)

.ty-cong-2-1 : (T : Ty Γ)
               {f : Hom x y} {g : Hom y z} {h : Hom x z} (e-hom : g ∙ f ≡ h)
               {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
               {ef : Γ ⟪ f ⟫ γy ≡ γx} {eg : Γ ⟪ g ⟫ γz ≡ γy} {eh : Γ ⟪ h ⟫ γz ≡ γx}
               {t : T ⟨ z , γz ⟩} →
               T ⟪ f , ef ⟫ (T ⟪ g , eg ⟫ t) ≡ T ⟪ h , eh ⟫ t
ty-cong-2-1 T {f}{g}{h} e-hom {t = t} =
  begin
    T ⟪ f , _ ⟫ T ⟪ g , _ ⟫ t
  ≡˘⟨ ty-comp T ⟩
    T ⟪ g ∙ f , _ ⟫ t
  ≡⟨ ty-cong T e-hom ⟩
    T ⟪ h , _ ⟫ t ∎
  where open ≡-Reasoning

.ty-cong-2-2 : (T : Ty Γ)
               {f : Hom x y} {f' : Hom x z} {g : Hom y w} {g' : Hom z w} (e-hom : g ∙ f ≡ g' ∙ f')
               {γw : Γ ⟨ w ⟩} {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
               {ef : Γ ⟪ f ⟫ γy ≡ γx} {ef' : Γ ⟪ f' ⟫ γz ≡ γx}
               {eg : Γ ⟪ g ⟫ γw ≡ γy} {eg' : Γ ⟪ g' ⟫ γw ≡ γz}
               {t : T ⟨ w , γw ⟩} →
               T ⟪ f , ef ⟫ (T ⟪ g , eg ⟫ t) ≡ T ⟪ f' , ef' ⟫ (T ⟪ g' , eg' ⟫ t)
ty-cong-2-2 T {f}{f'}{g}{g'} e-hom {t = t} =
  begin
    T ⟪ f , _ ⟫ T ⟪ g , _ ⟫ t
  ≡˘⟨ ty-comp T ⟩
    T ⟪ g ∙ f , _ ⟫ t
  ≡⟨ ty-cong T e-hom ⟩
    T ⟪ g' ∙ f' , _ ⟫ t
  ≡⟨ ty-comp T ⟩
    T ⟪ f' , _ ⟫ T ⟪ g' , _ ⟫ t ∎
  where open ≡-Reasoning

ctx-element-subst : (T : Ty Γ) {γ γ' : Γ ⟨ x ⟩} → γ ≡ γ' → T ⟨ x , γ ⟩ → T ⟨ x , γ' ⟩
ctx-element-subst {Γ = Γ} T eγ = T ⟪ hom-id , trans (ctx-id Γ) eγ ⟫_

.ctx-element-subst-inverseˡ : (T : Ty Γ) {γ γ' : Γ ⟨ x ⟩} {eγ : γ ≡ γ'} {t : T ⟨ x , γ ⟩} →
                              ctx-element-subst T (sym eγ) (ctx-element-subst T eγ t) ≡ t
ctx-element-subst-inverseˡ T = trans (ty-cong-2-1 T hom-idˡ) (ty-id T)

.ctx-element-subst-inverseʳ : (T : Ty Γ) {γ γ' : Γ ⟨ x ⟩} {eγ : γ ≡ γ'} {t : T ⟨ x , γ' ⟩} →
                              ctx-element-subst T eγ (ctx-element-subst T (sym eγ) t) ≡ t
ctx-element-subst-inverseʳ T = trans (ty-cong-2-1 T hom-idˡ) (ty-id T)

-- The following definitions are needed when defining context extension.
morph-transport : (T : Ty Γ) {f : Hom x y}
                  {γ1 : Γ ⟨ y ⟩} {γ2 γ3 : Γ ⟨ x ⟩}
                  {eγ12 : Γ ⟪ f ⟫ γ1 ≡ γ2} {eγ23 : γ2 ≡ γ3}
                  {t : T ⟨ y , γ1 ⟩} →
                  transport (λ - → T ⟨ x , - ⟩) eγ23 (T ⟪ f , eγ12 ⟫ t) ≡ T ⟪ f , trans eγ12 eγ23 ⟫ t
morph-transport T {eγ12 = refl} {eγ23 = refl} = refl

module _ {Γ : Ctx C} (T : Ty Γ) where
  strict-morph : (f : Hom x y) (γ : Γ ⟨ y ⟩) → T ⟨ y , γ ⟩ → T ⟨ x , Γ ⟪ f ⟫ γ ⟩
  strict-morph f γ t = T ⟪ f , refl ⟫ t

  .strict-morph-id : {γ : Γ ⟨ y ⟩} {t : T ⟨ y , γ ⟩} →
                     transport (λ - → T ⟨ y , - ⟩) (ctx-id Γ) (strict-morph hom-id γ t) ≡ t
  strict-morph-id {y = y}{γ = γ}{t = t} =
    begin
      transport (λ - → T ⟨ y , - ⟩) (ctx-id Γ) (strict-morph hom-id γ t)
    ≡⟨ morph-transport T ⟩
      T ⟪ hom-id , ctx-id Γ ⟫ t
    ≡⟨ ty-id T ⟩
      t ∎
    where open ≡-Reasoning

  .strict-morph-comp : {f : Hom x y} {g : Hom y z} {γ : Γ ⟨ z ⟩} {t : T ⟨ z , γ ⟩} →
                       transport (λ - → T ⟨ x , - ⟩) (ctx-comp Γ) (strict-morph (g ∙ f) γ t) ≡
                         strict-morph f (Γ ⟪ g ⟫ γ) (strict-morph g γ t)
  strict-morph-comp {x = x} {f = f} {g = g} {γ = γ} {t = t} =
    begin
      transport (λ - → T ⟨ x , - ⟩) (ctx-comp Γ) (strict-morph (g ∙ f) γ t)
    ≡⟨ morph-transport T ⟩
      T ⟪ g ∙ f , ctx-comp Γ ⟫ t
    ≡⟨ strong-ty-comp T ⟩
      strict-morph f (Γ ⟪ g ⟫ γ) (strict-morph g γ t) ∎
    where open ≡-Reasoning


--------------------------------------------------
-- Natural transformations between types

record _↣_ {Γ : Ctx C} (T : Ty Γ) (S : Ty Γ) : Set where
  no-eta-equality
  field
    func : ∀ {x} {γ} → T ⟨ x , γ ⟩ → S ⟨ x , γ ⟩
    .naturality : ∀ {x y} {f : Hom x y} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} {eγ : Γ ⟪ f ⟫ γy ≡ γx} {t : T ⟨ y , γy ⟩} →
                  S ⟪ f , eγ ⟫ (func t) ≡ func (T ⟪ f , eγ ⟫ t)
open _↣_ public

record _≅ⁿ_ {Γ : Ctx C} {T : Ty Γ} {S : Ty Γ} (η φ : T ↣ S) : Set where
  field
    eq : ∀ {x γ} (t : T ⟨ x , γ ⟩) → func η t ≡ func φ t
open _≅ⁿ_ public

≅ⁿ-refl : {η : T ↣ S} → η ≅ⁿ η
eq ≅ⁿ-refl _ = refl

≅ⁿ-sym : {η φ : T ↣ S} → η ≅ⁿ φ → φ ≅ⁿ η
eq (≅ⁿ-sym η=φ) t = sym (eq η=φ t)

≅ⁿ-trans : {η φ µ : T ↣ S} → η ≅ⁿ φ → φ ≅ⁿ µ → η ≅ⁿ µ
eq (≅ⁿ-trans η=φ φ=µ) t = trans (eq η=φ t) (eq φ=µ t)

module ≅ⁿ-Reasoning where
  infix  3 _∎
  infixr 2 _≅⟨⟩_ step-≅ step-≅˘
  infix  1 begin_

  begin_ : ∀ {η φ : T ↣ S} → η ≅ⁿ φ → η ≅ⁿ φ
  begin_ η=φ = η=φ

  _≅⟨⟩_ : ∀ (η {φ} : T ↣ S) → η ≅ⁿ φ → η ≅ⁿ φ
  _ ≅⟨⟩ η=φ = η=φ

  step-≅ : ∀ (η {φ µ} : T ↣ S) → φ ≅ⁿ µ → η ≅ⁿ φ → η ≅ⁿ µ
  step-≅ _ φ≅µ η≅φ = ≅ⁿ-trans η≅φ φ≅µ

  step-≅˘ : ∀ (η {φ µ} : T ↣ S) → φ ≅ⁿ µ → φ ≅ⁿ η → η ≅ⁿ µ
  step-≅˘ _ φ≅µ φ≅η = ≅ⁿ-trans (≅ⁿ-sym φ≅η) φ≅µ

  _∎ : ∀ (η : T ↣ S) → η ≅ⁿ η
  _∎ _ = ≅ⁿ-refl

  syntax step-≅  η φ≅µ η≅φ = η ≅⟨  η≅φ ⟩ φ≅µ
  syntax step-≅˘ η φ≅µ φ≅η = η ≅˘⟨ φ≅η ⟩ φ≅µ

id-trans : (T : Ty Γ) → T ↣ T
func (id-trans T) = id
naturality (id-trans T) = refl

_⊙_ : S ↣ T → R ↣ S → R ↣ T
func (φ ⊙ η) = func φ ∘ func η
naturality (_⊙_ {S = S}{T = T}{R = R} φ η) {f = f}{eγ = eγ} {t = r} =
  begin
    T ⟪ f , eγ ⟫ func φ (func η r)
  ≡⟨ naturality φ ⟩
    func φ (S ⟪ f , eγ ⟫ func η r)
  ≡⟨ cong (func φ) (naturality η) ⟩
    func φ (func η (R ⟪ f , eγ ⟫ r)) ∎
  where open ≡-Reasoning

⊙-id-transʳ : (η : T ↣ S) → η ⊙ id-trans T ≅ⁿ η
eq (⊙-id-transʳ η) _ = refl

⊙-id-transˡ : (η : T ↣ S) → id-trans S ⊙ η ≅ⁿ η
eq (⊙-id-transˡ η) _ = refl

⊙-assoc : {T₁ : Ty Γ} {T₂ : Ty Γ} {T₃ : Ty Γ} {T₄ : Ty Γ}
           (η₃₄ : T₃ ↣ T₄) (η₂₃ : T₂ ↣ T₃) (η₁₂ : T₁ ↣ T₂) →
           (η₃₄ ⊙ η₂₃) ⊙ η₁₂ ≅ⁿ η₃₄ ⊙ (η₂₃ ⊙ η₁₂)
eq (⊙-assoc η₃₄ η₂₃ η₁₂) _ = refl

⊙-congˡ : (φ : S ↣ T) {η η' : R ↣ S} → η ≅ⁿ η' → φ ⊙ η ≅ⁿ φ ⊙ η'
eq (⊙-congˡ φ η=η') δ = cong (func φ) (eq η=η' δ)

⊙-congʳ : {φ φ' : S ↣ T} (η : R ↣ S) → φ ≅ⁿ φ' → φ ⊙ η ≅ⁿ φ' ⊙ η
eq (⊙-congʳ η φ=φ') δ = eq φ=φ' (func η δ)


--------------------------------------------------
-- Equivalence of types
{-
-- Two types are said to be equivalent if they are naturally isomorphic as presheaves.
-- This turns out to be easier to work with than standard propositional equality.
record _≅ᵗʸ_ {Γ : Ctx C} (T : Ty Γ) (S : Ty Γ) : Set where
  field
    from : T ↣ S
    to : S ↣ T
    isoˡ : to ⊙ from ≅ⁿ id-trans T
    isoʳ : from ⊙ to ≅ⁿ id-trans S
open _≅ᵗʸ_ public

≅ᵗʸ-refl : T ≅ᵗʸ T
from (≅ᵗʸ-refl {T = T}) = id-trans T
to (≅ᵗʸ-refl {T = T}) = id-trans T
eq (isoˡ ≅ᵗʸ-refl) _ = refl
eq (isoʳ ≅ᵗʸ-refl) _ = refl

≅ᵗʸ-sym : S ≅ᵗʸ T → T ≅ᵗʸ S
from (≅ᵗʸ-sym S=T) = to S=T
to (≅ᵗʸ-sym S=T) = from S=T
isoˡ (≅ᵗʸ-sym S=T) = isoʳ S=T
isoʳ (≅ᵗʸ-sym S=T) = isoˡ S=T

≅ᵗʸ-trans : S ≅ᵗʸ T → T ≅ᵗʸ R → S ≅ᵗʸ R
from (≅ᵗʸ-trans S=T T=R) = from T=R ⊙ from S=T
to (≅ᵗʸ-trans S=T T=R) = to S=T ⊙ to T=R
isoˡ (≅ᵗʸ-trans S=T T=R) =
  begin
    (to S=T ⊙ to T=R) ⊙ (from T=R ⊙ from S=T)
  ≅⟨ ⊙-assoc (to S=T) (to T=R) _ ⟩
    to S=T ⊙ (to T=R ⊙ (from T=R ⊙ from S=T))
  ≅˘⟨ ⊙-congˡ (to S=T) (⊙-assoc (to T=R) (from T=R) (from S=T)) ⟩
    to S=T ⊙ ((to T=R ⊙ from T=R) ⊙ from S=T)
  ≅⟨ ⊙-congˡ (to S=T) (⊙-congʳ (from S=T) (isoˡ T=R)) ⟩
    to S=T ⊙ (id-trans _ ⊙ from S=T)
  ≅⟨ ⊙-congˡ (to S=T) (⊙-id-transˡ (from S=T)) ⟩
    to S=T ⊙ from S=T
  ≅⟨ isoˡ S=T ⟩
    id-trans _ ∎
  where open ≅ⁿ-Reasoning
isoʳ (≅ᵗʸ-trans S=T T=R) =
  begin
    (from T=R ⊙ from S=T) ⊙ (to S=T ⊙ to T=R)
  ≅⟨ ⊙-assoc (from T=R) (from S=T) _ ⟩
    from T=R ⊙ (from S=T ⊙ (to S=T ⊙ to T=R))
  ≅˘⟨ ⊙-congˡ (from T=R) (⊙-assoc (from S=T) (to S=T) (to T=R)) ⟩
    from T=R ⊙ ((from S=T ⊙ to S=T) ⊙ to T=R)
  ≅⟨ ⊙-congˡ (from T=R) (⊙-congʳ (to T=R) (isoʳ S=T)) ⟩
    from T=R ⊙ (id-trans _ ⊙ to T=R)
  ≅⟨ ⊙-congˡ (from T=R) (⊙-id-transˡ (to T=R)) ⟩
    from T=R ⊙ to T=R
  ≅⟨ isoʳ T=R ⟩
    id-trans _ ∎
  where open ≅ⁿ-Reasoning

module ≅ᵗʸ-Reasoning where
  infix  3 _∎
  infixr 2 _≅⟨⟩_ step-≅ step-≅˘
  infix  1 begin_

  begin_ : T ≅ᵗʸ S → T ≅ᵗʸ S
  begin_ T=S = T=S

  _≅⟨⟩_ : (T : Ty Γ) → T ≅ᵗʸ S → T ≅ᵗʸ S
  _ ≅⟨⟩ T=S = T=S

  step-≅ : (T : Ty Γ) → S ≅ᵗʸ R → T ≅ᵗʸ S → T ≅ᵗʸ R
  step-≅ _ S≅R T≅S = ≅ᵗʸ-trans T≅S S≅R

  step-≅˘ : (T : Ty Γ) → S ≅ᵗʸ R → S ≅ᵗʸ T → T ≅ᵗʸ R
  step-≅˘ _ S≅R S≅T = ≅ᵗʸ-trans (≅ᵗʸ-sym S≅T) S≅R

  _∎ : (T : Ty Γ) → T ≅ᵗʸ T
  _∎ _ = ≅ᵗʸ-refl

  syntax step-≅  T S≅R T≅S = T ≅⟨  T≅S ⟩ S≅R
  syntax step-≅˘ T S≅R S≅T = T ≅˘⟨ S≅T ⟩ S≅R
-}

--------------------------------------------------
-- Substitution of types

_[_] : Ty Γ → Δ ⇒ Γ → Ty Δ
T [ σ ] ⟨ x , δ ⟩ = T ⟨ x , func σ δ ⟩
_⟪_,_⟫_ (_[_] {Γ = Γ} T σ) f {δy}{δx} eγ-yx t = T ⟪ f , proof ⟫ t
  where
    .proof : Γ ⟪ f ⟫ func σ δy ≡ func σ δx
    proof = trans (naturality σ) (cong (func σ) eγ-yx)
ty-cong (T [ σ ]) f = ty-cong T f
ty-id (T [ σ ]) = strong-ty-id T
ty-comp (T [ σ ]) = strong-ty-comp T

ty-subst-id : (T : Ty Γ) → T [ id-subst Γ ] ≡ T
ty-subst-id T = refl

{-
ty-subst-id : (T : Ty Γ) → T [ id-subst Γ ] ≅ᵗʸ T
func (from (ty-subst-id T)) = id
naturality (from (ty-subst-id T)) = ty-cong T refl
func (to (ty-subst-id T)) = id
naturality (to (ty-subst-id T)) = ty-cong T refl
eq (isoˡ (ty-subst-id T)) _ = refl
eq (isoʳ (ty-subst-id T)) _ = refl
-}

ty-subst-comp : (T : Ty Θ) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → T [ τ ] [ σ ] ≡ T [ τ ⊚ σ ]
ty-subst-comp T τ σ = refl

{-
ty-subst-comp : (T : Ty Θ) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → T [ τ ] [ σ ] ≅ᵗʸ T [ τ ⊚ σ ]
func (from (ty-subst-comp T τ σ)) = id
naturality (from (ty-subst-comp T τ σ)) = ty-cong T refl
func (to (ty-subst-comp T τ σ)) = id
naturality (to (ty-subst-comp T τ σ)) = ty-cong T refl
eq (isoˡ (ty-subst-comp T τ σ)) _ = refl
eq (isoʳ (ty-subst-comp T τ σ)) _ = refl

ty-subst-map : (σ : Δ ⇒ Γ) → (T ↣ S) → T [ σ ] ↣ S [ σ ]
func (ty-subst-map σ η) t = func η t
naturality (ty-subst-map σ η) = naturality η

ty-subst-map-cong : {σ : Δ ⇒ Γ} {η φ : T ↣ S} →
                    η ≅ⁿ φ → ty-subst-map σ η ≅ⁿ ty-subst-map σ φ
eq (ty-subst-map-cong e) t = eq e t

ty-subst-map-id : (σ : Δ ⇒ Γ) → ty-subst-map σ (id-trans T) ≅ⁿ id-trans (T [ σ ])
eq (ty-subst-map-id σ) t = refl

ty-subst-map-comp : (σ : Δ ⇒ Γ) (φ : S ↣ T) (η : R ↣ S) →
                    ty-subst-map σ (φ ⊙ η) ≅ⁿ ty-subst-map σ φ ⊙ ty-subst-map σ η
eq (ty-subst-map-comp σ φ η) t = refl

ty-subst-cong-ty : (σ : Δ ⇒ Γ) → T ≅ᵗʸ S → T [ σ ] ≅ᵗʸ S [ σ ]
from (ty-subst-cong-ty σ T=S) = ty-subst-map σ (from T=S)
to (ty-subst-cong-ty σ T=S) = ty-subst-map σ (to T=S)
eq (isoˡ (ty-subst-cong-ty σ T=S)) t = eq (isoˡ T=S) t
eq (isoʳ (ty-subst-cong-ty σ T=S)) t = eq (isoʳ T=S) t

ty-subst-cong-subst : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → (T : Ty Γ) → T [ σ ] ≅ᵗʸ T [ τ ]
func (from (ty-subst-cong-subst σ=τ T)) {_}{δ} t = ctx-element-subst T (eq σ=τ δ) t
naturality (from (ty-subst-cong-subst σ=τ T)) = ty-cong-2-2 T (trans hom-idˡ (sym hom-idʳ))
func (to (ty-subst-cong-subst σ=τ T)) {_}{δ} t = ctx-element-subst T (sym (eq σ=τ δ)) t
naturality (to (ty-subst-cong-subst σ=τ T)) = ty-cong-2-2 T (trans hom-idˡ (sym hom-idʳ))
eq (isoˡ (ty-subst-cong-subst {Γ = Γ} σ=τ T)) t =
  -- Here we cannot use ty-id T twice because the omitted equality proofs are not ctx-id Γ _
  -- (i.e. T ⟪_⟫ t is not applied to the identity morphism in the category of elements of Γ).
  begin
    T ⟪ hom-id , _ ⟫ T ⟪ hom-id , _ ⟫ t
  ≡⟨ ty-cong-2-1 T hom-idˡ ⟩
    T ⟪ hom-id , ctx-id Γ ⟫ t
  ≡⟨ ty-id T ⟩
    t ∎
  where open ≡-Reasoning
eq (isoʳ (ty-subst-cong-subst σ=τ T)) t =
  begin
    T ⟪ hom-id , _ ⟫ T ⟪ hom-id , _ ⟫ t
  ≡⟨ ty-cong-2-1 T hom-idˡ ⟩
    T ⟪ hom-id , _ ⟫ t
  ≡⟨ ty-id T ⟩
    t ∎
  where open ≡-Reasoning
-}
-- Nicer syntax for substitutions coming from context equality
ιc[_]_ : Γ ≅ᶜ Δ → Ty Δ → Ty Γ
ιc[ Γ=Δ ] T = T [ from Γ=Δ ]

ιc⁻¹[_]_ : Γ ≅ᶜ Δ → Ty Γ → Ty Δ
ιc⁻¹[ Γ=Δ ] T = T [ to Γ=Δ ]

