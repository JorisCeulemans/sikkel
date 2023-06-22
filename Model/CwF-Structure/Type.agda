--------------------------------------------------
-- Types
--------------------------------------------------

open import Model.BaseCategory

module Model.CwF-Structure.Type {C : BaseCategory} where

open import Data.Product renaming (_,_ to [_,_])
open import Function hiding (_⟨_⟩_; _↣_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.Helpers
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.ContextEquivalence

open BaseCategory C

infix 10 _↣_
infix 1 _≅ⁿ_ _≅ᵗʸ_
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
  no-eta-equality

  field
    ty-cell : (x : Ob) (γ : Γ ⟨ x ⟩) → Set
    ty-hom : ∀ {x y} (f : Hom x y) {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} → Γ ⟪ f ⟫ γy ≡ γx → ty-cell y γy → ty-cell x γx
    ty-cong : {f f' : Hom x y} (e-hom : f ≡ f')
              {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} {eγ : Γ ⟪ f ⟫ γy ≡ γx} {eγ' : Γ ⟪ f' ⟫ γy ≡ γx}
              {t : ty-cell y γy} →
              ty-hom f eγ t ≡ ty-hom f' eγ' t
    ty-id : ∀ {x} {γ : Γ ⟨ x ⟩} {t : ty-cell x γ} → ty-hom hom-id (ctx-id Γ) t ≡ t
    ty-comp : ∀ {x y z} {f : Hom x y} {g : Hom y z} {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} →
              {eγ-zy : Γ ⟪ g ⟫ γz ≡ γy} {eγ-yx : Γ ⟪ f ⟫ γy ≡ γx} {t : ty-cell z γz} →
              ty-hom (g ∙ f) (strong-ctx-comp Γ eγ-zy eγ-yx) t ≡ ty-hom f eγ-yx (ty-hom g eγ-zy t)
open Ty public renaming (ty-cell to infix 15 _⟨_,_⟩; ty-hom to infixr 11 _⟪_,_⟫_)

private
  variable
    T S R : Ty Γ
    T1 T2 T3 T4 : Ty Γ

strong-ty-id : (T : Ty Γ) {γ : Γ ⟨ x ⟩} {eγ : Γ ⟪ hom-id ⟫ γ ≡ γ} {t : T ⟨ x , γ ⟩} →
               T ⟪ hom-id , eγ ⟫ t ≡ t
strong-ty-id T = trans (ty-cong T refl) (ty-id T)

strong-ty-comp : (T : Ty Γ) {f : Hom x y} {g : Hom y z} {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩}
                {eγ-zx : Γ ⟪ g ∙ f ⟫ γz ≡ γx} {eγ-zy : Γ ⟪ g ⟫ γz ≡ γy} {eγ-yx : Γ ⟪ f ⟫ γy ≡ γx}
                {t : T ⟨ z , γz ⟩} →
                T ⟪ g ∙ f , eγ-zx ⟫ t ≡ T ⟪ f , eγ-yx ⟫ T ⟪ g , eγ-zy ⟫ t
strong-ty-comp T = trans (ty-cong T refl) (ty-comp T)

ty-cong-2-1 : (T : Ty Γ)
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

ty-cong-2-2 : (T : Ty Γ)
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

ty-ctx-subst : (T : Ty Γ) {γ γ' : Γ ⟨ x ⟩} → γ ≡ γ' → T ⟨ x , γ ⟩ → T ⟨ x , γ' ⟩
ty-ctx-subst {Γ = Γ} T eγ = T ⟪ hom-id , trans (ctx-id Γ) eγ ⟫_

ty-ctx-subst-inverseˡ : (T : Ty Γ) {γ γ' : Γ ⟨ x ⟩} {eγ : γ ≡ γ'} {t : T ⟨ x , γ ⟩} →
                        ty-ctx-subst T (sym eγ) (ty-ctx-subst T eγ t) ≡ t
ty-ctx-subst-inverseˡ T = trans (ty-cong-2-1 T hom-idˡ) (ty-id T)

ty-ctx-subst-inverseʳ : (T : Ty Γ) {γ γ' : Γ ⟨ x ⟩} {eγ : γ ≡ γ'} {t : T ⟨ x , γ' ⟩} →
                        ty-ctx-subst T eγ (ty-ctx-subst T (sym eγ) t) ≡ t
ty-ctx-subst-inverseʳ T = trans (ty-cong-2-1 T hom-idˡ) (ty-id T)

-- The following definition is needed when defining context extension.
to-Σ-ty-eq : ∀ {ℓ} {A : Set ℓ} (T : Ty Γ)
             {a b : A} (e : a ≡ b)
             {γ : A → Γ ⟨ x ⟩}
             {ta : T ⟨ x , γ a ⟩} {tb : T ⟨ x , γ b ⟩} → ty-ctx-subst T (cong γ e) ta ≡ tb →
             [ a , ta ] ≡ [ b , tb ]
to-Σ-ty-eq T {a = a} refl et = cong [ a ,_] (trans (sym (strong-ty-id T)) et)

from-Σ-ty-eq : ∀ {ℓ} {A : Set ℓ} (T : Ty Γ)
               {a b : A} {γ : A → Γ ⟨ x ⟩}
               {ta : T ⟨ x , γ a ⟩} {tb : T ⟨ x , γ b ⟩} →
               [ a , ta ] ≡ [ b , tb ] →
               Σ[ e ∈ a ≡ b ] ty-ctx-subst T (cong γ e) ta ≡ tb
from-Σ-ty-eq T refl = [ refl , strong-ty-id T ]


--------------------------------------------------
-- Natural transformations between types

record _↣_ {Γ : Ctx C} (T : Ty Γ) (S : Ty Γ) : Set where
  no-eta-equality
  field
    func : ∀ {x} {γ} → T ⟨ x , γ ⟩ → S ⟨ x , γ ⟩
    naturality : ∀ {x y} {f : Hom x y} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} {eγ : Γ ⟪ f ⟫ γy ≡ γx} {t : T ⟨ y , γy ⟩} →
                 S ⟪ f , eγ ⟫ (func t) ≡ func (T ⟪ f , eγ ⟫ t)
open _↣_ public

record _≅ⁿ_ {Γ : Ctx C} {T : Ty Γ} {S : Ty Γ} (η φ : T ↣ S) : Set where
  field
    eq : ∀ {x γ} (t : T ⟨ x , γ ⟩) → func η t ≡ func φ t
open _≅ⁿ_ public

reflⁿ : {η : T ↣ S} → η ≅ⁿ η
eq reflⁿ _ = refl

symⁿ : {η φ : T ↣ S} → η ≅ⁿ φ → φ ≅ⁿ η
eq (symⁿ η=φ) t = sym (eq η=φ t)

transⁿ : {η φ µ : T ↣ S} → η ≅ⁿ φ → φ ≅ⁿ µ → η ≅ⁿ µ
eq (transⁿ η=φ φ=µ) t = trans (eq η=φ t) (eq φ=µ t)

module ≅ⁿ-Reasoning where
  infix  3 _∎
  infixr 2 _≅⟨⟩_ step-≅ step-≅˘
  infix  1 begin_

  begin_ : ∀ {η φ : T ↣ S} → η ≅ⁿ φ → η ≅ⁿ φ
  begin_ η=φ = η=φ

  _≅⟨⟩_ : ∀ (η {φ} : T ↣ S) → η ≅ⁿ φ → η ≅ⁿ φ
  _ ≅⟨⟩ η=φ = η=φ

  step-≅ : ∀ (η {φ µ} : T ↣ S) → φ ≅ⁿ µ → η ≅ⁿ φ → η ≅ⁿ µ
  step-≅ _ φ≅µ η≅φ = transⁿ η≅φ φ≅µ

  step-≅˘ : ∀ (η {φ µ} : T ↣ S) → φ ≅ⁿ µ → φ ≅ⁿ η → η ≅ⁿ µ
  step-≅˘ _ φ≅µ φ≅η = transⁿ (symⁿ φ≅η) φ≅µ

  _∎ : ∀ (η : T ↣ S) → η ≅ⁿ η
  _∎ _ = reflⁿ

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

id-trans-unitʳ : (η : T ↣ S) → η ⊙ id-trans T ≅ⁿ η
eq (id-trans-unitʳ η) _ = refl

id-trans-unitˡ : (η : T ↣ S) → id-trans S ⊙ η ≅ⁿ η
eq (id-trans-unitˡ η) _ = refl

⊙-assoc : {T₁ : Ty Γ} {T₂ : Ty Γ} {T₃ : Ty Γ} {T₄ : Ty Γ}
          (η₃₄ : T₃ ↣ T₄) (η₂₃ : T₂ ↣ T₃) (η₁₂ : T₁ ↣ T₂) →
          (η₃₄ ⊙ η₂₃) ⊙ η₁₂ ≅ⁿ η₃₄ ⊙ (η₂₃ ⊙ η₁₂)
eq (⊙-assoc η₃₄ η₂₃ η₁₂) _ = refl

⊙-congʳ : (φ : S ↣ T) {η η' : R ↣ S} → η ≅ⁿ η' → φ ⊙ η ≅ⁿ φ ⊙ η'
eq (⊙-congʳ φ η=η') δ = cong (func φ) (eq η=η' δ)

⊙-congˡ : {φ φ' : S ↣ T} (η : R ↣ S) → φ ≅ⁿ φ' → φ ⊙ η ≅ⁿ φ' ⊙ η
eq (⊙-congˡ η φ=φ') δ = eq φ=φ' (func η δ)


--------------------------------------------------
-- Equivalence of types

-- Two types are said to be equivalent if they are naturally isomorphic as presheaves.
-- This turns out to be easier to work with than standard propositional equality.
record _≅ᵗʸ_ {Γ : Ctx C} (T : Ty Γ) (S : Ty Γ) : Set where
  no-eta-equality

  field
    from : T ↣ S
    to : S ↣ T
    isoˡ : to ⊙ from ≅ⁿ id-trans T
    isoʳ : from ⊙ to ≅ⁿ id-trans S
open _≅ᵗʸ_ public

reflᵗʸ : T ≅ᵗʸ T
from (reflᵗʸ {T = T}) = id-trans T
to (reflᵗʸ {T = T}) = id-trans T
eq (isoˡ reflᵗʸ) _ = refl
eq (isoʳ reflᵗʸ) _ = refl

symᵗʸ : S ≅ᵗʸ T → T ≅ᵗʸ S
from (symᵗʸ S=T) = to S=T
to (symᵗʸ S=T) = from S=T
isoˡ (symᵗʸ S=T) = isoʳ S=T
isoʳ (symᵗʸ S=T) = isoˡ S=T

transᵗʸ : S ≅ᵗʸ T → T ≅ᵗʸ R → S ≅ᵗʸ R
from (transᵗʸ S=T T=R) = from T=R ⊙ from S=T
to (transᵗʸ S=T T=R) = to S=T ⊙ to T=R
isoˡ (transᵗʸ S=T T=R) =
  begin
    (to S=T ⊙ to T=R) ⊙ (from T=R ⊙ from S=T)
  ≅⟨ ⊙-assoc (to S=T) (to T=R) _ ⟩
    to S=T ⊙ (to T=R ⊙ (from T=R ⊙ from S=T))
  ≅˘⟨ ⊙-congʳ (to S=T) (⊙-assoc (to T=R) (from T=R) (from S=T)) ⟩
    to S=T ⊙ ((to T=R ⊙ from T=R) ⊙ from S=T)
  ≅⟨ ⊙-congʳ (to S=T) (⊙-congˡ (from S=T) (isoˡ T=R)) ⟩
    to S=T ⊙ (id-trans _ ⊙ from S=T)
  ≅⟨ ⊙-congʳ (to S=T) (id-trans-unitˡ (from S=T)) ⟩
    to S=T ⊙ from S=T
  ≅⟨ isoˡ S=T ⟩
    id-trans _ ∎
  where open ≅ⁿ-Reasoning
isoʳ (transᵗʸ S=T T=R) =
  begin
    (from T=R ⊙ from S=T) ⊙ (to S=T ⊙ to T=R)
  ≅⟨ ⊙-assoc (from T=R) (from S=T) _ ⟩
    from T=R ⊙ (from S=T ⊙ (to S=T ⊙ to T=R))
  ≅˘⟨ ⊙-congʳ (from T=R) (⊙-assoc (from S=T) (to S=T) (to T=R)) ⟩
    from T=R ⊙ ((from S=T ⊙ to S=T) ⊙ to T=R)
  ≅⟨ ⊙-congʳ (from T=R) (⊙-congˡ (to T=R) (isoʳ S=T)) ⟩
    from T=R ⊙ (id-trans _ ⊙ to T=R)
  ≅⟨ ⊙-congʳ (from T=R) (id-trans-unitˡ (to T=R)) ⟩
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
  step-≅ _ S≅R T≅S = transᵗʸ T≅S S≅R

  step-≅˘ : (T : Ty Γ) → S ≅ᵗʸ R → S ≅ᵗʸ T → T ≅ᵗʸ R
  step-≅˘ _ S≅R S≅T = transᵗʸ (symᵗʸ S≅T) S≅R

  _∎ : (T : Ty Γ) → T ≅ᵗʸ T
  _∎ _ = reflᵗʸ

  syntax step-≅  T S≅R T≅S = T ≅⟨  T≅S ⟩ S≅R
  syntax step-≅˘ T S≅R S≅T = T ≅˘⟨ S≅T ⟩ S≅R


-- Ty Γ is a groupoid and not a setoid (i.e. T ≅ᵗʸ S is not necessarily a proposition).
-- Therefore, we want to express equalities of natural isomorphisms of types.
record _≅ᵉ_ {T S : Ty Γ} (e1 e2 : T ≅ᵗʸ S) : Set where
  no-eta-equality
  field
    from-eq : from e1 ≅ⁿ from e2
open _≅ᵉ_ public

to-eq : {e1 e2 : T ≅ᵗʸ S} → e1 ≅ᵉ e2 → to e1 ≅ⁿ to e2
to-eq {e1 = e1} {e2} ε = begin
    to e1
  ≅˘⟨ id-trans-unitʳ (to e1) ⟩
    to e1 ⊙ id-trans _
  ≅˘⟨ ⊙-congʳ _ (isoʳ e2) ⟩
    to e1 ⊙ (from e2 ⊙ to e2)
  ≅˘⟨ ⊙-assoc _ _ _ ⟩
    (to e1 ⊙ from e2) ⊙ to e2
  ≅⟨ ⊙-congˡ _ (⊙-congʳ _ (symⁿ (from-eq ε))) ⟩
    (to e1 ⊙ from e1) ⊙ to e2
  ≅⟨ ⊙-congˡ _ (isoˡ e1) ⟩
    id-trans _ ⊙ to e2
  ≅⟨ id-trans-unitˡ _ ⟩
    to e2 ∎
  where open ≅ⁿ-Reasoning

reflᵉ : {e : T ≅ᵗʸ S} → e ≅ᵉ e
from-eq reflᵉ = reflⁿ

symᵉ : {e1 e2 : T ≅ᵗʸ S} → e1 ≅ᵉ e2 → e2 ≅ᵉ e1
from-eq (symᵉ ε) = symⁿ (from-eq ε)

transᵉ : {e1 e2 e3 : T ≅ᵗʸ S} → e1 ≅ᵉ e2 → e2 ≅ᵉ e3 → e1 ≅ᵉ e3
from-eq (transᵉ ε ε') = transⁿ (from-eq ε) (from-eq ε')

-- symᵗʸ and transᵗʸ respect equality of natural isomorphisms.
symᵗʸ-cong : {e e' : T ≅ᵗʸ S} → e ≅ᵉ e' → symᵗʸ e ≅ᵉ symᵗʸ e'
from-eq (symᵗʸ-cong 𝑒) = to-eq 𝑒

transᵗʸ-congˡ : {e1 e1' : T ≅ᵗʸ S} {e2 : S ≅ᵗʸ R} → e1 ≅ᵉ e1' → transᵗʸ e1 e2 ≅ᵉ transᵗʸ e1' e2
from-eq (transᵗʸ-congˡ 𝑒) = ⊙-congʳ _ (from-eq 𝑒)

transᵗʸ-congʳ : {e1 : T ≅ᵗʸ S} {e2 e2' : S ≅ᵗʸ R} → e2 ≅ᵉ e2' → transᵗʸ e1 e2 ≅ᵉ transᵗʸ e1 e2'
from-eq (transᵗʸ-congʳ 𝑒) = ⊙-congˡ _ (from-eq 𝑒)

-- Groupoid laws for the groupoid Ty Γ and some consequences
transᵗʸ-assoc : {e : T1 ≅ᵗʸ T2} {e' : T2 ≅ᵗʸ T3} {e'' : T3 ≅ᵗʸ T4} →
                transᵗʸ (transᵗʸ e e') e'' ≅ᵉ transᵗʸ e (transᵗʸ e' e'')
from-eq transᵗʸ-assoc = symⁿ (⊙-assoc _ _ _)

reflᵗʸ-unitˡ : {e : T ≅ᵗʸ S} → transᵗʸ reflᵗʸ e ≅ᵉ e
from-eq reflᵗʸ-unitˡ = id-trans-unitʳ _

reflᵗʸ-unitʳ : {e : T ≅ᵗʸ S} → transᵗʸ e reflᵗʸ ≅ᵉ e
from-eq reflᵗʸ-unitʳ = id-trans-unitˡ _

symᵗʸ-invˡ : {e : T ≅ᵗʸ S} → transᵗʸ (symᵗʸ e) e ≅ᵉ reflᵗʸ
from-eq (symᵗʸ-invˡ {e = e}) = isoʳ e

symᵗʸ-invʳ : {e : T ≅ᵗʸ S} → transᵗʸ e (symᵗʸ e) ≅ᵉ reflᵗʸ
from-eq (symᵗʸ-invʳ {e = e}) = isoˡ e

symᵗʸ-transᵗʸ : {e : T ≅ᵗʸ S} {e' : S ≅ᵗʸ R} → symᵗʸ (transᵗʸ e e') ≅ᵉ transᵗʸ (symᵗʸ e') (symᵗʸ e)
from-eq symᵗʸ-transᵗʸ = reflⁿ

to-symᵗʸ-eq : {e : T ≅ᵗʸ S} {e' : S ≅ᵗʸ T} → transᵗʸ e e' ≅ᵉ reflᵗʸ → e ≅ᵉ symᵗʸ e'
to-symᵗʸ-eq 𝑒 = transᵉ (symᵉ reflᵗʸ-unitʳ) (transᵉ (transᵗʸ-congʳ (symᵉ symᵗʸ-invʳ)) (transᵉ (symᵉ transᵗʸ-assoc) (transᵉ (transᵗʸ-congˡ 𝑒) reflᵗʸ-unitˡ)))

transᵗʸ-cancelʳ : {e : T ≅ᵗʸ S} {e' : R ≅ᵗʸ S} → transᵗʸ e (transᵗʸ (symᵗʸ e') e') ≅ᵉ e
transᵗʸ-cancelʳ = transᵉ (transᵗʸ-congʳ symᵗʸ-invˡ) reflᵗʸ-unitʳ

transᵗʸ-cancelˡ : {e : T ≅ᵗʸ S} {e' : S ≅ᵗʸ R} → transᵗʸ (transᵗʸ (symᵗʸ e) e) e' ≅ᵉ e'
transᵗʸ-cancelˡ = transᵉ (transᵗʸ-congˡ symᵗʸ-invˡ) reflᵗʸ-unitˡ


--------------------------------------------------
-- Substitution of types

_[_] : Ty Γ → Δ ⇒ Γ → Ty Δ
T [ σ ] ⟨ x , δ ⟩ = T ⟨ x , func σ δ ⟩
_⟪_,_⟫_ (_[_] {Γ = Γ} T σ) f {δy}{δx} eγ-yx t = T ⟪ f , proof ⟫ t
  where
    proof : Γ ⟪ f ⟫ func σ δy ≡ func σ δx
    proof = trans (naturality σ) (cong (func σ) eγ-yx)
ty-cong (T [ σ ]) f = ty-cong T f
ty-id (T [ σ ]) = strong-ty-id T
ty-comp (T [ σ ]) = strong-ty-comp T

ty-subst-id : (T : Ty Γ) → T [ id-subst Γ ] ≅ᵗʸ T
func (from (ty-subst-id T)) = id
naturality (from (ty-subst-id T)) = ty-cong T refl
func (to (ty-subst-id T)) = id
naturality (to (ty-subst-id T)) = ty-cong T refl
eq (isoˡ (ty-subst-id T)) _ = refl
eq (isoʳ (ty-subst-id T)) _ = refl

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
func (from (ty-subst-cong-subst σ=τ T)) {_}{δ} t = ty-ctx-subst T (eq σ=τ δ) t
naturality (from (ty-subst-cong-subst σ=τ T)) = ty-cong-2-2 T (trans hom-idˡ (sym hom-idʳ))
func (to (ty-subst-cong-subst σ=τ T)) {_}{δ} t = ty-ctx-subst T (sym (eq σ=τ δ)) t
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

-- Substitution by σ : Γ ⇒ Δ constitutes a groupoid morphism from Ty Δ to Ty Γ.
ty-subst-cong-ty-cong : {T S : Ty Δ} {e e' : T ≅ᵗʸ S} → e ≅ᵉ e' → (σ : Γ ⇒ Δ) →
                        ty-subst-cong-ty σ e ≅ᵉ ty-subst-cong-ty σ e'
from-eq (ty-subst-cong-ty-cong 𝑒 σ) = ty-subst-map-cong (from-eq 𝑒)

ty-subst-cong-ty-refl : {σ : Γ ⇒ Δ} {T : Ty Δ} → ty-subst-cong-ty σ (reflᵗʸ {T = T}) ≅ᵉ reflᵗʸ
from-eq ty-subst-cong-ty-refl = ty-subst-map-id _

ty-subst-cong-ty-sym : {σ : Γ ⇒ Δ} {e : T ≅ᵗʸ S} → ty-subst-cong-ty σ (symᵗʸ e) ≅ᵉ symᵗʸ (ty-subst-cong-ty σ e)
from-eq ty-subst-cong-ty-sym = reflⁿ

ty-subst-cong-ty-trans : {σ : Γ ⇒ Δ} {e : T1 ≅ᵗʸ T2} {e' : T2 ≅ᵗʸ T3} →
                         ty-subst-cong-ty σ (transᵗʸ e e') ≅ᵉ transᵗʸ (ty-subst-cong-ty σ e) (ty-subst-cong-ty σ e')
from-eq ty-subst-cong-ty-trans = ty-subst-map-comp _ _ _

ty-subst-cong-natural : {σ τ : Γ ⇒ Δ} (ε : σ ≅ˢ τ) (e : T ≅ᵗʸ S) →
                        transᵗʸ (ty-subst-cong-subst ε T) (ty-subst-cong-ty τ e) ≅ᵉ transᵗʸ (ty-subst-cong-ty σ e) (ty-subst-cong-subst ε S)
eq (from-eq (ty-subst-cong-natural ε e)) _ = sym (naturality (from e))

ty-subst-cong-subst-refl : {σ : Γ ⇒ Δ} → ty-subst-cong-subst (reflˢ {σ = σ}) T ≅ᵉ reflᵗʸ
eq (from-eq (ty-subst-cong-subst-refl {T = T})) _ = strong-ty-id T

ty-subst-cong-subst-sym : {σ τ : Γ ⇒ Δ} {ε : σ ≅ˢ τ} → ty-subst-cong-subst (symˢ ε) T ≅ᵉ symᵗʸ (ty-subst-cong-subst ε T)
eq (from-eq ty-subst-cong-subst-sym) _ = refl

ty-subst-cong-subst-trans : {σ1 σ2 σ3 : Γ ⇒ Δ} {ε : σ1 ≅ˢ σ2} {ε' : σ2 ≅ˢ σ3} →
                            ty-subst-cong-subst (transˢ ε ε') T ≅ᵉ transᵗʸ (ty-subst-cong-subst ε T) (ty-subst-cong-subst ε' T)
eq (from-eq (ty-subst-cong-subst-trans {T = T})) _ = sym (ty-cong-2-1 T hom-idʳ)

ty-subst-cong-subst-2-1 : {σ1 : Γ ⇒ Δ} {σ2 : Δ ⇒ Θ} {τ : Γ ⇒ Θ}
                          (T : Ty Θ) → σ2 ⊚ σ1 ≅ˢ τ →
                          T [ σ2 ] [ σ1 ] ≅ᵗʸ T [ τ ]
ty-subst-cong-subst-2-1 T ε = transᵗʸ (ty-subst-comp T _ _) (ty-subst-cong-subst ε T)

ty-subst-cong-subst-2-2 : {Δ' : Ctx C} {σ1 : Γ ⇒ Δ} {σ2 : Δ ⇒ Θ} {τ1 : Γ ⇒ Δ'} {τ2 : Δ' ⇒ Θ}
                          (T : Ty Θ) → σ2 ⊚ σ1 ≅ˢ τ2 ⊚ τ1 →
                          T [ σ2 ] [ σ1 ] ≅ᵗʸ T [ τ2 ] [ τ1 ]
ty-subst-cong-subst-2-2 T ε =
  transᵗʸ (ty-subst-comp T _ _) (transᵗʸ (ty-subst-cong-subst ε T) (symᵗʸ (ty-subst-comp T _ _)))

-- Nicer syntax for substitutions coming from context equality
ιc[_]_ : Γ ≅ᶜ Δ → Ty Δ → Ty Γ
ιc[ Γ=Δ ] T = T [ from Γ=Δ ]

ιc⁻¹[_]_ : Γ ≅ᶜ Δ → Ty Γ → Ty Δ
ιc⁻¹[ Γ=Δ ] T = T [ to Γ=Δ ]
