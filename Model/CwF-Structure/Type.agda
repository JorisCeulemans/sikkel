--------------------------------------------------
-- Types
--------------------------------------------------

open import Model.BaseCategory

module Model.CwF-Structure.Type {C : BaseCategory} where

open import Data.Product renaming (_,_ to [_,_])
open import Function hiding (_⟨_⟩_; _↣_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open import Relation.Binary.Reasoning.Syntax
open import Preliminaries

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
  ≡⟨ ty-comp T ⟨
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
  ≡⟨ ty-comp T ⟨
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

ty-ctx-subst-iso : (T : Ty Γ) {γ γ' : Γ ⟨ x ⟩} (eγ : γ ≡ γ') → (T ⟨ x , γ ⟩ ↔ T ⟨ x , γ' ⟩)
ty-ctx-subst-iso T eγ = mk↔ₛ′
  (ty-ctx-subst T eγ)
  (ty-ctx-subst T (sym eγ))
  (λ _ → ty-ctx-subst-inverseʳ T)
  (λ _ → ty-ctx-subst-inverseˡ T)

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

module ≅ⁿ-Reasoning {Γ}{T S : Ty Γ} where
  open begin-syntax {A = T ↣ S} _≅ⁿ_ id public
  open ≅-syntax {A = T ↣ S} _≅ⁿ_ _≅ⁿ_ transⁿ symⁿ public
  open end-syntax {A = T ↣ S} _≅ⁿ_ reflⁿ public

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

id-trans-unitʳ : {η : T ↣ S} → η ⊙ id-trans T ≅ⁿ η
eq id-trans-unitʳ _ = refl

id-trans-unitˡ : {η : T ↣ S} → id-trans S ⊙ η ≅ⁿ η
eq id-trans-unitˡ _ = refl

⊙-assoc : {T₁ : Ty Γ} {T₂ : Ty Γ} {T₃ : Ty Γ} {T₄ : Ty Γ}
          {η₃₄ : T₃ ↣ T₄} {η₂₃ : T₂ ↣ T₃} {η₁₂ : T₁ ↣ T₂} →
          (η₃₄ ⊙ η₂₃) ⊙ η₁₂ ≅ⁿ η₃₄ ⊙ (η₂₃ ⊙ η₁₂)
eq ⊙-assoc _ = refl

⊙-congʳ : {φ : S ↣ T} {η η' : R ↣ S} → η ≅ⁿ η' → φ ⊙ η ≅ⁿ φ ⊙ η'
eq (⊙-congʳ {φ = φ} η=η') δ = cong (func φ) (eq η=η' δ)

⊙-congˡ : {φ φ' : S ↣ T} {η : R ↣ S} → φ ≅ⁿ φ' → φ ⊙ η ≅ⁿ φ' ⊙ η
eq (⊙-congˡ {η = η} φ=φ') δ = eq φ=φ' (func η δ)


--------------------------------------------------
-- Equivalence of types

-- Two types are said to be equivalent if they are naturally isomorphic as presheaves.
-- This turns out to be easier to work with than standard propositional equality.
-- Note: T ≅ᵗʸ could live in Set rather than Set₁, but this definition makes it easier
--   to write types of functions that take a Ty Γ and produce an equivalence.
record _≅ᵗʸ_ {Γ : Ctx C} (T : Ty Γ) (S : Ty Γ) : Set₁ where
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
  ≅⟨ ⊙-assoc ⟩
    to S=T ⊙ (to T=R ⊙ (from T=R ⊙ from S=T))
  ≅⟨ ⊙-congʳ ⊙-assoc ⟨
    to S=T ⊙ ((to T=R ⊙ from T=R) ⊙ from S=T)
  ≅⟨ ⊙-congʳ (⊙-congˡ (isoˡ T=R)) ⟩
    to S=T ⊙ (id-trans _ ⊙ from S=T)
  ≅⟨ ⊙-congʳ id-trans-unitˡ ⟩
    to S=T ⊙ from S=T
  ≅⟨ isoˡ S=T ⟩
    id-trans _ ∎
  where open ≅ⁿ-Reasoning
isoʳ (transᵗʸ S=T T=R) =
  begin
    (from T=R ⊙ from S=T) ⊙ (to S=T ⊙ to T=R)
  ≅⟨ ⊙-assoc ⟩
    from T=R ⊙ (from S=T ⊙ (to S=T ⊙ to T=R))
  ≅⟨ ⊙-congʳ ⊙-assoc ⟨
    from T=R ⊙ ((from S=T ⊙ to S=T) ⊙ to T=R)
  ≅⟨ ⊙-congʳ (⊙-congˡ (isoʳ S=T)) ⟩
    from T=R ⊙ (id-trans _ ⊙ to T=R)
  ≅⟨ ⊙-congʳ id-trans-unitˡ ⟩
    from T=R ⊙ to T=R
  ≅⟨ isoʳ T=R ⟩
    id-trans _ ∎
  where open ≅ⁿ-Reasoning

-- There is no module ≅ᵗʸ-Reasoning because Ty Γ with _≅ᵗʸ_ is a
-- groupoid and not a setoid. Hence we do not want to add reflᵗʸ to
-- the end of every proof of type equivalence.


-- Ty Γ is a groupoid and not a setoid (i.e. T ≅ᵗʸ S is not necessarily a proposition).
-- Therefore, we want to express equalities of natural isomorphisms of types.
record _≅ᵉ_ {T S : Ty Γ} (e1 e2 : T ≅ᵗʸ S) : Set where
  no-eta-equality
  field
    from-eq : from e1 ≅ⁿ from e2
open _≅ᵉ_ public

to-eq : {e1 e2 : T ≅ᵗʸ S} → e1 ≅ᵉ e2 → to e1 ≅ⁿ to e2
to-eq {e1 = e1} {e2} 𝑒 = begin
    to e1
  ≅⟨ id-trans-unitʳ ⟨
    to e1 ⊙ id-trans _
  ≅⟨ ⊙-congʳ (isoʳ e2) ⟨
    to e1 ⊙ (from e2 ⊙ to e2)
  ≅⟨ ⊙-assoc ⟨
    (to e1 ⊙ from e2) ⊙ to e2
  ≅⟨ ⊙-congˡ (⊙-congʳ (symⁿ (from-eq 𝑒))) ⟩
    (to e1 ⊙ from e1) ⊙ to e2
  ≅⟨ ⊙-congˡ (isoˡ e1) ⟩
    id-trans _ ⊙ to e2
  ≅⟨ id-trans-unitˡ ⟩
    to e2 ∎
  where open ≅ⁿ-Reasoning

reflᵉ : {e : T ≅ᵗʸ S} → e ≅ᵉ e
from-eq reflᵉ = reflⁿ

symᵉ : {e1 e2 : T ≅ᵗʸ S} → e1 ≅ᵉ e2 → e2 ≅ᵉ e1
from-eq (symᵉ 𝑒) = symⁿ (from-eq 𝑒)

transᵉ : {e1 e2 e3 : T ≅ᵗʸ S} → e1 ≅ᵉ e2 → e2 ≅ᵉ e3 → e1 ≅ᵉ e3
from-eq (transᵉ 𝑒 𝑒') = transⁿ (from-eq 𝑒) (from-eq 𝑒')

module ≅ᵉ-Reasoning {Γ}{T S : Ty Γ} where
  open begin-syntax {A = T ≅ᵗʸ S} _≅ᵉ_ id public
  open ≅-syntax {A = T ≅ᵗʸ S} _≅ᵉ_ _≅ᵉ_ transᵉ symᵉ public
  open end-syntax {A = T ≅ᵗʸ S} _≅ᵉ_ reflᵉ public


-- symᵗʸ and transᵗʸ respect equality of natural isomorphisms.
symᵗʸ-cong : {e e' : T ≅ᵗʸ S} → e ≅ᵉ e' → symᵗʸ e ≅ᵉ symᵗʸ e'
from-eq (symᵗʸ-cong 𝑒) = to-eq 𝑒

transᵗʸ-congˡ : {e1 e1' : T ≅ᵗʸ S} {e2 : S ≅ᵗʸ R} → e1 ≅ᵉ e1' → transᵗʸ e1 e2 ≅ᵉ transᵗʸ e1' e2
from-eq (transᵗʸ-congˡ 𝑒) = ⊙-congʳ (from-eq 𝑒)

transᵗʸ-congʳ : {e1 : T ≅ᵗʸ S} {e2 e2' : S ≅ᵗʸ R} → e2 ≅ᵉ e2' → transᵗʸ e1 e2 ≅ᵉ transᵗʸ e1 e2'
from-eq (transᵗʸ-congʳ 𝑒) = ⊙-congˡ (from-eq 𝑒)

-- Groupoid laws for the groupoid Ty Γ and some consequences
transᵗʸ-assoc : {e : T1 ≅ᵗʸ T2} {e' : T2 ≅ᵗʸ T3} {e'' : T3 ≅ᵗʸ T4} →
                transᵗʸ (transᵗʸ e e') e'' ≅ᵉ transᵗʸ e (transᵗʸ e' e'')
from-eq transᵗʸ-assoc = symⁿ ⊙-assoc

reflᵗʸ-unitˡ : {e : T ≅ᵗʸ S} → transᵗʸ reflᵗʸ e ≅ᵉ e
from-eq reflᵗʸ-unitˡ = id-trans-unitʳ

reflᵗʸ-unitʳ : {e : T ≅ᵗʸ S} → transᵗʸ e reflᵗʸ ≅ᵉ e
from-eq reflᵗʸ-unitʳ = id-trans-unitˡ

symᵗʸ-invˡ : {e : T ≅ᵗʸ S} → transᵗʸ (symᵗʸ e) e ≅ᵉ reflᵗʸ
from-eq (symᵗʸ-invˡ {e = e}) = isoʳ e

symᵗʸ-invʳ : {e : T ≅ᵗʸ S} → transᵗʸ e (symᵗʸ e) ≅ᵉ reflᵗʸ
from-eq (symᵗʸ-invʳ {e = e}) = isoˡ e

symᵗʸ-reflᵗʸ : symᵗʸ (reflᵗʸ {T = T}) ≅ᵉ reflᵗʸ
from-eq symᵗʸ-reflᵗʸ = reflⁿ

symᵗʸ-transᵗʸ : {e : T ≅ᵗʸ S} {e' : S ≅ᵗʸ R} → symᵗʸ (transᵗʸ e e') ≅ᵉ transᵗʸ (symᵗʸ e') (symᵗʸ e)
from-eq symᵗʸ-transᵗʸ = reflⁿ

symᵗʸ-involutive : {e : T ≅ᵗʸ S} → symᵗʸ (symᵗʸ e) ≅ᵉ e
from-eq symᵗʸ-involutive = reflⁿ

to-symᵗʸ-eq : {e : T ≅ᵗʸ S} {e' : S ≅ᵗʸ T} → transᵗʸ e e' ≅ᵉ reflᵗʸ → e ≅ᵉ symᵗʸ e'
to-symᵗʸ-eq 𝑒 = transᵉ (symᵉ reflᵗʸ-unitʳ) (transᵉ (transᵗʸ-congʳ (symᵉ symᵗʸ-invʳ)) (transᵉ (symᵉ transᵗʸ-assoc) (transᵉ (transᵗʸ-congˡ 𝑒) reflᵗʸ-unitˡ)))

transᵗʸ-cancelʳ-symˡ : {e : T ≅ᵗʸ S} {e' : R ≅ᵗʸ S} → transᵗʸ e (transᵗʸ (symᵗʸ e') e') ≅ᵉ e
transᵗʸ-cancelʳ-symˡ = transᵉ (transᵗʸ-congʳ symᵗʸ-invˡ) reflᵗʸ-unitʳ

transᵗʸ-cancelˡ-symˡ : {e : T ≅ᵗʸ S} {e' : S ≅ᵗʸ R} → transᵗʸ (transᵗʸ (symᵗʸ e) e) e' ≅ᵉ e'
transᵗʸ-cancelˡ-symˡ = transᵉ (transᵗʸ-congˡ symᵗʸ-invˡ) reflᵗʸ-unitˡ

transᵗʸ-cancelʳ-symʳ : {e : T ≅ᵗʸ S} {e' : S ≅ᵗʸ R} → transᵗʸ e (transᵗʸ e' (symᵗʸ e')) ≅ᵉ e
transᵗʸ-cancelʳ-symʳ = transᵉ (transᵗʸ-congʳ symᵗʸ-invʳ) reflᵗʸ-unitʳ

transᵗʸ-cancelˡ-symʳ : {e : T ≅ᵗʸ S} {e' : T ≅ᵗʸ R} → transᵗʸ (transᵗʸ e (symᵗʸ e)) e' ≅ᵉ e'
transᵗʸ-cancelˡ-symʳ = transᵉ (transᵗʸ-congˡ symᵗʸ-invʳ) reflᵗʸ-unitˡ

to-symᵗʸ-eqʳ : {e : T ≅ᵗʸ S} {e' : R ≅ᵗʸ S} {e'' : T ≅ᵗʸ R} → e ≅ᵉ transᵗʸ e'' e' → transᵗʸ e (symᵗʸ e') ≅ᵉ e''
to-symᵗʸ-eqʳ 𝑒 = transᵉ (transᵗʸ-congˡ 𝑒) (transᵉ transᵗʸ-assoc transᵗʸ-cancelʳ-symʳ)

to-symᵗʸ-eqˡ : {e : T ≅ᵗʸ S} {e' : T ≅ᵗʸ R} {e'' : S ≅ᵗʸ R} → e' ≅ᵉ transᵗʸ e e'' → transᵗʸ (symᵗʸ e) e' ≅ᵉ e''
to-symᵗʸ-eqˡ 𝑒 = transᵉ (transᵗʸ-congʳ 𝑒) (transᵉ (symᵉ transᵗʸ-assoc) transᵗʸ-cancelˡ-symˡ)

move-symᵗʸ-out : {T S S' R : Ty Γ} {e1 : S ≅ᵗʸ T} {e2 : S ≅ᵗʸ R} {e1' : T ≅ᵗʸ S'} {e2' : R ≅ᵗʸ S'} →
                 transᵗʸ e2 e2' ≅ᵉ transᵗʸ e1 e1' →
                 transᵗʸ (symᵗʸ e1) e2 ≅ᵉ transᵗʸ e1' (symᵗʸ e2')
move-symᵗʸ-out 𝑒 = to-symᵗʸ-eqˡ (symᵉ (transᵉ (symᵉ transᵗʸ-assoc) (to-symᵗʸ-eqʳ (symᵉ 𝑒))))

move-symᵗʸ-in : {T S S' R : Ty Γ} {e1 : T ≅ᵗʸ S} {e2 : R ≅ᵗʸ S} {e1' : S' ≅ᵗʸ T} {e2' : S' ≅ᵗʸ R} →
                transᵗʸ e1' e1 ≅ᵉ transᵗʸ e2' e2 →
                transᵗʸ e1 (symᵗʸ e2) ≅ᵉ transᵗʸ (symᵗʸ e1') e2'
move-symᵗʸ-in 𝑒 = to-symᵗʸ-eqʳ (symᵉ (transᵉ transᵗʸ-assoc (to-symᵗʸ-eqˡ (symᵉ 𝑒))))

exchange-to-from-out : {T T' S R : Ty Γ} (e : T ≅ᵗʸ S) (e' : R ≅ᵗʸ T') {φ : T ↣ R} {φ' : S ↣ T'} →
                       φ ⊙ to e ≅ⁿ to e' ⊙ φ' →
                       from e' ⊙ φ ≅ⁿ φ' ⊙ from e
exchange-to-from-out e e' 𝔢 =
  transⁿ (⊙-congʳ (transⁿ (symⁿ id-trans-unitʳ) (⊙-congʳ (symⁿ (isoˡ e))))) (
    transⁿ (⊙-congʳ (symⁿ ⊙-assoc)) (
  transⁿ (⊙-congʳ (⊙-congˡ 𝔢)) (
    transⁿ (transⁿ (⊙-congʳ ⊙-assoc) (symⁿ ⊙-assoc))
  (transⁿ (⊙-congˡ (isoʳ e')) id-trans-unitˡ))))

exchange-to-from-in : {T T' S R : Ty Γ} (e : R ≅ᵗʸ T) (e' : T' ≅ᵗʸ S) {φ : S ↣ T} {φ' : T' ↣ R} →
                      to e ⊙ φ ≅ⁿ φ' ⊙ to e' →
                      φ ⊙ from e' ≅ⁿ from e ⊙ φ'
exchange-to-from-in e e' 𝔢 =
  transⁿ (⊙-congˡ (transⁿ (symⁿ id-trans-unitˡ) (⊙-congˡ (symⁿ (isoʳ e))))) (
    transⁿ (⊙-congˡ ⊙-assoc) (
  transⁿ (⊙-congˡ (⊙-congʳ 𝔢)) (
    transⁿ (transⁿ (⊙-congˡ (symⁿ ⊙-assoc)) ⊙-assoc)
  (transⁿ (⊙-congʳ (isoˡ e')) id-trans-unitʳ))))

exchange-from-to-out : {T T' S R : Ty Γ} (e : S ≅ᵗʸ T) (e' : T' ≅ᵗʸ R) {φ : T ↣ R} {φ' : S ↣ T'} →
                       φ ⊙ from e ≅ⁿ from e' ⊙ φ' →
                       to e' ⊙ φ ≅ⁿ φ' ⊙ to e
exchange-from-to-out e e' 𝔢 = exchange-to-from-out (symᵗʸ e) (symᵗʸ e') 𝔢

exchange-from-to-in : {T T' S R : Ty Γ} (e : T ≅ᵗʸ R) (e' : S ≅ᵗʸ T') {φ : S ↣ T} {φ' : T' ↣ R} →
                      from e ⊙ φ ≅ⁿ φ' ⊙ from e' →
                      φ ⊙ to e' ≅ⁿ to e ⊙ φ'
exchange-from-to-in e e' 𝔢 = exchange-to-from-in (symᵗʸ e) (symᵗʸ e') 𝔢


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

ty-subst-id-from : (T : Ty Γ) → T [ id-subst Γ ] ↣ T
func (ty-subst-id-from T) = id
naturality (ty-subst-id-from T) = ty-cong T refl

ty-subst-id-to : (T : Ty Γ) → T ↣ T [ id-subst Γ ]
func (ty-subst-id-to T) = id
naturality (ty-subst-id-to T) = ty-cong T refl

ty-subst-id-to-from : (T : Ty Γ) → ty-subst-id-to T ⊙ ty-subst-id-from T ≅ⁿ id-trans _
eq (ty-subst-id-to-from T) _ = refl

ty-subst-id-from-to : (T : Ty Γ) → ty-subst-id-from T ⊙ ty-subst-id-to T ≅ⁿ id-trans T
eq (ty-subst-id-from-to T) _ = refl

ty-subst-id : (T : Ty Γ) → T [ id-subst Γ ] ≅ᵗʸ T
from (ty-subst-id T) = ty-subst-id-from T
to (ty-subst-id T) = ty-subst-id-to T
isoˡ (ty-subst-id T) = ty-subst-id-to-from T
isoʳ (ty-subst-id T) = ty-subst-id-from-to T

ty-subst-comp-from : (T : Ty Θ) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → T [ τ ] [ σ ] ↣ T [ τ ⊚ σ ]
func (ty-subst-comp-from T τ σ) = id
naturality (ty-subst-comp-from T τ σ) = ty-cong T refl

ty-subst-comp-to : (T : Ty Θ) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → T [ τ ⊚ σ ] ↣ T [ τ ] [ σ ]
func (ty-subst-comp-to T τ σ) = id
naturality (ty-subst-comp-to T τ σ) = ty-cong T refl

ty-subst-comp : (T : Ty Θ) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → T [ τ ] [ σ ] ≅ᵗʸ T [ τ ⊚ σ ]
from (ty-subst-comp T τ σ) = ty-subst-comp-from T τ σ
to (ty-subst-comp T τ σ) = ty-subst-comp-to T τ σ
eq (isoˡ (ty-subst-comp T τ σ)) _ = refl
eq (isoʳ (ty-subst-comp T τ σ)) _ = refl

ty-subst-map : (σ : Δ ⇒ Γ) → (T ↣ S) → T [ σ ] ↣ S [ σ ]
func (ty-subst-map σ η) t = func η t
naturality (ty-subst-map σ η) = naturality η

ty-subst-map-cong : {σ : Δ ⇒ Γ} {η φ : T ↣ S} →
                    η ≅ⁿ φ → ty-subst-map σ η ≅ⁿ ty-subst-map σ φ
eq (ty-subst-map-cong e) t = eq e t

ty-subst-map-id : {σ : Δ ⇒ Γ} → ty-subst-map σ (id-trans T) ≅ⁿ id-trans (T [ σ ])
eq ty-subst-map-id t = refl

ty-subst-map-⊙ : {σ : Δ ⇒ Γ} {φ : S ↣ T} {η : R ↣ S} →
                 ty-subst-map σ (φ ⊙ η) ≅ⁿ ty-subst-map σ φ ⊙ ty-subst-map σ η
eq ty-subst-map-⊙ t = refl

ty-subst-cong-ty : (σ : Δ ⇒ Γ) → T ≅ᵗʸ S → T [ σ ] ≅ᵗʸ S [ σ ]
from (ty-subst-cong-ty σ T=S) = ty-subst-map σ (from T=S)
to (ty-subst-cong-ty σ T=S) = ty-subst-map σ (to T=S)
eq (isoˡ (ty-subst-cong-ty σ T=S)) t = eq (isoˡ T=S) t
eq (isoʳ (ty-subst-cong-ty σ T=S)) t = eq (isoʳ T=S) t

ty-subst-eq-subst-morph : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → (T : Ty Γ) → T [ σ ] ↣ T [ τ ]
func (ty-subst-eq-subst-morph ε T) {_} {δ} t = ty-ctx-subst T (eq ε δ) t
naturality (ty-subst-eq-subst-morph ε T) = ty-cong-2-2 T (trans hom-idˡ (sym hom-idʳ))

ty-subst-eq-subst-morph-refl : {σ : Δ ⇒ Γ} {T : Ty Γ} → ty-subst-eq-subst-morph reflˢ T ≅ⁿ id-trans (T [ σ ])
eq (ty-subst-eq-subst-morph-refl {T = T}) t = strong-ty-id T

ty-subst-eq-subst-morph-trans : {σ1 σ2 σ3 : Γ ⇒ Δ} {ε : σ1 ≅ˢ σ2} {ε' : σ2 ≅ˢ σ3} →
                                ty-subst-eq-subst-morph (transˢ ε ε') T ≅ⁿ ty-subst-eq-subst-morph ε' T ⊙ ty-subst-eq-subst-morph ε T
eq (ty-subst-eq-subst-morph-trans {T = T}) t = sym (ty-cong-2-1 T hom-idʳ)

ty-subst-cong-subst : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → (T : Ty Γ) → T [ σ ] ≅ᵗʸ T [ τ ]
from (ty-subst-cong-subst ε T) = ty-subst-eq-subst-morph ε T
to (ty-subst-cong-subst ε T) = ty-subst-eq-subst-morph (symˢ ε) T
eq (isoˡ (ty-subst-cong-subst {Γ = Γ} ε T)) t =
  -- Here we cannot use ty-id T twice because the omitted equality proofs are not ctx-id Γ _
  -- (i.e. T ⟪_⟫ t is not applied to the identity morphism in the category of elements of Γ).
  begin
    T ⟪ hom-id , _ ⟫ T ⟪ hom-id , _ ⟫ t
  ≡⟨ ty-cong-2-1 T hom-idˡ ⟩
    T ⟪ hom-id , ctx-id Γ ⟫ t
  ≡⟨ ty-id T ⟩
    t ∎
  where open ≡-Reasoning
eq (isoʳ (ty-subst-cong-subst ε T)) t =
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
from-eq ty-subst-cong-ty-refl = ty-subst-map-id

ty-subst-cong-ty-sym : {σ : Γ ⇒ Δ} {e : T ≅ᵗʸ S} → ty-subst-cong-ty σ (symᵗʸ e) ≅ᵉ symᵗʸ (ty-subst-cong-ty σ e)
from-eq ty-subst-cong-ty-sym = reflⁿ

ty-subst-cong-ty-trans : {σ : Γ ⇒ Δ} {e : T1 ≅ᵗʸ T2} {e' : T2 ≅ᵗʸ T3} →
                         ty-subst-cong-ty σ (transᵗʸ e e') ≅ᵉ transᵗʸ (ty-subst-cong-ty σ e) (ty-subst-cong-ty σ e')
from-eq ty-subst-cong-ty-trans = ty-subst-map-⊙

ty-subst-cong-natural : {σ τ : Γ ⇒ Δ} (ε : σ ≅ˢ τ) (e : T ≅ᵗʸ S) →
                        transᵗʸ (ty-subst-cong-subst ε T) (ty-subst-cong-ty τ e) ≅ᵉ transᵗʸ (ty-subst-cong-ty σ e) (ty-subst-cong-subst ε S)
eq (from-eq (ty-subst-cong-natural ε e)) _ = sym (naturality (from e))

ty-subst-cong-ty-id : (e : T ≅ᵗʸ S) → transᵗʸ (ty-subst-id T) e ≅ᵉ transᵗʸ (ty-subst-cong-ty (id-subst _) e) (ty-subst-id S)
eq (from-eq (ty-subst-cong-ty-id e)) _ = refl

ty-subst-cong-ty-id-sym : (e : T ≅ᵗʸ S) →
                          transᵗʸ e (symᵗʸ (ty-subst-id S)) ≅ᵉ transᵗʸ (symᵗʸ (ty-subst-id T)) (ty-subst-cong-ty (id-subst _) e)
eq (from-eq (ty-subst-cong-ty-id-sym e)) _ = refl

ty-subst-cong-ty-⊚ : {τ : Δ ⇒ Θ} {σ : Γ ⇒ Δ} (e : T ≅ᵗʸ S) →
                     transᵗʸ (ty-subst-comp T τ σ) (ty-subst-cong-ty _ e) ≅ᵉ transᵗʸ (ty-subst-cong-ty σ (ty-subst-cong-ty τ e)) (ty-subst-comp S τ σ)
eq (from-eq (ty-subst-cong-ty-⊚ e)) _ = refl

ty-subst-cong-subst-refl : {σ : Γ ⇒ Δ} → ty-subst-cong-subst (reflˢ {σ = σ}) T ≅ᵉ reflᵗʸ
from-eq ty-subst-cong-subst-refl = ty-subst-eq-subst-morph-refl

ty-subst-cong-subst-sym : {σ τ : Γ ⇒ Δ} {ε : σ ≅ˢ τ} → ty-subst-cong-subst (symˢ ε) T ≅ᵉ symᵗʸ (ty-subst-cong-subst ε T)
from-eq ty-subst-cong-subst-sym = reflⁿ

ty-subst-cong-subst-trans : {σ1 σ2 σ3 : Γ ⇒ Δ} {ε : σ1 ≅ˢ σ2} {ε' : σ2 ≅ˢ σ3} →
                            ty-subst-cong-subst (transˢ ε ε') T ≅ᵉ transᵗʸ (ty-subst-cong-subst ε T) (ty-subst-cong-subst ε' T)
from-eq ty-subst-cong-subst-trans = ty-subst-eq-subst-morph-trans

ty-subst-id-⊚ˡ : {σ : Γ ⇒ Δ} {T : Ty Δ} →
                 transᵗʸ (ty-subst-comp T (id-subst Δ) σ) (ty-subst-cong-subst (id-subst-unitˡ σ) T)
                   ≅ᵉ
                 ty-subst-cong-ty σ (ty-subst-id T)
eq (from-eq (ty-subst-id-⊚ˡ {T = T})) t = strong-ty-id T

ty-subst-id-⊚ʳ : {σ : Γ ⇒ Δ} {T : Ty Δ} →
                 transᵗʸ (ty-subst-comp T σ (id-subst Γ)) (ty-subst-cong-subst (id-subst-unitʳ σ) T)
                   ≅ᵉ
                 ty-subst-id (T [ σ ])
eq (from-eq (ty-subst-id-⊚ʳ {T = T})) t = strong-ty-id T

ty-subst-cong-subst-2-1 : {σ1 : Γ ⇒ Δ} {σ2 : Δ ⇒ Θ} {τ : Γ ⇒ Θ}
                          (T : Ty Θ) → σ2 ⊚ σ1 ≅ˢ τ →
                          T [ σ2 ] [ σ1 ] ≅ᵗʸ T [ τ ]
ty-subst-cong-subst-2-1 T ε = transᵗʸ (ty-subst-comp T _ _) (ty-subst-cong-subst ε T)

ty-subst-cong-subst-2-0 : {σ : Γ ⇒ Δ} {τ : Δ ⇒ Γ} (T : Ty Γ) →
                          τ ⊚ σ ≅ˢ id-subst Γ → T [ τ ] [ σ ] ≅ᵗʸ T
ty-subst-cong-subst-2-0 T ε = transᵗʸ (ty-subst-cong-subst-2-1 T ε) (ty-subst-id T)

ty-subst-cong-subst-2-2 : {Δ' : Ctx C} {σ1 : Γ ⇒ Δ} {σ2 : Δ ⇒ Θ} {τ1 : Γ ⇒ Δ'} {τ2 : Δ' ⇒ Θ}
                          (T : Ty Θ) → σ2 ⊚ σ1 ≅ˢ τ2 ⊚ τ1 →
                          T [ σ2 ] [ σ1 ] ≅ᵗʸ T [ τ2 ] [ τ1 ]
ty-subst-cong-subst-2-2 T ε =
  transᵗʸ (ty-subst-comp T _ _) (transᵗʸ (ty-subst-cong-subst ε T) (symᵗʸ (ty-subst-comp T _ _)))

ty-subst-cong-subst-2-0-natural : {τ : Δ ⇒ Γ} {σ : Γ ⇒ Δ} (ε : τ ⊚ σ ≅ˢ id-subst Γ) (e : T ≅ᵗʸ S) →
                                  transᵗʸ (ty-subst-cong-subst-2-0 T ε) e
                                    ≅ᵉ
                                  transᵗʸ (ty-subst-cong-ty σ (ty-subst-cong-ty τ e)) (ty-subst-cong-subst-2-0 S ε)
ty-subst-cong-subst-2-0-natural ε e =
    transᵉ transᵗʸ-assoc (
  transᵉ (transᵗʸ-congʳ (ty-subst-cong-ty-id e)) (
    transᵉ (transᵉ (symᵉ transᵗʸ-assoc) (transᵗʸ-congˡ transᵗʸ-assoc)) (
  transᵉ (transᵗʸ-congˡ (transᵗʸ-congʳ (ty-subst-cong-natural ε e))) (
    transᵉ (transᵗʸ-congˡ (symᵉ transᵗʸ-assoc)) (
  transᵉ (transᵗʸ-congˡ (transᵗʸ-congˡ (ty-subst-cong-ty-⊚ e))) (
    transᵉ (transᵗʸ-congˡ transᵗʸ-assoc) transᵗʸ-assoc))))))

ty-subst-cong-subst-2-0-iso : {σ : Γ ⇒ Δ} {τ : Δ ⇒ Γ} (T : Ty Δ)
                              (ε :  σ ⊚ τ ≅ˢ id-subst Δ)
                              (ε' : τ ⊚ σ ≅ˢ id-subst Γ) →
                              ty-subst-cong-ty σ (ty-subst-cong-subst-2-0 T ε) ≅ᵉ ty-subst-cong-subst-2-0 (T [ σ ]) ε'
eq (from-eq (ty-subst-cong-subst-2-0-iso T ε ε')) _ = ty-cong T refl

ty-subst-cong-subst-2-2-id : {σ : Γ ⇒ Δ} (T : Ty Δ) →
                             transᵗʸ (ty-subst-cong-subst-2-2 T (transˢ (id-subst-unitˡ σ) (symˢ (id-subst-unitʳ σ)))) (ty-subst-id (T [ σ ]))
                               ≅ᵉ
                             ty-subst-cong-ty σ (ty-subst-id T)
eq (from-eq (ty-subst-cong-subst-2-2-id T)) _ = strong-ty-id T

ty-subst-cong-subst-2-2-natural-from : {Δ' : Ctx C} {σ1 : Γ ⇒ Δ} {σ2 : Δ ⇒ Θ} {τ1 : Γ ⇒ Δ'} {τ2 : Δ' ⇒ Θ}
                                       {T S : Ty Θ} (φ : T ↣ S) (ε : σ2 ⊚ σ1 ≅ˢ τ2 ⊚ τ1) →
                                       from (ty-subst-cong-subst-2-2 S ε) ⊙ ty-subst-map σ1 (ty-subst-map σ2 φ)
                                         ≅ⁿ
                                       ty-subst-map τ1 (ty-subst-map τ2 φ) ⊙ from (ty-subst-cong-subst-2-2 T ε)
eq (ty-subst-cong-subst-2-2-natural-from φ ε) t = naturality φ

ty-subst-cong-subst-2-2-natural-to : {Δ' : Ctx C} {σ1 : Γ ⇒ Δ} {σ2 : Δ ⇒ Θ} {τ1 : Γ ⇒ Δ'} {τ2 : Δ' ⇒ Θ}
                                     {T S : Ty Θ} (φ : T ↣ S) (ε : σ2 ⊚ σ1 ≅ˢ τ2 ⊚ τ1) →
                                     to (ty-subst-cong-subst-2-2 S ε) ⊙ ty-subst-map τ1 (ty-subst-map τ2 φ)
                                       ≅ⁿ
                                     ty-subst-map σ1 (ty-subst-map σ2 φ) ⊙ to (ty-subst-cong-subst-2-2 T ε)
eq (ty-subst-cong-subst-2-2-natural-to φ ε) t = naturality φ

ty-subst-cong-subst-2-2-natural : {Δ' : Ctx C} {σ1 : Γ ⇒ Δ} {σ2 : Δ ⇒ Θ} {τ1 : Γ ⇒ Δ'} {τ2 : Δ' ⇒ Θ}
                                  {T S : Ty Θ} (e : T ≅ᵗʸ S) (ε : σ2 ⊚ σ1 ≅ˢ τ2 ⊚ τ1) →
                                  transᵗʸ (ty-subst-cong-subst-2-2 T ε) (ty-subst-cong-ty τ1 (ty-subst-cong-ty τ2 e))
                                    ≅ᵉ
                                  transᵗʸ (ty-subst-cong-ty σ1 (ty-subst-cong-ty σ2 e)) (ty-subst-cong-subst-2-2 S ε)
from-eq (ty-subst-cong-subst-2-2-natural e ε) = symⁿ (ty-subst-cong-subst-2-2-natural-from (from e) ε)


-- Nicer syntax for substitutions coming from context equality
ιc[_]_ : Γ ≅ᶜ Δ → Ty Δ → Ty Γ
ιc[ Γ=Δ ] T = T [ from Γ=Δ ]

ιc⁻¹[_]_ : Γ ≅ᶜ Δ → Ty Γ → Ty Δ
ιc⁻¹[ Γ=Δ ] T = T [ to Γ=Δ ]
