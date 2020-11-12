{-# OPTIONS --without-K #-}

--------------------------------------------------
-- Types
--------------------------------------------------

open import Categories

module CwF-Structure.Types {C : Category} where

open import Level renaming (zero to lzero; suc to lsuc)
open import Function hiding (_⟨_⟩_; _↣_)
open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality
  hiding ([_]; naturality) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

open import Helpers
open import CwF-Structure.Contexts

open Category C

infixr 11 _⟪_,_⟫_
infix 10 _↣_
infix 1 _≅ⁿ_ _≅ᵗʸ_
infixl 20 _⊙_

private
  variable
    ℓc ℓt ℓt' r rc rt rt' : Level
    x y z : Ob
    Δ Γ Θ : Ctx C ℓ r


--------------------------------------------------
-- Definition of types in a context

-- A type in context Γ is defined as a presheaf over the category of elements of Γ.
-- A morphism in the category of elements of Γ from (x, γx) to (y, γy) consists of
--   a morphism f : Hom x y together with a proof that Γ ⟪ f ⟫ γy ≈[ Γ ]≈ γx. This explains
--   the type of the field morph (representing the action of the presheaf on morphisms).

record Ty (Γ : Ctx C ℓc rc) (ℓt rt : Level) : Set (ℓc ⊔ lsuc ℓt ⊔ rc ⊔ lsuc rt) where
  constructor MkTy
  no-eta-equality

  infix 15 _⟨_,_⟩

  open Setoid
  
  field
    type : (x : Ob) (γ : Γ ⟨ x ⟩) → Setoid ℓt rt

  _⟨_,_⟩ : (x : Ob) → Γ ⟨ x ⟩ → Set ℓt
  _⟨_,_⟩ x γ = Carrier (type x γ)

  ty≈ : (x : Ob) (γ : Γ ⟨ x ⟩) → _⟨_,_⟩ x γ → _⟨_,_⟩ x γ → Set rt
  ty≈ x γ = _≈_ (type x γ)

  field
    morph : ∀ {x y} (f : Hom x y) {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} → Γ ⟪ f ⟫ γy ≈[ Γ ]≈ γx →
            _⟨_,_⟩ y γy → _⟨_,_⟩ x γx
    morph-cong : ∀ {x y} (f : Hom x y) {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} (eγ : Γ ⟪ f ⟫ γy ≈[ Γ ]≈ γx) →
                 Congruent (ty≈ y γy) (ty≈ x γx) (morph f eγ)
    morph-hom-cong : {f f' : Hom x y} (e-hom : f ≡ f')
                     {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} {eγ : Γ ⟪ f ⟫ γy ≈[ Γ ]≈ γx} {eγ' : Γ ⟪ f' ⟫ γy ≈[ Γ ]≈ γx}
                     {t : _⟨_,_⟩ y γy} →
                     ty≈ x γx (morph f eγ t) (morph f' eγ' t)
    morph-id : ∀ {x} {γ : Γ ⟨ x ⟩} (t : _⟨_,_⟩ x γ) → ty≈ x γ (morph hom-id (rel-id Γ γ) t) t
    morph-comp : ∀ {x y z} (f : Hom x y) (g : Hom y z) {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} →
                 (eq-zy : Γ ⟪ g ⟫ γz ≈[ Γ ]≈ γy) (eq-yx : Γ ⟪ f ⟫ γy ≈[ Γ ]≈ γx) (t : _⟨_,_⟩ z γz) →
                 ty≈ x γx (morph (g ∙ f) (strong-rel-comp Γ eq-zy eq-yx) t) (morph f eq-yx (morph g eq-zy t))

  ty≈-refl : {x : Ob} {γ : Γ ⟨ x ⟩} {t : _⟨_,_⟩ x γ} → ty≈ x γ t t
  ty≈-refl {x}{γ} = refl (type x γ)

  ty≈-sym : {x : Ob} {γ : Γ ⟨ x ⟩} {t1 t2 : _⟨_,_⟩ x γ} → ty≈ x γ t1 t2 → ty≈ x γ t2 t1
  ty≈-sym {x}{γ} = sym (type x γ)

  ty≈-trans : {x : Ob} {γ : Γ ⟨ x ⟩} {t1 t2 t3 : _⟨_,_⟩ x γ} → ty≈ x γ t1 t2 → ty≈ x γ t2 t3 → ty≈ x γ t1 t3
  ty≈-trans {x}{γ} = trans (type x γ)

open Ty public

ty≈-syntax : (T : Ty Γ ℓ r) {x : Category.Ob C} {γ : Γ ⟨ x ⟩} (t1 t2 : T ⟨ x , γ ⟩) → Set r
ty≈-syntax T {x}{γ} = ty≈ T x γ

infix 1 ty≈-syntax
syntax ty≈-syntax T t1 t2 = t1 ≈⟦ T ⟧≈ t2

private
  variable
    T S R : Ty Γ ℓ r
{-
_⟨_,_⟩ : Ty Γ ℓ → (x : Ob) → Γ ⟨ x ⟩ → Set ℓ
T ⟨ x , γ ⟩ = type T x γ

_⟪_,_⟫ : (T : Ty Γ ℓ) (f : Hom x y) {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} → Γ ⟪ f ⟫ γy ≡ γx →
         T ⟨ y , γy ⟩ → T ⟨ x , γx ⟩
_⟪_,_⟫ T f eγ = morph T f eγ
-}
_⟪_,_⟫_ : (T : Ty Γ ℓ r) (f : Hom x y) {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} → Γ ⟪ f ⟫ γy ≈[ Γ ]≈ γx →
          T ⟨ y , γy ⟩ → T ⟨ x , γx ⟩
T ⟪ f , eγ ⟫ t = morph T f eγ t

{-
-- This is one of the places where we assume uip (by pattern matching on both eγ and eγ'). We could probably avoid it
-- by adding a field to a type T requiring morph T to "not depend on eγ" (propositionally).
morph-cong : (T : Ty Γ ℓ) {f f' : Hom x y} (e-hom : f ≡ f')
             {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} (eγ : Γ ⟪ f ⟫ γy ≡ γx) (eγ' : Γ ⟪ f' ⟫ γy ≡ γx)
             {t : T ⟨ y , γy ⟩} →
             T ⟪ f , eγ ⟫ t ≡ T ⟪ f' , eγ' ⟫ t
morph-cong T refl refl refl = refl
-}
ctx-element-subst : (T : Ty Γ ℓ r) {γ γ' : Γ ⟨ x ⟩} → γ ≈[ Γ ]≈ γ' → T ⟨ x , γ ⟩ → T ⟨ x , γ' ⟩
ctx-element-subst {Γ = Γ} T eγ = T ⟪ hom-id , ctx≈-trans Γ (rel-id Γ _) eγ ⟫_
{-
-- The following definitions are needed when defining context extension.
morph-transport : (T : Ty Γ ℓ) {f : Hom x y}
                  {γ1 : Γ ⟨ y ⟩} {γ2 γ3 : Γ ⟨ x ⟩}
                  (eq12 : Γ ⟪ f ⟫ γ1 ≡ γ2) (eq23 : γ2 ≡ γ3)
                  (t : T ⟨ y , γ1 ⟩) →
                  transport (λ - → T ⟨ x , - ⟩) eq23 (T ⟪ f , eq12 ⟫ t) ≡ T ⟪ f , trans eq12 eq23 ⟫ t
morph-transport T refl refl t = refl
-}
module _ {Γ : Ctx C ℓc rc} (T : Ty Γ ℓt rt) where
  strict-morph : (f : Hom x y) (γ : Γ ⟨ y ⟩) → T ⟨ y , γ ⟩ → T ⟨ x , Γ ⟪ f ⟫ γ ⟩
  strict-morph f γ t = T ⟪ f , ctx≈-refl Γ ⟫ t
{-
  strict-morph-id : {γ : Γ ⟨ y ⟩} (t : T ⟨ y , γ ⟩) →
                    transport (λ - → T ⟨ y , - ⟩) (rel-id Γ γ) (strict-morph hom-id γ t) ≡ t
  strict-morph-id {y = y}{γ = γ} t =
    begin
      transport (λ - → T ⟨ y , - ⟩) (rel-id Γ γ) (strict-morph hom-id γ t)
    ≡⟨ morph-transport T refl (rel-id Γ γ) t ⟩
      T ⟪ hom-id , rel-id Γ γ ⟫ t
    ≡⟨ morph-id T t ⟩
      t ∎
    where open ≡-Reasoning

  strict-morph-comp : (f : Hom x y) (g : Hom y z) {γ : Γ ⟨ z ⟩} (t : T ⟨ z , γ ⟩) →
                      transport (λ - → T ⟨ x , - ⟩) (rel-comp Γ f g γ) (strict-morph (g ∙ f) γ t) ≡
                        strict-morph f (Γ ⟪ g ⟫ γ) (strict-morph g γ t)
  strict-morph-comp {x = x} f g {γ = γ} t =
    begin
      transport (λ - → T ⟨ x , - ⟩) (rel-comp Γ f g γ) (strict-morph (g ∙ f) γ t)
    ≡⟨ morph-transport T refl (rel-comp Γ f g γ) t ⟩
      T ⟪ g ∙ f , rel-comp Γ f g γ ⟫ t
    ≡˘⟨ cong (λ - → T ⟪ g ∙ f , - ⟫ t) (trans-reflʳ _) ⟩
      T ⟪ g ∙ f , trans (rel-comp Γ f g γ) refl ⟫ t
    ≡⟨ morph-comp T f g refl refl t ⟩
      strict-morph f (Γ ⟪ g ⟫ γ) (strict-morph g γ t) ∎
    where open ≡-Reasoning
-}

--------------------------------------------------
-- Natural transformations between types

record _↣_ {Γ : Ctx C ℓc rc} (T : Ty Γ ℓt rt) (S : Ty Γ ℓt' rt') : Set (ℓc ⊔ ℓt ⊔ ℓt' ⊔ rc ⊔ rt ⊔ rt') where
  no-eta-equality
  field
    func : ∀ {x}{γ} → T ⟨ x , γ ⟩ → S ⟨ x , γ ⟩
    func-cong : ∀ {x}{γ} → Congruent (ty≈ T x γ) (ty≈ S x γ) func
    naturality : ∀ {x y} {f : Hom x y} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} {eγ : Γ ⟪ f ⟫ γy ≈[ Γ ]≈ γx} (t : T ⟨ y , γy ⟩) →
                 S ⟪ f , eγ ⟫ (func t) ≈⟦ S ⟧≈ func (T ⟪ f , eγ ⟫ t)
open _↣_ public

record _≅ⁿ_ {Γ : Ctx C ℓc rc} {T : Ty Γ ℓt rt} {S : Ty Γ ℓt' rt'} (η φ : T ↣ S) : Set (ℓc ⊔ ℓt ⊔ rt') where
  field
    eq : ∀ {x γ} (t : T ⟨ x , γ ⟩) → func η t ≈⟦ S ⟧≈ func φ t
open _≅ⁿ_ public

≅ⁿ-refl : {η : T ↣ S} → η ≅ⁿ η
eq (≅ⁿ-refl {S = S}) _ = ty≈-refl S

≅ⁿ-sym : {η φ : T ↣ S} → η ≅ⁿ φ → φ ≅ⁿ η
eq (≅ⁿ-sym {S = S} η=φ) t = ty≈-sym S (eq η=φ t)

≅ⁿ-trans : {η φ µ : T ↣ S} → η ≅ⁿ φ → φ ≅ⁿ µ → η ≅ⁿ µ
eq (≅ⁿ-trans {S = S} η=φ φ=µ) t = ty≈-trans S (eq η=φ t) (eq φ=µ t)

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

id-trans : (T : Ty Γ ℓ r) → T ↣ T
func (id-trans T) = id
func-cong (id-trans T) e = e
naturality (id-trans T) _ = ty≈-refl T

_⊙_ : S ↣ T → R ↣ S → R ↣ T
func (φ ⊙ η) = func φ ∘ func η
func-cong (φ ⊙ η) = func-cong φ ∘ func-cong η
naturality (_⊙_ {S = S}{T = T}{R = R} φ η) {f = f}{eγ = eγ} r =
  begin
    T ⟪ f , eγ ⟫ func φ (func η r)
  ≈⟨ naturality φ (func η r) ⟩
    func φ (S ⟪ f , eγ ⟫ func η r)
  ≈⟨ func-cong φ (naturality η r) ⟩
    func φ (func η (R ⟪ f , eγ ⟫ r)) ∎
  where open SetoidReasoning (type T _ _)

⊙-id-transʳ : (η : T ↣ S) → η ⊙ id-trans T ≅ⁿ η
eq (⊙-id-transʳ {S = S} η) _ = ty≈-refl S

⊙-id-transˡ : (η : T ↣ S) → id-trans S ⊙ η ≅ⁿ η
eq (⊙-id-transˡ {S = S} η) _ = ty≈-refl S

⊙-assoc : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ r₁ r₂ r₃ r₄}
           {T₁ : Ty Γ ℓ₁ r₁} {T₂ : Ty Γ ℓ₂ r₂} {T₃ : Ty Γ ℓ₃ r₃} {T₄ : Ty Γ ℓ₄ r₄}
           (η₃₄ : T₃ ↣ T₄) (η₂₃ : T₂ ↣ T₃) (η₁₂ : T₁ ↣ T₂) →
           (η₃₄ ⊙ η₂₃) ⊙ η₁₂ ≅ⁿ η₃₄ ⊙ (η₂₃ ⊙ η₁₂)
eq (⊙-assoc {T₄ = T₄} η₃₄ η₂₃ η₁₂) _ = ty≈-refl T₄

⊙-congˡ : (φ : S ↣ T) {η η' : R ↣ S} → η ≅ⁿ η' → φ ⊙ η ≅ⁿ φ ⊙ η'
eq (⊙-congˡ φ η=η') δ = func-cong φ (eq η=η' δ)

⊙-congʳ : {φ φ' : S ↣ T} (η : R ↣ S) → φ ≅ⁿ φ' → φ ⊙ η ≅ⁿ φ' ⊙ η
eq (⊙-congʳ η φ=φ') δ = eq φ=φ' (func η δ)


--------------------------------------------------
-- Equivalence of types

-- Two types are said to be equivalent if they are naturally isomorphic as presheaves.
-- This turns out to be easier to work with than standard propositional equality.
record _≅ᵗʸ_ {Γ : Ctx C ℓc rc} (T : Ty Γ ℓt rt) (S : Ty Γ ℓt' rt') : Set (ℓc ⊔ ℓt ⊔ ℓt' ⊔ rc ⊔ rt ⊔ rt') where
  field
    from : T ↣ S
    to : S ↣ T
    isoˡ : to ⊙ from ≅ⁿ id-trans T
    isoʳ : from ⊙ to ≅ⁿ id-trans S
open _≅ᵗʸ_ public

≅ᵗʸ-refl : T ≅ᵗʸ T
from (≅ᵗʸ-refl {T = T}) = id-trans T
to (≅ᵗʸ-refl {T = T}) = id-trans T
eq (isoˡ (≅ᵗʸ-refl {T = T})) _ = ty≈-refl T
eq (isoʳ (≅ᵗʸ-refl {T = T})) _ = ty≈-refl T

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

  _≅⟨⟩_ : (T : Ty Γ ℓt rt) → T ≅ᵗʸ S → T ≅ᵗʸ S
  _ ≅⟨⟩ T=S = T=S

  step-≅ : (T : Ty Γ ℓt rt) → S ≅ᵗʸ R → T ≅ᵗʸ S → T ≅ᵗʸ R
  step-≅ _ S≅R T≅S = ≅ᵗʸ-trans T≅S S≅R

  step-≅˘ : (T : Ty Γ ℓt rt) → S ≅ᵗʸ R → S ≅ᵗʸ T → T ≅ᵗʸ R
  step-≅˘ _ S≅R S≅T = ≅ᵗʸ-trans (≅ᵗʸ-sym S≅T) S≅R

  _∎ : (T : Ty Γ ℓt rt) → T ≅ᵗʸ T
  _∎ _ = ≅ᵗʸ-refl

  syntax step-≅  T S≅R T≅S = T ≅⟨  T≅S ⟩ S≅R
  syntax step-≅˘ T S≅R S≅T = T ≅˘⟨ S≅T ⟩ S≅R


--------------------------------------------------
-- Substitution of types

_[_] : Ty Γ ℓ r → Δ ⇒ Γ → Ty Δ ℓ r
type (T [ σ ]) x δ = type T x (func σ δ)
morph (_[_] {Γ = Γ} T σ) f {δy}{δx} eq-yx t = T ⟪ f , proof ⟫ t
  where
    proof : Γ ⟪ f ⟫ func σ δy ≈[ Γ ]≈ func σ δx
    proof = ctx≈-trans Γ (naturality σ δy) (func-cong σ eq-yx)
morph-cong (T [ σ ]) f eδ = morph-cong T f _
morph-hom-cong (T [ σ ]) ef = morph-hom-cong T ef
morph-id (T [ σ ]) t = ty≈-trans T (morph-hom-cong T ≡-refl)
                                   (morph-id T t)
morph-comp (T [ σ ]) f g eq-zy eq-yx t = ty≈-trans T (morph-hom-cong T ≡-refl)
                                                     (morph-comp T f g _ _ t)

ty-subst-id : (T : Ty Γ ℓ r) → T [ id-subst Γ ] ≅ᵗʸ T
func (from (ty-subst-id T)) = id
func-cong (from (ty-subst-id T)) = id
naturality (from (ty-subst-id T)) _ = morph-hom-cong T ≡-refl
func (to (ty-subst-id T)) = id
func-cong (to (ty-subst-id T)) = id
naturality (to (ty-subst-id T)) _ = morph-hom-cong T ≡-refl
eq (isoˡ (ty-subst-id T)) _ = ty≈-refl T
eq (isoʳ (ty-subst-id T)) _ = ty≈-refl T

ty-subst-comp : (T : Ty Θ ℓ r) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → T [ τ ] [ σ ] ≅ᵗʸ T [ τ ⊚ σ ]
func (from (ty-subst-comp T τ σ)) = id
func-cong (from (ty-subst-comp T τ σ)) = id
naturality (from (ty-subst-comp T τ σ)) _ = morph-hom-cong T ≡-refl
func (to (ty-subst-comp T τ σ)) = id
func-cong (to (ty-subst-comp T τ σ)) = id
naturality (to (ty-subst-comp T τ σ)) _ = morph-hom-cong T ≡-refl
eq (isoˡ (ty-subst-comp T τ σ)) _ = ty≈-refl T
eq (isoʳ (ty-subst-comp T τ σ)) _ = ty≈-refl T

ty-subst-map : (σ : Δ ⇒ Γ) → (T ↣ S) → T [ σ ] ↣ S [ σ ]
func (ty-subst-map σ η) t = func η t
func-cong (ty-subst-map σ η) e = func-cong η e
naturality (ty-subst-map σ η) t = naturality η t

ty-subst-map-cong : {σ : Δ ⇒ Γ} {η φ : T ↣ S} →
                    η ≅ⁿ φ → ty-subst-map σ η ≅ⁿ ty-subst-map σ φ
eq (ty-subst-map-cong e) t = eq e t

ty-subst-map-id : (σ : Δ ⇒ Γ) → ty-subst-map σ (id-trans T) ≅ⁿ id-trans (T [ σ ])
eq (ty-subst-map-id {T = T} σ) t = ty≈-refl T

ty-subst-map-comp : (σ : Δ ⇒ Γ) (φ : S ↣ T) (η : R ↣ S) →
                    ty-subst-map σ (φ ⊙ η) ≅ⁿ ty-subst-map σ φ ⊙ ty-subst-map σ η
eq (ty-subst-map-comp {T = T} σ φ η) t = ty≈-refl T

ty-subst-cong-ty : (σ : Δ ⇒ Γ) → T ≅ᵗʸ S → T [ σ ] ≅ᵗʸ S [ σ ]
from (ty-subst-cong-ty σ T=S) = ty-subst-map σ (from T=S)
to (ty-subst-cong-ty σ T=S) = ty-subst-map σ (to T=S)
eq (isoˡ (ty-subst-cong-ty σ T=S)) t = eq (isoˡ T=S) t
eq (isoʳ (ty-subst-cong-ty σ T=S)) t = eq (isoʳ T=S) t

ty-subst-cong-subst : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → (T : Ty Γ ℓ r) → T [ σ ] ≅ᵗʸ T [ τ ]
func (from (ty-subst-cong-subst σ=τ T)) {_}{δ} t = ctx-element-subst T (eq σ=τ δ) t
func-cong (from (ty-subst-cong-subst σ=τ T)) e = morph-cong T hom-id _ e
naturality (from (ty-subst-cong-subst σ=τ T)) {_}{_}{f} t =
  begin
    T ⟪ f , _ ⟫ T ⟪ hom-id , _ ⟫ t
  ≈˘⟨ morph-comp T f hom-id _ _ t ⟩
    T ⟪ hom-id ∙ f , _ ⟫ t
  ≈⟨ morph-hom-cong T (≡-trans hom-idˡ (≡-sym hom-idʳ)) ⟩
    T ⟪ f ∙ hom-id , _ ⟫ t
  ≈⟨ morph-comp T hom-id f _ _ t ⟩
    T ⟪ hom-id , _ ⟫ T ⟪ f , _ ⟫ t ∎
  where open SetoidReasoning (type T _ _)
func (to (ty-subst-cong-subst {Γ = Γ} σ=τ T)) {_}{δ} t = ctx-element-subst T (ctx≈-sym Γ (eq σ=τ δ)) t
func-cong (to (ty-subst-cong-subst σ=τ T)) e = morph-cong T hom-id _ e
naturality (to (ty-subst-cong-subst σ=τ T)) {_}{_}{f} t =
  begin
    T ⟪ f , _ ⟫ T ⟪ hom-id , _ ⟫ t
  ≈˘⟨ morph-comp T f hom-id _ _ t ⟩
    T ⟪ hom-id ∙ f , _ ⟫ t
  ≈⟨ morph-hom-cong T (≡-trans hom-idˡ (≡-sym hom-idʳ)) ⟩
    T ⟪ f ∙ hom-id , _ ⟫ t
  ≈⟨ morph-comp T hom-id f _ _ t ⟩
    T ⟪ hom-id , _ ⟫ T ⟪ f , _ ⟫ t ∎
  where open SetoidReasoning (type T _ _)
eq (isoˡ (ty-subst-cong-subst {Γ = Γ} σ=τ T)) t =
  -- Here we cannot use morph-id T twice because the omitted equality proofs are not rel-id Γ _
  -- (i.e. T ⟪_⟫ t is not applied to the identity morphism in the category of elements of Γ).
  begin
    T ⟪ hom-id , _ ⟫ T ⟪ hom-id , _ ⟫ t
  ≈˘⟨ morph-comp T hom-id hom-id _ _ t ⟩
    T ⟪ hom-id ∙ hom-id , _ ⟫ t
  ≈⟨ morph-hom-cong T hom-idˡ ⟩
    T ⟪ hom-id , rel-id Γ _ ⟫ t
  ≈⟨ morph-id T t ⟩
    t ∎
  where open SetoidReasoning (type T _ _)
eq (isoʳ (ty-subst-cong-subst σ=τ T)) t =
  begin
    T ⟪ hom-id , _ ⟫ T ⟪ hom-id , _ ⟫ t
  ≈˘⟨ morph-comp T hom-id hom-id _ _ t ⟩
    T ⟪ hom-id ∙ hom-id , _ ⟫ t
  ≈⟨ morph-hom-cong T hom-idˡ ⟩
    T ⟪ hom-id , _ ⟫ t
  ≈⟨ morph-id T t ⟩
    t ∎
  where open SetoidReasoning (type T _ _)
