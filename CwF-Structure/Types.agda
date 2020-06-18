--------------------------------------------------
-- Types
--------------------------------------------------

open import Categories

module CwF-Structure.Types {C : Category} where

open import Level renaming (zero to lzero; suc to lsuc)
open import Function hiding (_⟨_⟩_; _↣_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Helpers
open import CwF-Structure.Contexts

open Category C

infix 15 _⟨_,_⟩
infixr 11 _⟪_,_⟫_
infix 10 _↣_
infix 1 _≅ⁿ_ _≅ᵗʸ_
infixl 20 _⊙_

private
  variable
    x y z : Ob
    Δ Γ Θ : Ctx C ℓ


--------------------------------------------------
-- Definition of types in a context

-- A type in context Γ is defined as a presheaf over the category of elements of Γ.
-- A morphism in the category of elements of Γ from (x, γx) to (y, γy) consists of
--   a morphism f : Hom x y together with a proof that Γ ⟪ f ⟫ γy ≡ γx. This explains
--   the type of the field morph (representing the action of the presheaf on morphisms).
record Ty {ℓ} (Γ : Ctx C ℓ) : Set (lsuc ℓ) where
  constructor MkTy
  no-eta-equality

  field
    type : (x : Ob) (γ : Γ ⟨ x ⟩) → Set ℓ
    morph : ∀ {x y} (f : Hom x y) {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} → Γ ⟪ f ⟫ γy ≡ γx → type y γy → type x γx
    morph-id : ∀ {x} {γ : Γ ⟨ x ⟩} (t : type x γ) → morph hom-id (rel-id Γ γ) t ≡ t
    morph-comp : ∀ {x y z} (f : Hom x y) (g : Hom y z) {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} →
                 (eq-zy : Γ ⟪ g ⟫ γz ≡ γy) (eq-yx : Γ ⟪ f ⟫ γy ≡ γx) (t : type z γz) →
                 morph (g ∙ f) (strong-rel-comp Γ eq-zy eq-yx) t ≡ morph f eq-yx (morph g eq-zy t)
open Ty public

_⟨_,_⟩ : {Γ : Ctx C ℓ} → Ty Γ → (x : Ob) → Γ ⟨ x ⟩ → Set ℓ
T ⟨ x , γ ⟩ = type T x γ

_⟪_,_⟫ : (T : Ty Γ) (f : Hom x y) {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} → Γ ⟪ f ⟫ γy ≡ γx →
         T ⟨ y , γy ⟩ → T ⟨ x , γx ⟩
_⟪_,_⟫ T f eγ = morph T f eγ

_⟪_,_⟫_ : (T : Ty Γ) (f : Hom x y) {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} → Γ ⟪ f ⟫ γy ≡ γx →
          T ⟨ y , γy ⟩ → T ⟨ x , γx ⟩
T ⟪ f , eγ ⟫ t = (T ⟪ f , eγ ⟫) t

-- This is one of the places where we assume uip (by pattern matching on both eγ and eγ'). We could probably avoid it
-- by adding a field to a type T requiring morph T to "not depend on eγ" (propositionally).
morph-cong : (T : Ty Γ) {f f' : Hom x y} (e-hom : f ≡ f')
             {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} (eγ : Γ ⟪ f ⟫ γy ≡ γx) (eγ' : Γ ⟪ f' ⟫ γy ≡ γx)
             {t : T ⟨ y , γy ⟩} →
             T ⟪ f , eγ ⟫ t ≡ T ⟪ f' , eγ' ⟫ t
morph-cong T refl refl refl = refl

ctx-element-subst : (T : Ty Γ) {γ γ' : Γ ⟨ x ⟩} → γ ≡ γ' → T ⟨ x , γ ⟩ → T ⟨ x , γ' ⟩
ctx-element-subst {Γ = Γ} T eγ = T ⟪ hom-id , trans (rel-id Γ _) eγ ⟫

-- The following definitions are needed when defining context extension.
morph-subst : (T : Ty Γ) {f : Hom x y}
              {γ1 : Γ ⟨ y ⟩} {γ2 γ3 : Γ ⟨ x ⟩}
              (eq12 : Γ ⟪ f ⟫ γ1 ≡ γ2) (eq23 : γ2 ≡ γ3)
              (t : T ⟨ y , γ1 ⟩) →
              subst (λ - → T ⟨ x , - ⟩) eq23 (T ⟪ f , eq12 ⟫ t) ≡ T ⟪ f , trans eq12 eq23 ⟫ t
morph-subst T refl refl t = refl

module _ {Γ : Ctx C ℓ} (T : Ty Γ) where
  strict-morph : (f : Hom x y) (γ : Γ ⟨ y ⟩) → T ⟨ y , γ ⟩ → T ⟨ x , Γ ⟪ f ⟫ γ ⟩
  strict-morph f γ t = T ⟪ f , refl ⟫ t

  strict-morph-id : {γ : Γ ⟨ y ⟩} (t : T ⟨ y , γ ⟩) →
                    subst (λ - → T ⟨ y , - ⟩) (rel-id Γ γ) (strict-morph hom-id γ t) ≡ t
  strict-morph-id t = trans (morph-subst T refl (rel-id Γ _) t)
                            (morph-id T t)

  strict-morph-comp : (f : Hom x y) (g : Hom y z) {γ : Γ ⟨ z ⟩} (t : T ⟨ z , γ ⟩) →
                      subst (λ - → T ⟨ x , - ⟩) (rel-comp Γ f g γ) (strict-morph (g ∙ f) γ t) ≡
                        strict-morph f (Γ ⟪ g ⟫ γ) (strict-morph g γ t)
  strict-morph-comp f g t = trans (morph-subst T refl (rel-comp Γ f g _) t)
                                  (trans (cong (λ - → T ⟪ _ , - ⟫ t) (sym (trans-reflʳ _)))
                                         (morph-comp T f g refl refl t))


--------------------------------------------------
-- Natural transformations between types

record _↣_ {ℓ} {Γ : Ctx C ℓ} (T S : Ty Γ) : Set ℓ where
  field
    func : ∀ {x} {γ} → T ⟨ x , γ ⟩ → S ⟨ x , γ ⟩
    naturality : ∀ {x y} {f : Hom x y} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} {eγ : Γ ⟪ f ⟫ γy ≡ γx} (t : T ⟨ y , γy ⟩) →
                 S ⟪ f , eγ ⟫ (func t) ≡ func (T ⟪ f , eγ ⟫ t)
open _↣_ public

record _≅ⁿ_ {ℓ} {Γ : Ctx C ℓ} {T S : Ty Γ} (η φ : T ↣ S) : Set ℓ where
  field
    eq : ∀ {x γ} (t : T ⟨ x , γ ⟩) → func η t ≡ func φ t
open _≅ⁿ_ public

≅ⁿ-refl : {T S : Ty Γ} {η : T ↣ S} → η ≅ⁿ η
eq ≅ⁿ-refl _ = refl

≅ⁿ-sym : {T S : Ty Γ} {η φ : T ↣ S} → η ≅ⁿ φ → φ ≅ⁿ η
eq (≅ⁿ-sym η=φ) t = sym (eq η=φ t)

≅ⁿ-trans : {T S : Ty Γ} {η φ µ : T ↣ S} → η ≅ⁿ φ → φ ≅ⁿ µ → η ≅ⁿ µ
eq (≅ⁿ-trans η=φ φ=µ) t = trans (eq η=φ t) (eq φ=µ t)

module ≅ⁿ-Reasoning {Γ : Ctx C ℓ} {T S : Ty Γ} where
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
naturality (id-trans T) _ = refl

_⊙_ : {R S T : Ty Γ} → S ↣ T → R ↣ S → R ↣ T
func (φ ⊙ η) = func φ ∘ func η
naturality (φ ⊙ η) r = trans (naturality φ (func η r))
                              (cong (func φ) (naturality η r))

⊙-id-transʳ : {T S : Ty Γ} (η : T ↣ S) → η ⊙ id-trans T ≅ⁿ η
eq (⊙-id-transʳ η) _ = refl

⊙-id-transˡ : {T S : Ty Γ} (η : T ↣ S) → id-trans S ⊙ η ≅ⁿ η
eq (⊙-id-transˡ η) _ = refl

⊙-assoc : {T₁ T₂ T₃ T₄ : Ty Γ}  (η₃₄ : T₃ ↣ T₄) (η₂₃ : T₂ ↣ T₃) (η₁₂ : T₁ ↣ T₂) → (η₃₄ ⊙ η₂₃) ⊙ η₁₂ ≅ⁿ η₃₄ ⊙ (η₂₃ ⊙ η₁₂)
eq (⊙-assoc η₃₄ η₂₃ η₁₂) _ = refl

⊙-congˡ : {R S T : Ty Γ} (φ : S ↣ T) {η η' : R ↣ S} → η ≅ⁿ η' → φ ⊙ η ≅ⁿ φ ⊙ η'
eq (⊙-congˡ φ η=η') δ = cong (func φ) (eq η=η' δ)

⊙-congʳ : {R S T : Ty Γ} {φ φ' : S ↣ T} (η : R ↣ S) → φ ≅ⁿ φ' → φ ⊙ η ≅ⁿ φ' ⊙ η
eq (⊙-congʳ η φ=φ') δ = eq φ=φ' (func η δ)


--------------------------------------------------
-- Equivalence of types

-- Two types are said to be equivalent if they are naturally isomorphic as presheaves.
-- This turns out to be easier to work with than normal propositional equality. In particular,
-- it lets us easily convert a term of type T to a term of type S when T ≅ᵗʸ S.
record _≅ᵗʸ_ {ℓ} {Γ : Ctx C ℓ} (T S : Ty Γ) : Set ℓ where
  field
    from : T ↣ S
    to : S ↣ T
    isoˡ : to ⊙ from ≅ⁿ id-trans T
    isoʳ : from ⊙ to ≅ⁿ id-trans S
open _≅ᵗʸ_ public

≅ᵗʸ-refl : {T : Ty Γ} → T ≅ᵗʸ T
from (≅ᵗʸ-refl {T = T}) = id-trans T
to (≅ᵗʸ-refl {T = T}) = id-trans T
isoˡ ≅ᵗʸ-refl = ≅ⁿ-refl
isoʳ ≅ᵗʸ-refl = ≅ⁿ-refl

≅ᵗʸ-sym : {S T : Ty Γ} → S ≅ᵗʸ T → T ≅ᵗʸ S
from (≅ᵗʸ-sym S=T) = to S=T
to (≅ᵗʸ-sym S=T) = from S=T
isoˡ (≅ᵗʸ-sym S=T) = isoʳ S=T
isoʳ (≅ᵗʸ-sym S=T) = isoˡ S=T

≅ᵗʸ-trans : {S T R : Ty Γ} → S ≅ᵗʸ T → T ≅ᵗʸ R → S ≅ᵗʸ R
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

module ≅ᵗʸ-Reasoning {Γ : Ctx C ℓ} where
  infix  3 _∎
  infixr 2 _≅⟨⟩_ step-≅ step-≅˘
  infix  1 begin_

  begin_ : ∀ {T S : Ty Γ} → T ≅ᵗʸ S → T ≅ᵗʸ S
  begin_ T=S = T=S

  _≅⟨⟩_ : ∀ (T {S} : Ty Γ) → T ≅ᵗʸ S → T ≅ᵗʸ S
  _ ≅⟨⟩ T=S = T=S

  step-≅ : ∀ (T {S R} : Ty Γ) → S ≅ᵗʸ R → T ≅ᵗʸ S → T ≅ᵗʸ R
  step-≅ _ S≅R T≅S = ≅ᵗʸ-trans T≅S S≅R

  step-≅˘ : ∀ (T {S R} : Ty Γ) → S ≅ᵗʸ R → S ≅ᵗʸ T → T ≅ᵗʸ R
  step-≅˘ _ S≅R S≅T = ≅ᵗʸ-trans (≅ᵗʸ-sym S≅T) S≅R

  _∎ : ∀ (T : Ty Γ) → T ≅ᵗʸ T
  _∎ _ = ≅ᵗʸ-refl

  syntax step-≅  T S≅R T≅S = T ≅⟨  T≅S ⟩ S≅R
  syntax step-≅˘ T S≅R S≅T = T ≅˘⟨ S≅T ⟩ S≅R


--------------------------------------------------
-- Substitution of types

_[_] : Ty Γ → Δ ⇒ Γ → Ty Δ
type (T [ σ ]) x δ = T ⟨ x , func σ δ ⟩
morph (_[_] {Γ = Γ} T σ) f {δy}{δx} eq-yx t = T ⟪ f , proof ⟫ t
  where
    proof : Γ ⟪ f ⟫ func σ δy ≡ func σ δx
    proof = trans (naturality σ δy) (cong (func σ) eq-yx)
morph-id (T [ σ ]) t = trans (cong (λ - → T ⟪ hom-id , - ⟫ t) (uip _ _))
                             (morph-id T t)
morph-comp (T [ σ ]) f g eq-zy eq-yx t = trans (cong (λ - → T ⟪ g ∙ f , - ⟫ t) (uip _ _))
                                               (morph-comp T f g _ _ t)

ty-subst-id : (T : Ty Γ) → T [ id-subst Γ ] ≅ᵗʸ T
from (ty-subst-id T) = record { func = id ; naturality = λ t → morph-cong T refl _ _ }
to (ty-subst-id T) = record { func = id ; naturality = λ t → morph-cong T refl _ _ }
isoˡ (ty-subst-id T) = record { eq = λ t → refl }
isoʳ (ty-subst-id T) = record { eq = λ t → refl }

ty-subst-comp : (T : Ty Θ) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → T [ τ ] [ σ ] ≅ᵗʸ T [ τ ⊚ σ ]
from (ty-subst-comp T τ σ) = record { func = id ; naturality = λ t → morph-cong T refl _ _ }
to (ty-subst-comp T τ σ) = record { func = id ; naturality = λ t → morph-cong T refl _ _ }
isoˡ (ty-subst-comp T τ σ) = record { eq = λ t → refl }
isoʳ (ty-subst-comp T τ σ) = record { eq = λ t → refl }

ty-subst-map : (σ : Δ ⇒ Γ) {T S : Ty Γ} → (T ↣ S) → T [ σ ] ↣ S [ σ ]
func (ty-subst-map σ η) t = func η t
naturality (ty-subst-map σ η) t = naturality η t

ty-subst-map-id : (σ : Δ ⇒ Γ) {T : Ty Γ} → ty-subst-map σ (id-trans T) ≅ⁿ id-trans (T [ σ ])
eq (ty-subst-map-id σ) t = refl

ty-subst-map-comp : (σ : Δ ⇒ Γ) {R S T : Ty Γ} (φ : S ↣ T) (η : R ↣ S) →
                    ty-subst-map σ (φ ⊙ η) ≅ⁿ ty-subst-map σ φ ⊙ ty-subst-map σ η
eq (ty-subst-map-comp σ φ η) t = refl

ty-subst-cong-ty : (σ : Δ ⇒ Γ) {T S : Ty Γ} → T ≅ᵗʸ S → T [ σ ] ≅ᵗʸ S [ σ ]
from (ty-subst-cong-ty σ T=S) = ty-subst-map σ (from T=S)
to (ty-subst-cong-ty σ T=S) = ty-subst-map σ (to T=S)
eq (isoˡ (ty-subst-cong-ty σ T=S)) t = eq (isoˡ T=S) t
eq (isoʳ (ty-subst-cong-ty σ T=S)) t = eq (isoʳ T=S) t

ty-subst-cong-subst : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → (T : Ty Γ) → T [ σ ] ≅ᵗʸ T [ τ ]
from (ty-subst-cong-subst σ=τ T) = record { func = λ {_ δ} t → ctx-element-subst T (eq σ=τ δ) t
                                          ; naturality = λ {_ _ f} t →
  begin
    T ⟪ f , _ ⟫ T ⟪ hom-id , _ ⟫ t
  ≡˘⟨ morph-comp T f hom-id _ _ t ⟩
    T ⟪ hom-id ∙ f , _ ⟫ t
  ≡⟨ morph-cong T (trans hom-idˡ (sym hom-idʳ)) _ _ ⟩
    T ⟪ f ∙ hom-id , _ ⟫ t
  ≡⟨ morph-comp T hom-id f _ _ t ⟩
    T ⟪ hom-id , _ ⟫ T ⟪ f , _ ⟫ t ∎ }
  where open ≡-Reasoning
to (ty-subst-cong-subst σ=τ T) = record { func = λ {_ δ} t → ctx-element-subst T (sym (eq σ=τ δ)) t
                                        ; naturality = λ {_ _ f} t →
  begin
    T ⟪ f , _ ⟫ T ⟪ hom-id , _ ⟫ t
  ≡˘⟨ morph-comp T f hom-id _ _ t ⟩
    T ⟪ hom-id ∙ f , _ ⟫ t
  ≡⟨ morph-cong T (trans hom-idˡ (sym hom-idʳ)) _ _ ⟩
    T ⟪ f ∙ hom-id , _ ⟫ t
  ≡⟨ morph-comp T hom-id f _ _ t ⟩
    T ⟪ hom-id , _ ⟫ T ⟪ f , _ ⟫ t ∎ }
  where open ≡-Reasoning
eq (isoˡ (ty-subst-cong-subst {Γ = Γ} σ=τ T)) t =
  -- Here we cannot use morph-id T twice because the omitted equality proofs are not rel-id Γ _
  -- (i.e. T ⟪_⟫ t is not applied to the identity morphism in the category of elements of Γ).
  begin
    T ⟪ hom-id , _ ⟫ T ⟪ hom-id , _ ⟫ t
  ≡˘⟨ morph-comp T hom-id hom-id _ _ t ⟩
    T ⟪ hom-id ∙ hom-id , _ ⟫ t
  ≡⟨ morph-cong T hom-idˡ _ _ ⟩
    T ⟪ hom-id , rel-id Γ _ ⟫ t
  ≡⟨ morph-id T t ⟩
    t ∎
  where open ≡-Reasoning
eq (isoʳ (ty-subst-cong-subst σ=τ T)) t =
  begin
    T ⟪ hom-id , _ ⟫ T ⟪ hom-id , _ ⟫ t
  ≡˘⟨ morph-comp T hom-id hom-id _ _ t ⟩
    T ⟪ hom-id ∙ hom-id , _ ⟫ t
  ≡⟨ morph-cong T hom-idˡ _ _ ⟩
    T ⟪ hom-id , _ ⟫ t
  ≡⟨ morph-id T t ⟩
    t ∎
  where open ≡-Reasoning
