--------------------------------------------------
-- An example of representation independence using
-- unary parametricity
--------------------------------------------------

module Applications.UnaryParametricity.Model where

open import Data.Empty
open import Data.Nat
open import Data.Product renaming (_,_ to [_,_])
open import Data.Product.Properties
open import Data.Sum hiding ([_,_])
open import Data.Unit
open import Function using (id)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Unary hiding (_⇒_)

open import Preliminaries
open import Model.BaseCategory
open BaseCategory
open import Model.CwF-Structure
open import Model.Type.Function
open import Model.Type.Product
open import Model.DRA

open import Experimental.DependentTypes.Model.Function as Π using (Pi)

private
  variable
    Γ : Ctx ↑


--------------------------------------------------
-- Constructing an embedded type in base category ↑
-- using an Agda type and a predicate

PrimFromPred : (A : Set) → Pred A 0ℓ → Ty {C = ↑} ◇
PrimFromPred A P ⟨ type-obj , _ ⟩ = A
PrimFromPred A P ⟨ pred-obj , _ ⟩ = Σ[ a ∈ A ] P a
PrimFromPred A P ⟪ type-id , _ ⟫ a = a
PrimFromPred A P ⟪ pred-id , _ ⟫ x = x
PrimFromPred A P ⟪ type-pred , _ ⟫ [ a , p ] = a
ty-cong (PrimFromPred A P) refl {eγ = refl} {eγ' = refl} = refl
ty-id (PrimFromPred A P) {x = type-obj} = refl
ty-id (PrimFromPred A P) {x = pred-obj} = refl
ty-comp (PrimFromPred A P) {f = type-id} {eγ-zy = refl} {eγ-yx = refl} = refl
ty-comp (PrimFromPred A P) {f = pred-id} {eγ-zy = refl} {eγ-yx = refl} = refl
ty-comp (PrimFromPred A P) {f = type-pred} {g = pred-id} = refl

FromPred : (A : Set) → Pred A 0ℓ → ClosedTy ↑
FromPred A P {Γ = Γ} = PrimFromPred A P [ !◇ Γ ]

frompred-natural : {A : Set} {P : Pred A 0ℓ} → IsClosedNatural (FromPred A P)
closed-natural (frompred-natural {A} {P}) σ = ty-subst-cong-subst-2-1 (PrimFromPred A P) (◇-terminal _ _ _)
eq (from-eq (closed-id (frompred-natural {A} {P}))) {x = x} t = ty-id (PrimFromPred A P) {x = x}
eq (from-eq (closed-⊚ frompred-natural σ τ)) {x = type-obj} t = refl
eq (from-eq (closed-⊚ frompred-natural σ τ)) {x = pred-obj} t = refl
eq (from-eq (closed-subst-eq frompred-natural ε)) {x = type-obj} t = refl
eq (from-eq (closed-subst-eq frompred-natural ε)) {x = pred-obj} t = refl

from-pred : {A : Set} {P : Pred A 0ℓ} (a : A) → P a → Tm Γ (FromPred A P)
from-pred a p ⟨ type-obj , _ ⟩' = a
from-pred a p ⟨ pred-obj , _ ⟩' = [ a , p ]
Tm.naturality (from-pred a p) type-id _ = refl
Tm.naturality (from-pred a p) pred-id _ = refl
Tm.naturality (from-pred a p) type-pred _ = refl

from-pred1 : {A B : Set} {P : Pred A 0ℓ} {Q : Pred B 0ℓ}
             (f : A → B) → (P ⟨→⟩ Q) f →
             Tm (Γ ,, FromPred A P) (FromPred B Q)
from-pred1 f g ⟨ type-obj , [ _ , a ] ⟩' = f a
from-pred1 f g ⟨ pred-obj , [ _ , [ a , p ] ] ⟩' = [ f a , g p ]
Tm.naturality (from-pred1 f g) type-id refl = refl
Tm.naturality (from-pred1 f g) pred-id refl = refl
Tm.naturality (from-pred1 f g) type-pred refl = refl

from-pred2 : {A : Set} {P : Pred A 0ℓ}
             {B : Set} {Q : Pred B 0ℓ}
             {C : Set} {R : Pred C 0ℓ}
             (f : A → B → C) → (P ⟨→⟩ Q ⟨→⟩ R) f →
             Tm (Γ ,, FromPred A P ,, FromPred B Q) (FromPred C R)
from-pred2 f g ⟨ type-obj , [ [ _ , a ] , b ] ⟩' = f a b
from-pred2 f g ⟨ pred-obj , [ [ _ , [ a , p ] ] , [ b , q ] ] ⟩' = [ f a b , g p q ]
Tm.naturality (from-pred2 f g) type-id refl = refl
Tm.naturality (from-pred2 f g) pred-id refl = refl
Tm.naturality (from-pred2 f g) type-pred refl = refl

from-pred-tm-natural : {A : Set} {P : Pred A 0ℓ} {a : A} {p : P a}
                       {Γ Δ : Ctx ↑} (σ : Γ ⇒ Δ) →
                       (from-pred a p [ frompred-natural {P = P} ∣ σ ]cl) ≅ᵗᵐ from-pred a p
eq (from-pred-tm-natural σ) {x = type-obj} γ = refl
eq (from-pred-tm-natural σ) {x = pred-obj} γ = refl

from-pred1-tm-natural : {A B : Set} {P : Pred A 0ℓ} {Q : Pred B 0ℓ}
                        (f : A → B) (pres-f : (P ⟨→⟩ Q) f)
                        {Γ Δ : Ctx ↑} (σ : Γ ⇒ Δ) →
                        lamcl (frompred-natural {P = Q}) (from-pred1 f pres-f)
                              [ fun-closed (frompred-natural {P = P}) (frompred-natural {P = Q}) ∣ σ ]cl
                          ≅ᵗᵐ
                        lamcl (frompred-natural {P = Q}) (from-pred1 f pres-f)
eq (from-pred1-tm-natural f pres-f σ) γ = to-pshfun-eq λ
  { type-id eγ t → refl
  ; pred-id eγ t → refl
  ; type-pred eγ t → refl }

from-pred2-tm-natural : {A : Set} {P : Pred A 0ℓ}
                        {B : Set} {Q : Pred B 0ℓ}
                        {C : Set} {R : Pred C 0ℓ}
                        (f : A → B → C) (pres-f : (P ⟨→⟩ Q ⟨→⟩ R) f)
                        {Γ Δ : Ctx ↑} (σ : Γ ⇒ Δ) →
                        lamcl (fun-closed (frompred-natural {P = Q}) (frompred-natural {P = R})) (lamcl (frompred-natural {P = R}) (from-pred2 f pres-f))
                             [ fun-closed (frompred-natural {P = P}) (fun-closed (frompred-natural {P = Q}) (frompred-natural {P = R})) ∣ σ ]cl
                          ≅ᵗᵐ
                        lamcl (fun-closed (frompred-natural {P = Q}) (frompred-natural {P = R})) (lamcl (frompred-natural {P = R}) (from-pred2 f pres-f))
eq (from-pred2-tm-natural f pres-f σ) γ = to-pshfun-eq λ
  { type-id eγ t → to-pshfun-eq (λ { type-id eγ' t' → refl })
  ; pred-id eγ t → to-pshfun-eq (λ { pred-id eγ' t' → refl ; type-pred eγ' t' → refl })
  ; type-pred eγ t → to-pshfun-eq (λ { type-id eγ' t' → refl }) }


--------------------------------------------------
-- Definition of two DRAs from ↑ to ★

always-false : Ctx ★ → Ctx ↑
always-false Γ ⟨ type-obj ⟩ = Γ ⟨ tt ⟩
always-false Γ ⟨ pred-obj ⟩ = ⊥
always-false Γ ⟪ type-id ⟫ γ = γ
always-false Γ ⟪ pred-id ⟫ x = x
always-false Γ ⟪ type-pred ⟫ x = ⊥-elim x
ctx-id (always-false Γ) {x = type-obj} = refl
ctx-comp (always-false Γ) {f = type-id} = refl
ctx-comp (always-false Γ) {f = pred-id} = refl
ctx-comp (always-false Γ) {f = type-pred} {g = pred-id} = refl

always-false-subst : {Δ Γ : Ctx ★} → Δ ⇒ Γ → always-false Δ ⇒ always-false Γ
func (always-false-subst σ) {x = type-obj} = func σ
func (always-false-subst σ) {x = pred-obj} = ⊥-elim
_⇒_.naturality (always-false-subst σ) {f = type-id} = refl

always-false-subst-cong : {Δ Γ : Ctx ★} {σ τ : Δ ⇒ Γ} →
                          σ ≅ˢ τ → always-false-subst σ ≅ˢ always-false-subst τ
eq (always-false-subst-cong σ=τ) {x = type-obj} δ = eq σ=τ δ

always-false-subst-id : {Γ : Ctx ★} → always-false-subst (id-subst Γ) ≅ˢ id-subst (always-false Γ)
eq always-false-subst-id {x = type-obj} _ = refl

always-false-subst-⊚ : {Δ Γ Θ : Ctx ★} (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) →
                       always-false-subst (σ ⊚ τ) ≅ˢ always-false-subst σ ⊚ always-false-subst τ
eq (always-false-subst-⊚ σ τ) {x = type-obj} _ = refl

forget-pred : {Γ : Ctx ★} → Ty (always-false Γ) → Ty Γ
forget-pred T ⟨ tt , γ ⟩ = T ⟨ type-obj , γ ⟩
forget-pred {Γ = Γ} T ⟪ tt , eγ ⟫ t = T ⟪ type-id , trans (sym (ctx-id Γ)) eγ ⟫ t
ty-cong (forget-pred T) refl {eγ = refl} {eγ' = refl} = refl
ty-id (forget-pred T) = strong-ty-id T
ty-comp (forget-pred T) = strong-ty-comp T

module _ {Γ : Ctx ★} {T : Ty (always-false Γ)} where
  forget-intro : Tm (always-false Γ) T → Tm Γ (forget-pred T)
  forget-intro t ⟨ tt , γ ⟩' = t ⟨ type-obj , γ ⟩'
  Tm.naturality (forget-intro t) tt _ = Tm.naturality t type-id _

  forget-elim : Tm Γ (forget-pred T) → Tm (always-false Γ) T
  forget-elim t ⟨ type-obj , γ ⟩' = t ⟨ tt , γ ⟩'
  Tm.naturality (forget-elim t) type-id eγ = trans (ty-cong T refl) (Tm.naturality t tt (trans (ctx-id Γ) eγ))

module _ {Δ : Ctx ★} {Γ : Ctx ★} (σ : Δ ⇒ Γ) {T : Ty (always-false Γ)} where
  forget-natural : (forget-pred T) [ σ ] ≅ᵗʸ forget-pred (T [ always-false-subst σ ])
  func (from forget-natural) = id
  _↣_.naturality (from forget-natural) = ty-cong T refl
  func (to forget-natural) = id
  _↣_.naturality (to forget-natural) = ty-cong T refl
  eq (isoˡ forget-natural) _ = refl
  eq (isoʳ forget-natural) _ = refl

  forget-intro-natural : (t : Tm (always-false Γ) T) →
                         forget-intro t [ σ ]' ≅ᵗᵐ ι[ forget-natural ] forget-intro (t [ always-false-subst σ ]')
  eq (forget-intro-natural t) _ = refl

  forget-elim-natural : (t : Tm Γ (forget-pred T)) →
                        forget-elim t [ always-false-subst σ ]' ≅ᵗᵐ forget-elim (ι⁻¹[ forget-natural ] (t [ σ ]'))
  eq (forget-elim-natural t) {x = type-obj} _ = refl

forget-map : {Γ : Ctx ★} {T : Ty (always-false Γ)} {T' : Ty (always-false Γ)} →
             T ↣ T' → forget-pred T ↣ forget-pred T'
func (forget-map φ) = func φ
_↣_.naturality (forget-map φ) = _↣_.naturality φ

forget-map-cong : {Γ : Ctx ★} {T T' : Ty (always-false Γ)} {φ η : T ↣ T'} →
                  φ ≅ⁿ η → forget-map φ ≅ⁿ forget-map η
eq (forget-map-cong 𝔢) = eq 𝔢

forget-map-id : {Γ : Ctx ★} {T : Ty (always-false Γ)} →
                forget-map (id-trans T) ≅ⁿ id-trans (forget-pred T)
eq forget-map-id _ = refl

forget-map-⊙ : {Γ : Ctx ★} {T T' T'' : Ty (always-false Γ)}
               {φ : T' ↣ T''} {η : T ↣ T'} →
               forget-map (φ ⊙ η) ≅ⁿ forget-map φ ⊙ forget-map η
eq forget-map-⊙ _ = refl

forget-natural-map : {Γ Δ : Ctx ★} (σ : Γ ⇒ Δ) {T S : Ty (always-false Δ)} (η : T ↣ S) →
                     forget-map (ty-subst-map (always-false-subst σ) η)
                     ⊙ from (forget-natural σ)
                       ≅ⁿ
                     from (forget-natural σ) ⊙ ty-subst-map σ (forget-map η)
eq (forget-natural-map σ η) _ = refl

forget-natural-id-map : {Γ : Ctx ★} {T : Ty (always-false Γ)} →
                        forget-map (ty-subst-id-from T ⊙ ty-subst-eq-subst-morph always-false-subst-id T)
                        ⊙ from (forget-natural (id-subst Γ))
                          ≅ⁿ
                        ty-subst-id-from (forget-pred T)
eq (forget-natural-id-map {T = T}) _ = ty-id T

forget-natural-⊚-map : {Γ Δ Θ : Ctx ★} (τ : Δ ⇒ Θ) (σ : Γ ⇒ Δ) {T : Ty (always-false Θ)} →
                       forget-map (ty-subst-comp-from T (always-false-subst τ) (always-false-subst σ))
                       ⊙ from (forget-natural σ)
                       ⊙ ty-subst-map σ (from (forget-natural τ))
                         ≅ⁿ
                       forget-map (ty-subst-eq-subst-morph (always-false-subst-⊚ τ σ) T)
                       ⊙ from (forget-natural (τ ⊚ σ))
                       ⊙ ty-subst-comp-from (forget-pred T) τ σ
eq (forget-natural-⊚-map τ σ {T}) _ = sym (ty-id T)

forget-natural-subst-eq-map : {Γ Δ : Ctx ★} {T : Ty (always-false Δ)} {σ τ : Γ ⇒ Δ} (ε : σ ≅ˢ τ) →
                              from (forget-natural τ)
                              ⊙ ty-subst-eq-subst-morph ε (forget-pred T)
                                ≅ⁿ
                              forget-map (ty-subst-eq-subst-morph (always-false-subst-cong ε) T)
                              ⊙ from (forget-natural σ)
eq (forget-natural-subst-eq-map {T = T} ε) _ = ty-cong T refl

module _ {Γ : Ctx ★} {T : Ty (always-false Γ)} where
  forget-intro-cong : {t t' : Tm (always-false Γ) T} → t ≅ᵗᵐ t' → forget-intro t ≅ᵗᵐ forget-intro t'
  eq (forget-intro-cong t=t') γ = eq t=t' γ

  forget-elim-cong : {t t' : Tm Γ (forget-pred T)} → t ≅ᵗᵐ t' → forget-elim t ≅ᵗᵐ forget-elim t'
  eq (forget-elim-cong t=t') {x = type-obj} γ = eq t=t' γ

  forget-β : (t : Tm (always-false Γ) T) → forget-elim (forget-intro t) ≅ᵗᵐ t
  eq (forget-β t) {x = type-obj} _ = refl

  forget-η : (t : Tm Γ (forget-pred T)) → forget-intro (forget-elim t) ≅ᵗᵐ t
  eq (forget-η t) _ = refl

forget-intro-convert : {Γ : Ctx ★} {T T' : Ty (always-false Γ)} {η : T ↣ T'}
                       (t : Tm (always-false Γ) T) →
                       convert-tm (forget-map η) (forget-intro t)
                         ≅ᵗᵐ
                       forget-intro (convert-tm η t)
eq (forget-intro-convert t) _ = refl

always-false-is-functor : IsCtxFunctor always-false
ctx-map {{always-false-is-functor}} = always-false-subst
ctx-map-cong {{always-false-is-functor}} = always-false-subst-cong
ctx-map-id {{always-false-is-functor}} = always-false-subst-id
ctx-map-⊚ {{always-false-is-functor}} = always-false-subst-⊚

always-false-functor : CtxFunctor ★ ↑
ctx-op always-false-functor = always-false
is-functor always-false-functor = always-false-is-functor

forget-dra : DRA ↑ ★
ctx-functor forget-dra = always-false-functor
⟨_∣_⟩ forget-dra = forget-pred
dra-map forget-dra = forget-map
dra-map-cong forget-dra = forget-map-cong
dra-map-id forget-dra = forget-map-id
dra-map-⊙ forget-dra = forget-map-⊙
dra-natural forget-dra = forget-natural
dra-natural-map forget-dra = forget-natural-map
dra-natural-id-map forget-dra = forget-natural-id-map
dra-natural-⊚-map forget-dra = forget-natural-⊚-map
dra-natural-subst-eq-map forget-dra = forget-natural-subst-eq-map
dra-intro forget-dra = forget-intro
dra-intro-cong forget-dra = forget-intro-cong
dra-intro-natural forget-dra = forget-intro-natural
dra-intro-convert forget-dra = forget-intro-convert
dra-elim forget-dra = forget-elim
dra-elim-cong forget-dra = forget-elim-cong
dra-β forget-dra = forget-β
dra-η forget-dra = forget-η


always-true : Ctx ★ → Ctx ↑
always-true Γ ⟨ x ⟩ = Γ ⟨ tt ⟩
always-true Γ ⟪ f ⟫ γ = γ
ctx-id (always-true Γ) = refl
ctx-comp (always-true Γ) = refl

always-true-subst : {Δ Γ : Ctx ★} → Δ ⇒ Γ → always-true Δ ⇒ always-true Γ
func (always-true-subst σ) = func σ
_⇒_.naturality (always-true-subst σ) = refl

always-true-subst-cong : {Δ Γ : Ctx ★} {σ τ : Δ ⇒ Γ} →
                          σ ≅ˢ τ → always-true-subst σ ≅ˢ always-true-subst τ
eq (always-true-subst-cong σ=τ) δ = eq σ=τ δ

always-true-subst-id : {Γ : Ctx ★} → always-true-subst (id-subst Γ) ≅ˢ id-subst (always-true Γ)
eq always-true-subst-id _ = refl

always-true-subst-⊚ : {Δ Γ Θ : Ctx ★} (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) →
                       always-true-subst (σ ⊚ τ) ≅ˢ always-true-subst σ ⊚ always-true-subst τ
eq (always-true-subst-⊚ σ τ) _ = refl

Σ-ty : {Γ : Ctx ★} → Ty (always-true Γ) → Ty Γ
Σ-ty T ⟨ tt , γ ⟩ = T ⟨ pred-obj , γ ⟩
Σ-ty {Γ = Γ} T ⟪ tt , eγ ⟫ t = T ⟪ pred-id , trans (sym (ctx-id Γ)) eγ ⟫ t
ty-cong (Σ-ty T) refl {eγ = refl} {eγ' = refl} = refl
ty-id (Σ-ty T) = strong-ty-id T
ty-comp (Σ-ty T) = strong-ty-comp T

module _ {Γ : Ctx ★} {T : Ty (always-true Γ)} where
  Σ-intro : Tm (always-true Γ) T → Tm Γ (Σ-ty T)
  Σ-intro t ⟨ tt , γ ⟩' = t ⟨ pred-obj , γ ⟩'
  Tm.naturality (Σ-intro t) tt _ = Tm.naturality t pred-id _

  Σ-elim : Tm Γ (Σ-ty T) → Tm (always-true Γ) T
  Σ-elim t ⟨ type-obj , γ ⟩' = T ⟪ type-pred , refl ⟫ t ⟨ tt , _ ⟩'
  Σ-elim t ⟨ pred-obj , γ ⟩' = t ⟨ tt , γ ⟩'
  Tm.naturality (Σ-elim t) type-id eγ = trans (ty-cong-2-2 T refl) (cong (T ⟪ _ , _ ⟫_) (Tm.naturality t tt (trans (ctx-id Γ) eγ)))
  Tm.naturality (Σ-elim t) pred-id eγ = trans (ty-cong T refl) (Tm.naturality t tt (trans (ctx-id Γ) eγ))
  Tm.naturality (Σ-elim t) type-pred eγ = trans (sym (ty-cong-2-1 T refl)) (cong (T ⟪ _ , _ ⟫_) (Tm.naturality t tt (trans (ctx-id Γ) eγ)))

module _ {Δ : Ctx ★} {Γ : Ctx ★} (σ : Δ ⇒ Γ) {T : Ty (always-true Γ)} where
  Σ-natural : (Σ-ty T) [ σ ] ≅ᵗʸ Σ-ty (T [ always-true-subst σ ])
  func (from Σ-natural) = id
  _↣_.naturality (from Σ-natural) = ty-cong T refl
  func (to Σ-natural) = id
  _↣_.naturality (to Σ-natural) = ty-cong T refl
  eq (isoˡ Σ-natural) _ = refl
  eq (isoʳ Σ-natural) _ = refl

  Σ-intro-natural : (t : Tm (always-true Γ) T) →
                    Σ-intro t [ σ ]' ≅ᵗᵐ ι[ Σ-natural ] Σ-intro (t [ always-true-subst σ ]')
  eq (Σ-intro-natural t) _ = refl

  Σ-elim-natural : (t : Tm Γ (Σ-ty T)) →
                   Σ-elim t [ always-true-subst σ ]' ≅ᵗᵐ Σ-elim (ι⁻¹[ Σ-natural ] (t [ σ ]'))
  eq (Σ-elim-natural t) {x = type-obj} _ = refl
  eq (Σ-elim-natural t) {x = pred-obj} _ = refl

Σ-map : {Γ : Ctx ★} {T : Ty (always-true Γ)} {T' : Ty (always-true Γ)} →
        T ↣ T' → Σ-ty T ↣ Σ-ty T'
func (Σ-map φ) = func φ
_↣_.naturality (Σ-map φ) = _↣_.naturality φ

Σ-map-cong : {Γ : Ctx ★} {T T' : Ty (always-true Γ)} {φ η : T ↣ T'} →
             φ ≅ⁿ η → Σ-map φ ≅ⁿ Σ-map η
eq (Σ-map-cong 𝔢) = eq 𝔢

Σ-map-id : {Γ : Ctx ★} {T : Ty (always-true Γ)} →
           Σ-map (id-trans T) ≅ⁿ id-trans (Σ-ty T)
eq Σ-map-id _ = refl

Σ-map-⊙ : {Γ : Ctx ★} {T T' T'' : Ty (always-true Γ)}
          {φ : T' ↣ T''} {η : T ↣ T'} →
          Σ-map (φ ⊙ η) ≅ⁿ Σ-map φ ⊙ Σ-map η
eq Σ-map-⊙ _ = refl

Σ-natural-map : {Γ Δ : Ctx ★} (σ : Γ ⇒ Δ) {T S : Ty (always-true Δ)} (η : T ↣ S) →
                Σ-map (ty-subst-map (always-true-subst σ) η)
                ⊙ from (Σ-natural σ)
                  ≅ⁿ
                from (Σ-natural σ) ⊙ ty-subst-map σ (Σ-map η)
eq (Σ-natural-map σ η) _ = refl

Σ-natural-id-map : {Γ : Ctx ★} {T : Ty (always-true Γ)} →
                   Σ-map (ty-subst-id-from T ⊙ ty-subst-eq-subst-morph always-true-subst-id T)
                   ⊙ from (Σ-natural (id-subst Γ))
                     ≅ⁿ
                   ty-subst-id-from (Σ-ty T)
eq (Σ-natural-id-map {T = T}) _ = ty-id T

Σ-natural-⊚-map : {Γ Δ Θ : Ctx ★} (τ : Δ ⇒ Θ) (σ : Γ ⇒ Δ) {T : Ty (always-true Θ)} →
                  Σ-map (ty-subst-comp-from T (always-true-subst τ) (always-true-subst σ))
                  ⊙ from (Σ-natural σ)
                  ⊙ ty-subst-map σ (from (Σ-natural τ))
                    ≅ⁿ
                  Σ-map (ty-subst-eq-subst-morph (always-true-subst-⊚ τ σ) T)
                  ⊙ from (Σ-natural (τ ⊚ σ))
                  ⊙ ty-subst-comp-from (Σ-ty T) τ σ
eq (Σ-natural-⊚-map τ σ {T}) _ = sym (ty-id T)

Σ-natural-subst-eq-map : {Γ Δ : Ctx ★} {T : Ty (always-true Δ)} {σ τ : Γ ⇒ Δ} (ε : σ ≅ˢ τ) →
                         from (Σ-natural τ)
                         ⊙ ty-subst-eq-subst-morph ε (Σ-ty T)
                           ≅ⁿ
                         Σ-map (ty-subst-eq-subst-morph (always-true-subst-cong ε) T)
                         ⊙ from (Σ-natural σ)
eq (Σ-natural-subst-eq-map {T = T} ε) _ = ty-cong T refl

module _ {Γ : Ctx ★} {T : Ty (always-true Γ)} where
  Σ-intro-cong : {t t' : Tm (always-true Γ) T} → t ≅ᵗᵐ t' → Σ-intro t ≅ᵗᵐ Σ-intro t'
  eq (Σ-intro-cong t=t') γ = eq t=t' γ

  Σ-elim-cong : {t t' : Tm Γ (Σ-ty T)} → t ≅ᵗᵐ t' → Σ-elim t ≅ᵗᵐ Σ-elim t'
  eq (Σ-elim-cong t=t') {x = type-obj} γ = cong (T ⟪ _ , _ ⟫_) (eq t=t' γ)
  eq (Σ-elim-cong t=t') {x = pred-obj} γ = eq t=t' γ 

  Σ-β : (t : Tm (always-true Γ) T) → Σ-elim (Σ-intro t) ≅ᵗᵐ t
  eq (Σ-β t) {x = type-obj} _ = Tm.naturality t type-pred refl
  eq (Σ-β t) {x = pred-obj} _ = refl

  Σ-η : (t : Tm Γ (Σ-ty T)) → Σ-intro (Σ-elim t) ≅ᵗᵐ t
  eq (Σ-η t) _ = refl

Σ-intro-convert : {Γ : Ctx ★} {T T' : Ty (always-true Γ)} {η : T ↣ T'}
                  (t : Tm (always-true Γ) T) →
                  convert-tm (Σ-map η) (Σ-intro t)
                    ≅ᵗᵐ
                  Σ-intro (convert-tm η t)
eq (Σ-intro-convert t) _ = refl

always-true-is-functor : IsCtxFunctor always-true
ctx-map {{always-true-is-functor}} = always-true-subst
ctx-map-cong {{always-true-is-functor}} = always-true-subst-cong
ctx-map-id {{always-true-is-functor}} = always-true-subst-id
ctx-map-⊚ {{always-true-is-functor}} = always-true-subst-⊚

always-true-functor : CtxFunctor ★ ↑
ctx-op always-true-functor = always-true
is-functor always-true-functor = always-true-is-functor

Σ-dra : DRA ↑ ★
ctx-functor Σ-dra = always-true-functor
⟨_∣_⟩ Σ-dra = Σ-ty
dra-map Σ-dra = Σ-map
dra-map-cong Σ-dra = Σ-map-cong
dra-map-id Σ-dra = Σ-map-id
dra-map-⊙ Σ-dra = Σ-map-⊙
dra-natural Σ-dra = Σ-natural
dra-natural-map Σ-dra = Σ-natural-map
dra-natural-id-map Σ-dra = Σ-natural-id-map
dra-natural-⊚-map Σ-dra = Σ-natural-⊚-map
dra-natural-subst-eq-map Σ-dra = Σ-natural-subst-eq-map
dra-intro Σ-dra = Σ-intro
dra-intro-cong Σ-dra = Σ-intro-cong
dra-intro-natural Σ-dra = Σ-intro-natural
dra-intro-convert Σ-dra = Σ-intro-convert
dra-elim Σ-dra = Σ-elim
dra-elim-cong Σ-dra = Σ-elim-cong
dra-β Σ-dra = Σ-β
dra-η Σ-dra = Σ-η

π-cell : TwoCell Σ-dra forget-dra
func (transf-op (transf π-cell) Γ) {x = type-obj} = id
func (transf-op (transf π-cell) Γ) {x = pred-obj} = ⊥-elim
_⇒_.naturality (transf-op (transf π-cell) Γ) {f = type-id} = refl
eq (CtxNatTransf.naturality (transf π-cell) σ) {x = type-obj} γ = refl


--------------------------------------------------
-- Expressing the predicate of a type over base category ↑ as a semantic type,
-- i.e. we get a predicate on terms of type `forget-pred A`, not
-- expressed as an Agda type, but as a type in the model.

semPred : {A : ClosedTy ↑} (clA : IsClosedNatural A) →
          {Γ : Ctx ★} →
          Tm Γ (forget-pred A) →
          Ty Γ
semPred {A = A} clA {Γ} t ⟨ x , γ ⟩ =
  Σ[ pf ∈ A {always-true Γ} ⟨ pred-obj , γ ⟩ ] func (from (closed-natural clA (key-subst π-cell))) (A {always-true Γ} ⟪ type-pred , refl ⟫ pf) ≡ t ⟨ tt , γ ⟩'
semPred {A = A} clA {Γ} t ⟪ tt , eγ ⟫ [ pf , e ] =
  [ A ⟪ pred-id , trans (sym (ctx-id Γ)) eγ ⟫ pf
  , trans (cong (func (from (closed-natural clA (key-subst π-cell)))) (ty-cong-2-2 A refl)) (
    trans (sym (_↣_.naturality (from (closed-natural clA (key-subst π-cell))))) (
    trans (cong (A ⟪ type-id , _ ⟫_) e) (
    Tm.naturality t tt eγ)))
  ]
ty-cong (semPred {A = A} clA t) e = Σ-≡,≡→≡ [ ty-cong A refl , uip _ _ ]
ty-id (semPred {A = A} clA t) = Σ-≡,≡→≡ [ strong-ty-id A , uip _ _ ]
ty-comp (semPred {A = A} clA t) = Σ-≡,≡→≡ [ strong-ty-comp A , uip _ _ ]

semPred-natural : {A : ClosedTy ↑} (clA : IsClosedNatural A) →
                  {Γ Δ : Ctx ★} (σ : Γ ⇒ Δ) →
                  (t : Tm Δ (forget-pred A)) →
                  semPred clA t [ σ ] ≅ᵗʸ semPred clA (t [ dra-closed forget-dra clA ∣ σ ]cl)
func (from (semPred-natural {A = A} clA σ t)) [ pf , e ] =
  [ func (from (closed-natural clA (always-true-subst σ))) pf
  , trans (cong (func (from (closed-natural clA (key-subst π-cell)))) (_↣_.naturality (from (closed-natural clA (always-true-subst σ))))) (
    trans (trans (eq (from-eq (closed-⊚ clA _ _)) _) (
           trans (sym (eq (from-eq (closed-subst-eq clA (symˢ (key-subst-natural π-cell)))) _)) (
           trans (sym (eq (from-eq (closed-⊚ clA _ _)) _)) (
           cong (func (from (closed-natural clA _))) (cong (func (from (closed-natural clA _))) (ty-cong-2-1 A refl)))))) (
    cong (func (from (closed-natural clA (always-false-subst σ)))) e)) ]
_↣_.naturality (from (semPred-natural {A = A} clA σ t)) {t = [ pf , _ ]} = Σ-≡,≡→≡
  [ trans (_↣_.naturality (from (closed-natural clA (always-true-subst σ)))) (cong (func (from (closed-natural clA _))) (ty-cong A refl)) , uip _ _ ]
func (to (semPred-natural {A = A} clA σ t)) [ pf , e ] =
  [ func (to (closed-natural clA (always-true-subst σ))) pf
  , trans (cong (func (from (closed-natural clA _))) (_↣_.naturality (to (closed-natural clA (always-true-subst σ))))) (
    trans (sym (eq (isoˡ (closed-natural clA (always-false-subst σ))) _)) (
    trans (cong (func (to (closed-natural clA _))) (
                trans (eq (from-eq (closed-⊚ clA _ _)) _) (
                trans (sym (eq (from-eq (closed-subst-eq clA (key-subst-natural π-cell))) _)) (
                sym (eq (from-eq (closed-⊚ clA _ _)) _))))) (
    trans (cong (func (to (closed-natural clA _))) (
      trans (cong (func (from (closed-natural clA _))) (
        trans (cong (func (from (closed-natural clA _))) (_↣_.naturality (to (closed-natural clA _)))) (eq (isoʳ (closed-natural clA _)) _))) (
      trans (cong (func (from (closed-natural clA _))) (ty-cong-2-1 A refl)) e))) (
    eq (isoˡ (closed-natural clA _)) _))))
  ]
_↣_.naturality (to (semPred-natural {A = A} clA σ t)) {t = [ pf , _ ]} = Σ-≡,≡→≡
  [ trans (ty-cong A refl) (_↣_.naturality (to (closed-natural clA (always-true-subst σ)))) , uip _ _ ]
eq (isoˡ (semPred-natural clA σ t)) _ = Σ-≡,≡→≡ [ eq (isoˡ (closed-natural clA _)) _ , uip _ _ ]
eq (isoʳ (semPred-natural clA σ t)) _ = Σ-≡,≡→≡ [ eq (isoʳ (closed-natural clA _)) _ , uip _ _ ]

semPred-cong : {A : ClosedTy ↑} (clA : IsClosedNatural A) →
               {Γ : Ctx ★} →
               {t1 t2 : Tm Γ (forget-pred A)} →
               t1 ≅ᵗᵐ t2 →
               semPred clA t1 ≅ᵗʸ semPred clA t2
func (from (semPred-cong clA 𝒆)) [ pf , e ] = [ pf , trans e (eq 𝒆 _) ]
_↣_.naturality (from (semPred-cong clA 𝒆)) = Σ-≡,≡→≡ [ refl , (uip _ _) ]
func (to (semPred-cong clA 𝒆)) [ pf , e ] = [ pf , trans e (sym (eq 𝒆 _)) ]
_↣_.naturality (to (semPred-cong clA 𝒆)) = Σ-≡,≡→≡ [ refl , uip _ _ ]
eq (isoˡ (semPred-cong clA 𝒆)) _ = Σ-≡,≡→≡ [ refl , uip _ _ ]
eq (isoʳ (semPred-cong clA 𝒆)) _ = Σ-≡,≡→≡ [ refl , uip _ _ ]

semPred-congᶜⁿ : {A : ClosedTy ↑} {clA clA' : IsClosedNatural A} (e : clA ≅ᶜⁿ clA') →
                 {Γ : Ctx ★} →
                 (t : Tm Γ (forget-pred A)) →
                 semPred clA t ≅ᵗʸ semPred clA' t
func (from (semPred-congᶜⁿ eclA t)) [ pf , e ] = [ pf , trans (sym (eq (from-eq (closed-natural-eq eclA _)) _)) e ]
_↣_.naturality (from (semPred-congᶜⁿ eclA t)) = Σ-≡,≡→≡ [ refl , (uip _ _) ]
func (to (semPred-congᶜⁿ eclA t)) [ pf , e ] = [ pf , trans (eq (from-eq (closed-natural-eq eclA _)) _) e ]
_↣_.naturality (to (semPred-congᶜⁿ eclA t)) = Σ-≡,≡→≡ [ refl , (uip _ _) ]
eq (isoˡ (semPred-congᶜⁿ eclA t)) _ = Σ-≡,≡→≡ [ refl , (uip _ _) ]
eq (isoʳ (semPred-congᶜⁿ eclA t)) _ = Σ-≡,≡→≡ [ refl , (uip _ _) ]


--------------------------------------------------
-- Semantic evidence for the axioms

-- The following is used in the soundness proof for the param primitive, stating that
--   ∀[ Σ ∣ "a" ∈ A ] bPred A (mod⟨ forget ⟩ var "a" π-cell)
param-sem : {A : ClosedTy ↑} (clA : IsClosedNatural A) →
            {Γ : Ctx ★} →
            Tm Γ (Pi (Σ-ty A) (semPred clA (forget-intro (Σ-elim (ξcl (dra-closed Σ-dra clA)) [ clA ∣ key-subst π-cell ]cl))))
param-sem {A = A} clA = Π.lam _ tm
  where
    tm : Tm _ _
    tm ⟨ x , [ γ , a ] ⟩' = [ func (from (closed-natural clA (always-true-subst π))) a , refl ]
    Tm.naturality tm tt refl = Σ-≡,≡→≡
      [ trans (_↣_.naturality (from (closed-natural clA _))) (cong (func (from (closed-natural clA _))) (ty-cong A refl))
      , uip _ _
      ]

-- The following is used in the soundness proof for the extent-from primitive, stating that
-- if we have evidence for bPred (A ⇛ B) f, then
--   ∀[ forget ∣ "a" ∈ A ] bPred A (mod⟨ forget ⟩ svar "a")
--                         ⊃ bPred B (let' mod⟨ forget ⟩ "f" ← f [ πʳ ]tmʳ in' mod⟨ forget ⟩ (svar "f" ∙ svar "a"))
extent-from-sem : {A B : ClosedTy ↑} (clA : IsClosedNatural A) (clB : IsClosedNatural B) →
                  {Γ : Ctx ★} →
                  (f : Tm Γ (forget-pred (A ⇛ B))) →
                  Tm Γ (semPred (fun-closed clA clB) f) →
                  Tm Γ (Pi (forget-pred A)
                         (semPred clA (ξcl (dra-closed forget-dra clA))
                           ⇛
                         (semPred clB (forget-intro (app (forget-elim (f [ dra-closed forget-dra (fun-closed clA clB) ∣ π ]cl))
                                                         (forget-elim (ξcl (dra-closed forget-dra clA))))))))
extent-from-sem {A = A} {B} clA clB {Γ} f f-pred = Π.lam _ (lam _ tm)
  where
    tm : Tm _ _
    tm ⟨ x , [ [ γ , a-ty ] , [ a-pred , e ] ] ⟩' =
      [ func (from (closed-natural clB (always-true-subst π))) (proj₁ (f-pred ⟨ tt , γ ⟩') $⟨ pred-id , refl ⟩ func (to (closed-natural clA (always-true-subst π))) a-pred)
      , trans (cong (func (from (closed-natural clB _))) (
          trans (_↣_.naturality (from (closed-natural clB _))) (cong (func (from (closed-natural clB _))) (sym (
            trans (cong (B ⟪ type-id , _ ⟫_) (cong (proj₁ (f-pred ⟨ tt , γ ⟩') $⟨ type-pred , refl ⟩_) (
              trans (eq (to-eq (closed-⊚ clA _ _)) _) (
              trans (sym (eq (to-eq (closed-subst-eq clA (key-subst-natural π-cell))) _)) (cong (A ⟪ type-id , refl ⟫_) (
                trans (sym (eq (to-eq (closed-⊚ clA _ _)) _)) (
                trans (cong (func (to (closed-natural clA _))) (eq (isoˡ (closed-natural clA _)) _)) (
                sym (_↣_.naturality (to (closed-natural clA _))))))))))) (
            trans (cong (B ⟪ type-id , refl ⟫_) (
              trans (cong (proj₁ (f-pred ⟨ tt , γ ⟩') $⟨ type-pred , refl ⟩_) (ty-cong-2-1 A refl)) (
              PshFun.naturality (proj₁ (f-pred ⟨ tt , γ ⟩'))))) (
            ty-cong-2-1 B refl))))))) (
        trans (sym (
          trans (eq (from-eq (closed-⊚ clB _ _)) _) (
          trans (sym (eq (from-eq (closed-subst-eq clB (key-subst-natural π-cell))) _)) (
          sym (eq (from-eq (closed-⊚ clB _ _)) _))))) (
        trans (cong (func (from (closed-natural clB _))) (cong (_$⟨ type-id , refl ⟩ _) (proj₂ (f-pred ⟨ tt , γ ⟩')))) (
        cong (forget-elim (f [ dra-closed forget-dra (fun-closed clA clB) ∣ π ]cl) €⟨ type-obj , [ γ , a-ty ] ⟩_) e)))
      ]
    Tm.naturality tm tt refl = Σ-≡,≡→≡
      [ trans (cong (B ⟪ pred-id , _ ⟫_) (cong (func (from (closed-natural clB _))) (
          trans ($-cong (proj₁ (f-pred ⟨ tt , _ ⟩')) refl) (
          cong (_$⟨ pred-id , ctx-id Γ ⟩ _) (cong proj₁ (Tm.naturality f-pred tt refl)))))) (
        trans (_↣_.naturality (from (closed-natural clB _))) (
        cong (func (from (closed-natural clB _))) (
          trans (sym (PshFun.naturality (proj₁ (f-pred ⟨ tt , _ ⟩')))) (
          trans ($-cong (proj₁ (f-pred ⟨ tt , _ ⟩')) refl) (
          cong (proj₁ (f-pred ⟨ tt , _ ⟩') $⟨ pred-id , refl ⟩_) (_↣_.naturality (to (closed-natural clA _))))))))
      , uip _ _
      ]


--------------------------------------------------
-- Example: types representing booleans

-- Representing booleans as natural numbers (0 = false, 1 = true)
data IsBit : Pred ℕ 0ℓ where
  0-bit : IsBit 0
  1-bit : IsBit 1

PrimBinaryBool : Ty {C = ↑} ◇
PrimBinaryBool = PrimFromPred ℕ IsBit

BinaryBool : ClosedTy ↑
BinaryBool = FromPred ℕ IsBit

⊓-preserves-bitness : (IsBit ⟨→⟩ IsBit ⟨→⟩ IsBit) _⊓_
⊓-preserves-bitness 0-bit _     = 0-bit
⊓-preserves-bitness 1-bit 0-bit = 0-bit
⊓-preserves-bitness 1-bit 1-bit = 1-bit

1∸-preserves-bitness : (IsBit ⟨→⟩ IsBit) (1 ∸_)
1∸-preserves-bitness 0-bit = 1-bit
1∸-preserves-bitness 1-bit = 0-bit
