--------------------------------------------------
-- Types
--------------------------------------------------

module CwF-Structure.Types where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Level renaming (zero to lzero; suc to lsuc)
open import Function hiding (_⟨_⟩_; _↣_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers
open import CwF-Structure.Contexts

infix 15 _⟨_,_⟩
infixr 11 _⟪_,_⟫_
infix 10 _↣_
infix 1 _≅ⁿ_ _≅ᵗʸ_
infixl 20 _⊙_


--------------------------------------------------
-- Definition of types in a context

record Ty {ℓ} (Γ : Ctx ℓ) : Set (lsuc ℓ) where
  constructor MkTy
  field
    type : (n : ℕ) (γ : Γ ⟨ n ⟩) → Set ℓ
    morph : ∀ {m n} (m≤n : m ≤ n) {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} → Γ ⟪ m≤n ⟫ γn ≡ γm → type n γn → type m γm
    morph-id : ∀ {n} {γ : Γ ⟨ n ⟩} (t : type n γ) → morph ≤-refl (rel-id Γ γ) t ≡ t
    morph-comp : ∀ {k m n} (k≤m : k ≤ m) (m≤n : m ≤ n) {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} {γk : Γ ⟨ k ⟩} →
                 (eq-nm : Γ ⟪ m≤n ⟫ γn ≡ γm) (eq-mk : Γ ⟪ k≤m ⟫ γm ≡ γk) (t : type n γn) →
                 morph (≤-trans k≤m m≤n) (strong-rel-comp Γ eq-nm eq-mk) t ≡ morph k≤m eq-mk (morph m≤n eq-nm t)
open Ty public

_⟨_,_⟩ : {Γ : Ctx ℓ} → Ty Γ → (n : ℕ) → Γ ⟨ n ⟩ → Set ℓ
T ⟨ n , γ ⟩ = type T n γ

_⟪_,_⟫ : {Γ : Ctx ℓ} (T : Ty Γ) (ineq : m ≤ n) {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} → Γ ⟪ ineq ⟫ γn ≡ γm →
         T ⟨ n , γn ⟩ → T ⟨ m , γm ⟩
T ⟪ ineq , eq ⟫ = morph T ineq eq

_⟪_,_⟫_ : {Γ : Ctx ℓ} (T : Ty Γ) (ineq : m ≤ n) {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} → Γ ⟪ ineq ⟫ γn ≡ γm →
          T ⟨ n , γn ⟩ → T ⟨ m , γm ⟩
T ⟪ ineq , eq ⟫ t = (T ⟪ ineq , eq ⟫) t

morph-subst : {Γ : Ctx ℓ} (T : Ty Γ) {m≤n : m ≤ n}
              {γ1 : Γ ⟨ n ⟩} {γ2 γ3 : Γ ⟨ m ⟩}
              (eq12 : Γ ⟪ m≤n ⟫ γ1 ≡ γ2) (eq23 : γ2 ≡ γ3)
              (t : T ⟨ n , γ1 ⟩) →
              subst (λ x → T ⟨ m , x ⟩) eq23 (T ⟪ m≤n , eq12 ⟫ t) ≡ T ⟪ m≤n , trans eq12 eq23 ⟫ t
morph-subst T refl refl t = refl

-- Instead of pattern matching on e-ineq, we could prove the following as cong₂-d (λ x y → T ⟪ x , y ⟫ t) e-ineq (...),
-- but cong₂-d would then pattern match on this equality anyway.
-- This is one of the places where we assume uip (by pattern matching on both eγ and eγ'). We could probably avoid it
-- by requiring morph T to "not depend on eγ" (propositionally).
morph-cong : {Γ : Ctx ℓ} (T : Ty Γ) {m≤n m≤n' : m ≤ n} (e-ineq : m≤n ≡ m≤n')
             {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} (eγ : Γ ⟪ m≤n ⟫ γn ≡ γm) (eγ' : Γ ⟪ m≤n' ⟫ γn ≡ γm)
             {t : T ⟨ n , γn ⟩} →
             T ⟪ m≤n , eγ ⟫ t ≡ T ⟪ m≤n' , eγ' ⟫ t
morph-cong {Γ = Γ} T refl {γn} refl refl {t} = refl

module _ {Γ : Ctx ℓ} (T : Ty Γ) where
  strict-morph : (m≤n : m ≤ n) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ → T ⟨ m , Γ ⟪ m≤n ⟫ γ ⟩
  strict-morph m≤n γ t = T ⟪ m≤n , refl ⟫ t

  strict-morph-id : {γ : Γ ⟨ n ⟩} (t : T ⟨ n , γ ⟩) →
                    subst (λ x → T ⟨ n , x ⟩) (rel-id Γ γ) (strict-morph ≤-refl γ t) ≡ t
  strict-morph-id t = trans (morph-subst T refl (rel-id Γ _) t)
                            (morph-id T t)

  strict-morph-comp : (k≤m : k ≤ m) (m≤n : m ≤ n) {γ : Γ ⟨ n ⟩} (t : T ⟨ n , γ ⟩) →
                      subst (λ x → T ⟨ k , x ⟩) (rel-comp Γ k≤m m≤n γ) (strict-morph (≤-trans k≤m m≤n) γ t) ≡
                        strict-morph k≤m (Γ ⟪ m≤n ⟫ γ) (strict-morph m≤n γ t)
  strict-morph-comp k≤m m≤n t = trans (morph-subst T refl (rel-comp Γ k≤m m≤n _) t)
                                      (trans (cong (λ x → T ⟪ _ , x ⟫ t) (sym (trans-reflʳ _)))
                                             (morph-comp T k≤m m≤n refl refl t))


--------------------------------------------------
-- Natural transformations between types

record _↣_ {ℓ} {Γ : Ctx ℓ} (T S : Ty Γ) : Set ℓ where
  field
    func : ∀ {n} {γ} → T ⟨ n , γ ⟩ → S ⟨ n , γ ⟩
    naturality : ∀ {m n} {m≤n : m ≤ n} {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} {eγ : Γ ⟪ m≤n ⟫ γn ≡ γm} (t : T ⟨ n , γn ⟩) →
                 S ⟪ m≤n , eγ ⟫ (func t) ≡ func (T ⟪ m≤n , eγ ⟫ t)
open _↣_ public

record _≅ⁿ_ {ℓ} {Γ : Ctx ℓ} {T S : Ty Γ} (η φ : T ↣ S) : Set ℓ where
  field
    eq : ∀ {n γ} (t : T ⟨ n , γ ⟩) → func η t ≡ func φ t
open _≅ⁿ_ public

≅ⁿ-refl : {Γ : Ctx ℓ} {T S : Ty Γ} {η : T ↣ S} → η ≅ⁿ η
eq (≅ⁿ-refl {η = η}) _ = refl

≅ⁿ-sym : {Γ : Ctx ℓ} {T S : Ty Γ} {η φ : T ↣ S} → η ≅ⁿ φ → φ ≅ⁿ η
eq (≅ⁿ-sym η=φ) t = sym (eq η=φ t)

≅ⁿ-trans : {Γ : Ctx ℓ} {T S : Ty Γ} {η φ µ : T ↣ S} → η ≅ⁿ φ → φ ≅ⁿ µ → η ≅ⁿ µ
eq (≅ⁿ-trans η=φ φ=µ) t = trans (eq η=φ t) (eq φ=µ t)

module ≅ⁿ-Reasoning {Γ : Ctx ℓ} {T S : Ty Γ} where
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

id-trans : {Γ : Ctx ℓ} (T : Ty Γ) → T ↣ T
func (id-trans T) = id
naturality (id-trans T) _ = refl

_⊙_ : {Γ : Ctx ℓ} {R S T : Ty Γ} → S ↣ T → R ↣ S → R ↣ T
func (φ ⊙ η) = func φ ∘ func η
naturality (φ ⊙ η) r = trans (naturality φ (func η r))
                              (cong (func φ) (naturality η r))

⊙-id-transʳ : {Γ : Ctx ℓ} {T S : Ty Γ} (η : T ↣ S) → η ⊙ id-trans T ≅ⁿ η
eq (⊙-id-transʳ η) _ = refl

⊙-id-transˡ : {Γ : Ctx ℓ} {T S : Ty Γ} (η : T ↣ S) → id-trans S ⊙ η ≅ⁿ η
eq (⊙-id-transˡ η) _ = refl

⊙-assoc : {Γ : Ctx ℓ} {T₁ T₂ T₃ T₄ : Ty Γ}  (η₃₄ : T₃ ↣ T₄) (η₂₃ : T₂ ↣ T₃) (η₁₂ : T₁ ↣ T₂) → (η₃₄ ⊙ η₂₃) ⊙ η₁₂ ≅ⁿ η₃₄ ⊙ (η₂₃ ⊙ η₁₂)
eq (⊙-assoc η₃₄ η₂₃ η₁₂) _ = refl

⊙-congˡ : {Γ : Ctx ℓ} {R S T : Ty Γ} (φ : S ↣ T) {η η' : R ↣ S} → η ≅ⁿ η' → φ ⊙ η ≅ⁿ φ ⊙ η'
eq (⊙-congˡ φ η=η') δ = cong (func φ) (eq η=η' δ)

⊙-congʳ : {Γ : Ctx ℓ} {R S T : Ty Γ} {φ φ' : S ↣ T} (η : R ↣ S) → φ ≅ⁿ φ' → φ ⊙ η ≅ⁿ φ' ⊙ η
eq (⊙-congʳ η φ=φ') δ = eq φ=φ' (func η δ)


--------------------------------------------------
-- Equivalence of types

record _≅ᵗʸ_ {ℓ} {Γ : Ctx ℓ} (T S : Ty Γ) : Set ℓ where
  field
    from : T ↣ S
    to : S ↣ T
    isoˡ : to ⊙ from ≅ⁿ id-trans T
    isoʳ : from ⊙ to ≅ⁿ id-trans S
open _≅ᵗʸ_ public

≅ᵗʸ-refl : {Γ : Ctx ℓ} {T : Ty Γ} → T ≅ᵗʸ T
from (≅ᵗʸ-refl {T = T}) = id-trans T
to (≅ᵗʸ-refl {T = T}) = id-trans T
isoˡ (≅ᵗʸ-refl {T = T}) = ≅ⁿ-refl
isoʳ (≅ᵗʸ-refl {T = T}) = ≅ⁿ-refl

≅ᵗʸ-sym : {Γ : Ctx ℓ} {S T : Ty Γ} → S ≅ᵗʸ T → T ≅ᵗʸ S
from (≅ᵗʸ-sym S=T) = to S=T
to (≅ᵗʸ-sym S=T) = from S=T
isoˡ (≅ᵗʸ-sym S=T) = isoʳ S=T
isoʳ (≅ᵗʸ-sym S=T) = isoˡ S=T

≅ᵗʸ-trans : {Γ : Ctx ℓ} {S T R : Ty Γ} → S ≅ᵗʸ T → T ≅ᵗʸ R → S ≅ᵗʸ R
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

module ≅ᵗʸ-Reasoning {Γ : Ctx ℓ} where
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

_[_] : {Δ Γ : Ctx ℓ} → Ty Γ → Δ ⇒ Γ → Ty Δ
type (T [ σ ]) n δ = T ⟨ n , func σ δ ⟩
morph (_[_] {Γ = Γ} T σ) m≤n {δn}{δm} eq-nm t = T ⟪ m≤n , proof ⟫ t
  where
    proof : Γ ⟪ m≤n ⟫ func σ δn ≡ func σ δm
    proof = trans (naturality σ δn) (cong (func σ) eq-nm)
morph-id (T [ σ ]) t = trans (cong (λ x → T ⟪ ≤-refl , x ⟫ t) (uip _ _))
                             (morph-id T t)
morph-comp (T [ σ ]) k≤m m≤n eq-nm eq-mk t = trans (cong (λ x → T ⟪ ≤-trans k≤m m≤n , x ⟫ t) (uip _ _))
                                                   (morph-comp T k≤m m≤n _ _ t)

ty-subst-id : {Γ : Ctx ℓ} (T : Ty Γ) → T [ id-subst Γ ] ≅ᵗʸ T
from (ty-subst-id T) = record { func = id ; naturality = λ t → cong (λ x → T ⟪ _ , x ⟫ t) (sym (cong-id _)) }
to (ty-subst-id T) = record { func = id ; naturality = λ t → cong (λ x → T ⟪ _ , x ⟫ t) (cong-id _) }
isoˡ (ty-subst-id T) = record { eq = λ t → refl }
isoʳ (ty-subst-id T) = record { eq = λ t → refl }

{-
ty-subst-id : {Γ : Ctx ℓ} (T : Ty Γ) → T [ id-subst Γ ] ≡ T
ty-subst-id T = cong₃-d (MkTy _)
                        (funextI (funextI (funext λ m≤n → funextI (funextI (funext λ eq → funext λ t →
                          cong (λ x → T ⟪ m≤n , x ⟫ t) (cong-id eq))))))
                        (funextI (funextI (funext (λ _ → uip _ _))))
                        (funextI (funextI (funextI (funext λ _ → funext λ _ → funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _)))))))
-}

ty-subst-comp : {Δ Γ Θ : Ctx ℓ} (T : Ty Θ) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → T [ τ ] [ σ ] ≅ᵗʸ T [ τ ⊚ σ ]
from (ty-subst-comp T τ σ) = record { func = id ; naturality = λ t → cong (λ x → T ⟪ _ , x ⟫ t) (uip _ _) }
to (ty-subst-comp T τ σ) = record { func = id ; naturality = λ t → cong (λ x → T ⟪ _ , x ⟫ t) (uip _ _) }
isoˡ (ty-subst-comp T τ σ) = record { eq = λ t → refl }
isoʳ (ty-subst-comp T τ σ) = record { eq = λ t → refl }

{-
-- TODO: Maybe it would be better to just use uip (since equality proofs will probably not be expanded
-- as much as they are now).
ty-subst-comp : {Δ Γ Θ : Ctx ℓ} (T : Ty Θ) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → T [ τ ] [ σ ] ≡ T [ τ ⊚ σ ]
ty-subst-comp T τ σ = cong₃-d (MkTy _)
                              (funextI (funextI (funext λ m≤n → funextI (funextI (funext λ eq → funext λ t →
                                cong (λ x → T ⟪ m≤n , x ⟫ t)
  (trans (naturality τ (func σ _))
         (cong (func τ) (trans (naturality σ _)
                               (cong (func σ) eq)))
     ≡⟨ cong (trans (naturality τ (func σ _))) (cong-trans (func τ) (naturality σ _)) ⟩
   trans (naturality τ (func σ _))
         (trans (cong (func τ) (naturality σ _))
                (cong (func τ) (cong (func σ) eq)))
     ≡⟨ sym (trans-assoc (naturality τ (func σ _))) ⟩
   trans (trans (naturality τ (func σ _))
                (cong (func τ) (naturality σ _)))
         (cong (func τ) (cong (func σ) eq))
     ≡⟨ cong (trans (trans (naturality τ (func σ _))
                           (cong (func τ) (naturality σ _))))
             (sym (cong-∘ eq)) ⟩
   trans (trans (naturality τ (func σ _))
                (cong (func τ) (naturality σ _)))
         (cong (λ x → func τ (func σ x)) eq) ∎))))))
                              (funextI (funextI (funext (λ _ → uip _ _))))
                              (funextI (funextI (funextI (funext λ _ → funext λ _ → funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _)))))))
  where open ≡-Reasoning
-}

ty-subst-map : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) {T S : Ty Γ} → (T ↣ S) → T [ σ ] ↣ S [ σ ]
func (ty-subst-map σ η) t = func η t
naturality (ty-subst-map σ η) t = naturality η t

ty-subst-map-id : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) {T : Ty Γ} → ty-subst-map σ (id-trans T) ≅ⁿ id-trans (T [ σ ])
eq (ty-subst-map-id σ) t = refl

ty-subst-map-comp : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) {R S T : Ty Γ} (φ : S ↣ T) (η : R ↣ S) → ty-subst-map σ (φ ⊙ η) ≅ⁿ ty-subst-map σ φ ⊙ ty-subst-map σ η
eq (ty-subst-map-comp σ φ η) t = refl

ty-subst-cong-ty : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) {T S : Ty Γ} → T ≅ᵗʸ S → T [ σ ] ≅ᵗʸ S [ σ ]
from (ty-subst-cong-ty σ T=S) = ty-subst-map σ (from T=S)
to (ty-subst-cong-ty σ T=S) = ty-subst-map σ (to T=S)
eq (isoˡ (ty-subst-cong-ty σ T=S)) t = eq (isoˡ T=S) t
eq (isoʳ (ty-subst-cong-ty σ T=S)) t = eq (isoʳ T=S) t

ctx-element-subst : {Γ : Ctx ℓ} (T : Ty Γ) {γ γ' : Γ ⟨ n ⟩} → γ ≡ γ' → T ⟨ n , γ ⟩ → T ⟨ n , γ' ⟩
ctx-element-subst {Γ = Γ} T eγ = T ⟪ ≤-refl , trans (rel-id Γ _) eγ ⟫

ty-subst-cong-subst : {Δ Γ : Ctx ℓ} {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → (T : Ty Γ) → T [ σ ] ≅ᵗʸ T [ τ ]
from (ty-subst-cong-subst σ=τ T) = record { func = λ {n δ} t → ctx-element-subst T (eq σ=τ δ) t
                                          ; naturality = λ {_ _ m≤n} t →
  begin
    T ⟪ m≤n , _ ⟫ T ⟪ ≤-refl , _ ⟫ t
  ≡˘⟨ morph-comp T m≤n ≤-refl _ _ t ⟩
    T ⟪ ≤-trans m≤n ≤-refl , _ ⟫ t
  ≡⟨ morph-cong T (≤-irrelevant _ _) _ _ ⟩
    T ⟪ ≤-trans ≤-refl m≤n , _ ⟫ t
  ≡⟨ morph-comp T ≤-refl m≤n _ _ t ⟩
    T ⟪ ≤-refl , _ ⟫ T ⟪ m≤n , _ ⟫ t ∎ }
  where open ≡-Reasoning
to (ty-subst-cong-subst σ=τ T) = record { func = λ {n δ} t → ctx-element-subst T (sym (eq σ=τ δ)) t
                                        ; naturality = λ {_ _ m≤n} t →
  begin
    T ⟪ m≤n , _ ⟫ T ⟪ ≤-refl , _ ⟫ t
  ≡˘⟨ morph-comp T m≤n ≤-refl _ _ t ⟩
    T ⟪ ≤-trans m≤n ≤-refl , _ ⟫ t
  ≡⟨ morph-cong T (≤-irrelevant _ _) _ _ ⟩
    T ⟪ ≤-trans ≤-refl m≤n , _ ⟫ t
  ≡⟨ morph-comp T ≤-refl m≤n _ _ t ⟩
    T ⟪ ≤-refl , _ ⟫ T ⟪ m≤n , _ ⟫ t ∎ }
  where open ≡-Reasoning
eq (isoˡ (ty-subst-cong-subst {Γ = Γ} σ=τ T)) t =
  -- Here we cannot use morph-id T twice because the omitted equality proofs are not rel-id Γ _
  -- (i.e. T ⟪_⟫ t is not applied to the identity morphism in the category of elements of Γ).
  begin
    T ⟪ ≤-refl , _ ⟫ T ⟪ ≤-refl , _ ⟫ t
  ≡˘⟨ morph-comp T ≤-refl ≤-refl _ _ t ⟩
    T ⟪ ≤-trans ≤-refl ≤-refl , _ ⟫ t
  ≡⟨ morph-cong T (≤-irrelevant _ _) _ _ ⟩
    T ⟪ ≤-refl , rel-id Γ _ ⟫ t
  ≡⟨ morph-id T t ⟩
    t ∎
  where open ≡-Reasoning
eq (isoʳ (ty-subst-cong-subst σ=τ T)) t =
  begin
    T ⟪ ≤-refl , _ ⟫ T ⟪ ≤-refl , _ ⟫ t
  ≡˘⟨ morph-comp T ≤-refl ≤-refl _ _ t ⟩
    T ⟪ ≤-trans ≤-refl ≤-refl , _ ⟫ t
  ≡⟨ morph-cong T (≤-irrelevant _ _) _ _ ⟩
    T ⟪ ≤-refl , _ ⟫ t
  ≡⟨ morph-id T t ⟩
    t ∎
  where open ≡-Reasoning
