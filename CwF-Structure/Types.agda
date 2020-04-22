module CwF-Structure.Types where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers
open import CwF-Structure.Contexts

infix 15 _⟨_,_⟩
infixr 11 _⟪_,_⟫_

--------------------------------------------------
-- Types
--------------------------------------------------

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

morph-ineq-cong : {Γ : Ctx ℓ} (T : Ty Γ) {m≤n m≤n' : m ≤ n} (e-ineq : m≤n ≡ m≤n')
                  {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} (eγ : Γ ⟪ m≤n' ⟫ γn ≡ γm)
                  {t : T ⟨ n , γn ⟩} →
                  T ⟪ m≤n , trans (cong (Γ ⟪_⟫ γn) e-ineq) eγ ⟫ t ≡ T ⟪ m≤n' , eγ ⟫ t
morph-ineq-cong {Γ = Γ} T refl {γn} eγ {t} = refl
-- Instead of pattern matching on e-ineq, we could prove this as cong₂-d (λ x y → T ⟪ x , y ⟫ t) e-ineq (...),
-- but cong₂-d would then pattern match on this equality anyway.

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

{- TODO: see if it is a good idea using the following way to prove equality of types
   + uniform way to prove type equality
   - using funext to show that type T ≡ type S where refl can be used most of the time
to-ty-eq : {Γ : Ctx ℓ} {T S : Ty Γ} →
           (et : (n : ℕ) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ ≡ S ⟨ n , γ ⟩) →
           ({m n : ℕ} (m≤n : m ≤ n) (γ : Γ ⟨ n ⟩) (t : T ⟨ n , γ ⟩) →
               subst (λ x → x) (et m (Γ ⟪ m≤n ⟫ γ)) (T ⟪ m≤n , γ ⟫ t) ≡ S ⟪ m≤n , γ ⟫ subst (λ x → x) (et n γ) t) →
           T ≡ S
to-ty-eq et em = cong₄-d MkTy
                         (funext λ n → funext λ γ → et n γ)
                         {!!}
                         {!!}
                         {!!}
-}

_[_] : {Δ Γ : Ctx ℓ} → Ty Γ → Δ ⇒ Γ → Ty Δ
type (T [ σ ]) n δ = T ⟨ n , func σ δ ⟩
morph (_[_] {Γ = Γ} T σ) m≤n {δ}{δ'} eq t = T ⟪ m≤n , proof ⟫ t
  where
    proof : Γ ⟪ m≤n ⟫ func σ δ ≡ func σ δ'
    proof = trans (naturality σ δ) (cong (func σ) eq)
morph-id (T [ σ ]) t = trans (cong (λ x → T ⟪ ≤-refl , x ⟫ t) (uip _ _))
                             (morph-id T t)
morph-comp (T [ σ ]) k≤m m≤n eq-nm eq-mk t = trans (cong (λ x → T ⟪ ≤-trans k≤m m≤n , x ⟫ t) (uip _ _))
                                                   (morph-comp T k≤m m≤n _ _ t)

ty-subst-id : {Γ : Ctx ℓ} (T : Ty Γ) → T [ id-subst Γ ] ≡ T
ty-subst-id T = cong₃-d (MkTy _)
                        (funextI (funextI (funext λ m≤n → funextI (funextI (funext λ eq → funext λ t →
                          cong (λ x → T ⟪ m≤n , x ⟫ t) (cong-id eq))))))
                        (funextI (funextI (funext (λ _ → uip _ _))))
                        (funextI (funextI (funextI (funext λ _ → funext λ _ → funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _)))))))

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
