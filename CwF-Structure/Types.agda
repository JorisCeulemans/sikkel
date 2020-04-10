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

strong-rel-comp : (Γ : Ctx ℓ) (k≤m : k ≤ m) (m≤n : m ≤ n) {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} {γk : Γ ⟨ k ⟩} →
                  (eq-nm : Γ ⟪ m≤n ⟫ γn ≡ γm) (eq-mk : Γ ⟪ k≤m ⟫ γm ≡ γk) →
                  Γ ⟪ ≤-trans k≤m m≤n ⟫ γn ≡ γk
strong-rel-comp Γ k≤m m≤n {γn} eq-nm eq-mk = trans (rel-comp Γ k≤m m≤n γn)
                                                   (trans (cong (Γ ⟪ k≤m ⟫) eq-nm)
                                                          eq-mk)

record Ty {ℓ} (Γ : Ctx ℓ) : Set (lsuc ℓ) where
  constructor MkTy
  field
    type : (n : ℕ) (γ : Γ ⟨ n ⟩) → Set ℓ
    morph : ∀ {m n} (m≤n : m ≤ n) {γ : Γ ⟨ n ⟩} {γ' : Γ ⟨ m ⟩} → Γ ⟪ m≤n ⟫ γ ≡ γ' → type n γ → type m γ'
    morph-id : ∀ {n} {γ : Γ ⟨ n ⟩} (t : type n γ) → morph ≤-refl (rel-id Γ γ) t ≡ t
    morph-comp : ∀ {k m n} (k≤m : k ≤ m) (m≤n : m ≤ n) {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} {γk : Γ ⟨ k ⟩} →
                 (eq-nm : Γ ⟪ m≤n ⟫ γn ≡ γm) (eq-mk : Γ ⟪ k≤m ⟫ γm ≡ γk) (t : type n γn) →
                 morph (≤-trans k≤m  m≤n) (strong-rel-comp Γ k≤m m≤n eq-nm eq-mk) t ≡ morph k≤m eq-mk (morph m≤n eq-nm t)
open Ty public

_⟨_,_⟩ : {Γ : Ctx ℓ} → Ty Γ → (n : ℕ) → Γ ⟨ n ⟩ → Set ℓ
T ⟨ n , γ ⟩ = type T n γ

_⟪_,_⟫ : {Γ : Ctx ℓ} (T : Ty Γ) (ineq : m ≤ n) {γ : Γ ⟨ n ⟩} {γ' : Γ ⟨ m ⟩} → Γ ⟪ ineq ⟫ γ ≡ γ' → T ⟨ n , γ ⟩ → T ⟨ m , γ' ⟩
T ⟪ ineq , eq ⟫ = morph T ineq eq

_⟪_,_⟫_ : {Γ : Ctx ℓ} (T : Ty Γ) (ineq : m ≤ n) {γ : Γ ⟨ n ⟩} {γ' : Γ ⟨ m ⟩} → Γ ⟪ ineq ⟫ γ ≡ γ' → T ⟨ n , γ ⟩ → T ⟨ m , γ' ⟩
T ⟪ ineq , eq ⟫ t = (T ⟪ ineq , eq ⟫) t

morph-subst : {Γ : Ctx ℓ} (T : Ty Γ) {m≤n : m ≤ n}
              {γ1 : Γ ⟨ n ⟩} {γ2 γ3 : Γ ⟨ m ⟩}
              (eq12 : Γ ⟪ m≤n ⟫ γ1 ≡ γ2) (eq23 : γ2 ≡ γ3)
              (t : T ⟨ n , γ1 ⟩) →
              subst (λ x → T ⟨ m , x ⟩) eq23 (T ⟪ m≤n , eq12 ⟫ t) ≡ T ⟪ m≤n , trans eq12 eq23 ⟫ t
morph-subst T refl refl t = refl

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
{-
_[_] : {Δ Γ : Ctx ℓ} → Ty Γ → Δ ⇒ Γ → Ty Δ
type (T [ σ ]) = λ n δ → T ⟨ n , func σ δ ⟩
morph (T [ σ ]) m≤n δ t = subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (T ⟪ m≤n , func σ δ ⟫ t)
morph-id (_[_] {Δ = Δ}{Γ} T σ) {n} {δ} t = proof
  where
     open ≡-Reasoning
--     abstract
     proof =
       subst (λ x → T ⟨ _ , func σ x ⟩) (rel-id Δ δ) (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (T ⟪ ≤-refl , func σ δ ⟫ t))
         ≡⟨ subst-∘ (rel-id Δ δ) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (cong (func σ) (rel-id Δ δ)) (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (T ⟪ ≤-refl , func σ δ ⟫ t))
         ≡⟨ subst-subst (naturality σ δ) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (trans (naturality σ δ) (cong (func σ) (rel-id Δ δ))) (T ⟪ ≤-refl , func σ δ ⟫ t)
         ≡⟨ cong (λ y → subst (λ x → T ⟨ _ , x ⟩) y (T ⟪ ≤-refl , func σ δ ⟫ t)) (uip _ (rel-id Γ (func σ δ))) ⟩
           -- Currently this equality is proven using uip. In a setting without uip, we would need to impose an extra coherence requirement
           -- on substitutions, ensuring that trans (naturality σ) (cong (func σ ∘_) (rel-id Δ)) ≡ cong (_∘ func σ) (rel-id Γ).
       subst (λ x → T ⟨ _ , x ⟩) (rel-id Γ (func σ δ)) (T ⟪ ≤-refl , func σ δ ⟫ t)
         ≡⟨ morph-id T t ⟩
       t ∎
morph-comp (_[_] {Δ = Δ}{Γ} T σ) k≤m m≤n {δ} t = proof
  where
     open ≡-Reasoning
--     abstract
     proof =
       subst (λ x → T ⟨ _ , func σ x ⟩) (rel-comp Δ k≤m m≤n δ)
         (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ)
           (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
         ≡⟨ subst-∘ (rel-comp Δ k≤m m≤n δ) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (cong (func σ) (rel-comp Δ k≤m m≤n δ))
         (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ)
           (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
         ≡⟨ subst-subst (naturality σ δ) ⟩
       subst (λ x → T ⟨ _ , x ⟩)
         (trans (naturality σ δ) (cong (func σ) (rel-comp Δ k≤m m≤n δ)))
           (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t)
         ≡⟨ cong (λ y → subst (λ x → T ⟨ _ , x ⟩) y (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
                 (uip (trans (naturality σ δ) (cong (func σ) (rel-comp Δ k≤m m≤n δ))) _) ⟩
         -- Again, without uip we would need to include an extra coherence law for substitutions.
       subst (λ x → T ⟨ _ , x ⟩)
         (trans (trans (rel-comp Γ k≤m m≤n (func σ δ)) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ))) (naturality σ (Δ ⟪ m≤n ⟫ δ)))
           (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t)
         ≡⟨ sym (subst-subst (trans (rel-comp Γ k≤m m≤n (func σ δ)) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ)))) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))
         (subst (λ x → T ⟨ _ , x ⟩) (trans (rel-comp Γ k≤m m≤n (func σ δ)) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ)))
           (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t))
         ≡⟨ cong (subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))) (sym (subst-subst (rel-comp Γ k≤m m≤n (func σ δ)))) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))
         (subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ))
           (subst (λ x → T ⟨ _ , x ⟩) (rel-comp Γ k≤m m≤n (func σ δ))
             (T ⟪ ≤-trans k≤m m≤n , func σ δ ⟫ t)))
         ≡⟨ cong (λ y → subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ)) (subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ)) y))
                 (morph-comp T k≤m m≤n t) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))
         (subst (λ x → T ⟨ _ , x ⟩) (cong (Γ ⟪ k≤m ⟫) (naturality σ δ))
           (T ⟪ k≤m , Γ ⟪ m≤n ⟫ (func σ δ) ⟫ (T ⟪ m≤n , func σ δ ⟫ t)))
         ≡⟨ cong (subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))) (sym (subst-∘ (naturality σ δ))) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))
         (subst (λ x → T ⟨ _ , Γ ⟪ k≤m ⟫ x ⟩) (naturality σ δ)
           (T ⟪ k≤m , Γ ⟪ m≤n ⟫ (func σ δ) ⟫ (T ⟪ m≤n , func σ δ ⟫ t)))
         ≡⟨ cong (subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ)))
                 (weak-subst-application (λ x y → T ⟪ k≤m , x ⟫ y) (naturality σ δ)) ⟩
       subst (λ x → T ⟨ _ , x ⟩) (naturality σ (Δ ⟪ m≤n ⟫ δ))
         (T ⟪ k≤m , func σ (Δ ⟪ m≤n ⟫ δ) ⟫
           (subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) (T ⟪ m≤n , func σ δ ⟫ t))) ∎
-}

ty-subst-id : {Γ : Ctx ℓ} (T : Ty Γ) → T [ id-subst Γ ] ≡ T
ty-subst-id T = cong₃-d (MkTy _)
                        (funextI (funextI (funext λ m≤n → funextI (funextI (funext λ eq → funext λ t →
                          cong (λ x → T ⟪ m≤n , x ⟫ t) (cong-id eq))))))
                        (funextI (funextI (funext (λ _ → uip _ _))))
                        (funextI (funextI (funextI (funext λ _ → funext λ _ → funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _)))))))

{-
-- abstract
ty-subst-id : {Γ : Ctx ℓ} (T : Ty Γ) → T [ id-subst Γ ] ≡ T
ty-subst-id T = cong₂-d (MkTy _ _)
                        (funextI (funextI (funext (λ _ → uip _ _))))
                        (funextI (funextI (funextI (funext λ _ → funext λ _ → funextI (funext λ _ → uip _ _)))))
-}

cong-trans : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) →
             {x y z : A} (x≡y : x ≡ y) {y≡z : y ≡ z} →
             cong f (trans x≡y y≡z) ≡ trans (cong f x≡y) (cong f y≡z)
cong-trans f refl = refl

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

{-
ty-subst-comp : {Δ Γ Θ : Ctx ℓ} (T : Ty Θ) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) → T [ τ ] [ σ ] ≡ T [ τ ⊚ σ ]
ty-subst-comp T τ σ = cong₃-d (MkTy _)
  (funextI (funextI (funext λ ineq → funext λ δ → funext λ t →
      subst (λ x → T ⟨ _ , func τ x ⟩) (naturality σ δ)
      (subst (λ x → T ⟨ _ , x ⟩) (naturality τ (func σ δ))
       (T ⟪ ineq , func τ (func σ δ) ⟫ t))
       ≡⟨ subst-∘ (naturality σ δ)  ⟩
      subst (λ x → T ⟨ _ , x ⟩) (cong (func τ) (naturality σ δ))
      (subst (λ x → T ⟨ _ , x ⟩) (naturality τ (func σ δ))
       (T ⟪ ineq , func τ (func σ δ) ⟫ t))
       ≡⟨ subst-subst (naturality τ (func σ δ))  ⟩
      subst (λ x → T ⟨ _ , x ⟩)
        (trans (naturality τ (func σ δ)) (cong (func τ) (naturality σ δ)))
        (T ⟪ ineq , func τ (func σ δ) ⟫ t)
       ≡⟨ cong
            (λ p →
               subst (λ x → T ⟨ _ , x ⟩) p
               (T ⟪ ineq , func τ (func σ δ) ⟫ t))
            (cong (trans (naturality τ (func σ δ))) (sym (trans-reflʳ _))) ⟩
       subst (λ x → T ⟨ _ , x ⟩)
         (trans (naturality τ (func σ δ))
           (trans (cong (func τ) (naturality σ δ))
         refl))
       (T ⟪ ineq , func τ (func σ δ) ⟫ t) ∎
      )))
  (funextI (funextI (funext (λ _ → uip _ _))))
  (funextI (funextI (funextI (funext λ _ → funext λ _ → funextI (funext λ _ → uip _ _)))))
  where open ≡-Reasoning
-}
