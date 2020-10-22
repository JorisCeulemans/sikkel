-- Work in progress on the construction of a type 𝓓 which satisfies
-- 𝓓 ≅ᵗʸ ▻' 𝓓 ⇛ ▻' 𝓓 so that we can interpret the untyped lambda
-- calculus in it. See also GuardedRecursion.Fixpoints

module GuardedRecursion.LambdaCalculus where

open import Data.Nat
open import Data.Nat.Induction using (<-rec; <-wellFounded)
open import Data.Nat.Properties
open import Data.Unit using (⊤; tt)
open import Function using (id)
open import Induction.WellFounded
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]) renaming
  (subst to transp; subst-subst-sym to transp-transp-sym; subst-sym-subst to transp-sym-transp)

open import Helpers
open import Categories
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import GuardedRecursion.Later
open import Reflection.Naturality


◄𝕪-suc : {n : ℕ} → ◄ (𝕪 (suc n)) ≅ᶜ 𝕪 n
func (from ◄𝕪-suc) (s≤s m≤n) = m≤n
_⇒_.naturality (from ◄𝕪-suc) (s≤s m≤n) = refl
func (to ◄𝕪-suc) m≤n = s≤s m≤n
_⇒_.naturality (to ◄𝕪-suc) _ = refl
eq (isoˡ ◄𝕪-suc) (s≤s m≤n) = refl
eq (isoʳ ◄𝕪-suc) _ = refl

𝐷 : (n : ℕ) → Ty {C = ω} (𝕪 n) 0ℓ
𝐷 zero = Unit' ⇛ Unit'
𝐷 (suc n) = ▻ (𝐷 n [ from ◄𝕪-suc ]) ⇛ ▻ (𝐷 n [ from ◄𝕪-suc ])

𝐷-natural : {m n : ℕ} (m≤n : m ≤ n) → 𝐷 n [ to-𝕪⇒𝕪 m≤n ] ≅ᵗʸ 𝐷 m
𝐷-natural {n = zero } z≤n = {!type-naturality-reflect (sub (bin fun-bin (nul discr-nul) (nul discr-nul)) (to-𝕪⇒𝕪 z≤n))
                                                     (bin fun-bin (nul discr-nul) (nul discr-nul))
                                                     refl refl!}
_$⟨_,_⟩_ (func (from (𝐷-natural {n = suc n} z≤n)) _) _ _ _ = tt
PresheafFunc.naturality (func (from (𝐷-natural {n = suc n} z≤n)) _) _ _ _ = refl
CwF-Structure.naturality (from (𝐷-natural {n = suc n} z≤n)) f = to-pshfun-eq λ _ _ _ → refl
func (to (𝐷-natural {n = suc n} z≤n)) {γ = z≤n} _ $⟨ z≤n , _ ⟩ _ = {!tt!}
PresheafFunc.naturality (func (to (𝐷-natural {n = suc n} z≤n)) _) = {!!}
CwF-Structure.naturality (to (𝐷-natural {n = suc n} z≤n)) = {!!}
isoˡ (𝐷-natural {n = suc n} z≤n) = {!!}
isoʳ (𝐷-natural {n = suc n} z≤n) = {!!}
𝐷-natural (s≤s m≤n) = {!!}


{-
𝐷 : ℕ → Set
𝐷 = <-rec (λ _ → Set)
          (λ m IH → (k : ℕ) (k<m : k < m) → IH k k<m → IH k k<m)

𝐷-eq : (n : ℕ) → 𝐷 n ≡ ((m : ℕ) (m<n : m < n) → 𝐷 m → 𝐷 m)
𝐷-eq n = FixPoint.unfold-wfRec
           <-wellFounded
           (λ _ → Set)
           (λ m IH → (k : ℕ) (k<m : k < m) → IH k k<m → IH k k<m)
           (λ m {IH}{IH'} IH-eq → cong (λ f → (k : ℕ) (k<m : k < m) → f k k<m → f k k<m)
                                        {x = IH}{y = IH'}
                                        (funext λ k → funext λ k<m → IH-eq k<m))

𝐷-unfold : {n : ℕ} → 𝐷 n → ((m : ℕ) (m<n : m < n) → 𝐷 m → 𝐷 m)
𝐷-unfold {n} = transp id (𝐷-eq n)

𝐷-fold : {n : ℕ} → ((m : ℕ) (m<n : m < n) → 𝐷 m → 𝐷 m) → 𝐷 n
𝐷-fold {n} = transp id (sym (𝐷-eq n))

𝐷-fold-unfold : {n : ℕ} {d : 𝐷 n} → 𝐷-fold (𝐷-unfold d) ≡ d
𝐷-fold-unfold = transp-sym-transp (𝐷-eq _)

𝐷-unfold-fold : {n : ℕ} {f : (m : ℕ) (m<n : m < n) → 𝐷 m → 𝐷 m} → 𝐷-unfold (𝐷-fold f) ≡ f
𝐷-unfold-fold = transp-transp-sym (𝐷-eq _)

𝒟-prim : Ty (◇ {C = ω}) 0ℓ
type 𝒟-prim n _ = 𝐷 n
morph 𝒟-prim {x = m}{y = n} m≤n _ dn = 𝐷-fold (λ k k<m → 𝐷-unfold dn k (<-transˡ k<m m≤n))
morph-id 𝒟-prim d =
  begin
    𝐷-fold (λ k k<m → 𝐷-unfold d k (<-transˡ k<m ≤-refl))
  ≡⟨ cong 𝐷-fold (funext λ k → funext λ k<m → cong (𝐷-unfold d k) (≤-irrelevant _ _)) ⟩
    𝐷-fold (𝐷-unfold d)
  ≡⟨ 𝐷-fold-unfold ⟩
    d ∎
  where open ≡-Reasoning
morph-comp 𝒟-prim l≤m m≤n eq-nm eq-ms d = cong 𝐷-fold (funext λ k → funext λ k<l → sym
  (begin
    𝐷-unfold (𝐷-fold (λ x x<k → 𝐷-unfold d x (<-transˡ x<k m≤n))) k (<-transˡ k<l l≤m)
  ≡⟨ cong (λ f → f k (<-transˡ k<l l≤m)) 𝐷-unfold-fold ⟩
    𝐷-unfold d k (<-transˡ (<-transˡ k<l l≤m) m≤n)
  ≡⟨ cong (𝐷-unfold d k) (≤-irrelevant _ _) ⟩
    𝐷-unfold d k (<-transˡ k<l (≤-trans l≤m m≤n)) ∎))
  where open ≡-Reasoning

𝒟 : ∀ {ℓ} {Γ : Ctx ω ℓ} → Ty Γ 0ℓ
𝒟 {Γ = Γ} = 𝒟-prim [ !◇ Γ ]

𝒟-fixpoint : {Γ : Ctx ω ℓ} → 𝒟 {Γ = Γ} ≅ᵗʸ (▻' 𝒟 ⇛ ▻' 𝒟)
_$⟨_,_⟩_ (func (from 𝒟-fixpoint) d) z≤n       _ = λ _ → lift tt
_$⟨_,_⟩_ (func (from 𝒟-fixpoint) d) (s≤s m≤n) _ = 𝐷-unfold d _ (s≤s m≤n)
PresheafFunc.naturality (func (from 𝒟-fixpoint) dn) {ρ-xy = z≤n}     {ρ-yz = m≤n}     _ _ dm = refl
PresheafFunc.naturality (func (from 𝒟-fixpoint) dn) {ρ-xy = s≤s l≤m} {ρ-yz = s≤s m≤n} _ _ dm =
  begin
    𝐷-unfold dn _ (s≤s (≤-trans l≤m m≤n)) (𝐷-fold (λ k k<l → 𝐷-unfold dm k (<-transˡ k<l l≤m)))
  ≡⟨ {!!} ⟩ -- Currently I do not manage to prove this. The equality probably does not hold and I suspect
            -- that one will have to add a naturality condition in the definition of 𝐷 (stating more or less
            -- what is needed here).
    𝐷-fold (λ k k<l → 𝐷-unfold (𝐷-unfold dn _ (s≤s m≤n) dm) k (<-transˡ k<l l≤m)) ∎
  where open ≡-Reasoning
CwF-Structure.naturality (from 𝒟-fixpoint) {f = z≤n}     dn = to-pshfun-eq λ { z≤n _ _ → refl }
CwF-Structure.naturality (from 𝒟-fixpoint) {f = s≤s m≤n} dn = to-pshfun-eq λ { z≤n _ dk → refl
                                                                              ; (s≤s k≤m) _ dk →
  begin
    𝐷-unfold dn _ (s≤s (≤-trans k≤m m≤n)) dk
  ≡⟨ cong (λ ineq → 𝐷-unfold dn _ ineq dk) (≤-irrelevant _ _) ⟩
    𝐷-unfold dn _ (<-transˡ (s≤s k≤m) (s≤s m≤n)) dk
  ≡˘⟨ cong (λ g → g _ (s≤s k≤m) dk) 𝐷-unfold-fold ⟩
    𝐷-unfold (𝐷-fold (λ l l<sm → 𝐷-unfold dn l (<-transˡ l<sm (s≤s m≤n)))) _ (s≤s k≤m) dk ∎ }
  where open ≡-Reasoning
func (to 𝒟-fixpoint) {x = n} f = 𝐷-fold (λ m m<n → f $⟨ m<n , refl ⟩_)
CwF-Structure.naturality (to 𝒟-fixpoint) {f = m≤n} f = cong 𝐷-fold (funext λ k → funext λ k<m → funext λ x →
  begin
    𝐷-unfold (𝐷-fold (λ l l<n → f $⟨ l<n , refl ⟩_)) k (<-transˡ k<m m≤n) x
  ≡⟨ cong (λ g → g k (<-transˡ k<m m≤n) x) 𝐷-unfold-fold ⟩
    f $⟨ <-transˡ k<m m≤n , refl ⟩ x
  ≡⟨ {!$-cong {!f!} {!!} {!!} {!!}!} ⟩ -- {!$-cong f (≤-irrelevant _ _) ? ?!} ⟩
    f $⟨ ≤-trans k<m m≤n , _ ⟩ x ∎)
  where open ≡-Reasoning
eq (isoˡ 𝒟-fixpoint) d =
  begin
    𝐷-fold (λ m m<n → (func (from 𝒟-fixpoint) d) $⟨ m<n , refl ⟩_)
  ≡⟨ cong 𝐷-fold (funext λ _ → funext λ { (s≤s _) → refl } ) ⟩
    𝐷-fold (λ m m<n → 𝐷-unfold d m m<n)
  ≡⟨ 𝐷-fold-unfold ⟩
    d ∎
  where open ≡-Reasoning
eq (isoʳ 𝒟-fixpoint) f = to-pshfun-eq λ { z≤n _ d → refl
                                        ; (s≤s m≤n) e dm →
  begin
    𝐷-unfold (𝐷-fold (λ k k<sn → f $⟨ k<sn , refl ⟩_)) _ (s≤s m≤n) dm
  ≡⟨ cong (λ g → g _ (s≤s m≤n) dm) 𝐷-unfold-fold ⟩
    f $⟨ s≤s m≤n , refl ⟩ dm
  ≡⟨ {!$-cong f {!refl!} {!refl!} {!e!}!} ⟩
    f $⟨ s≤s m≤n , e ⟩ dm ∎ }
  where open ≡-Reasoning
-}
