{-# OPTIONS --allow-unsolved-metas #-}

module Experimental.DependentTypes.LaterExperiment where

open import Data.Empty
open import Data.Nat
open import Data.Product renaming (_,_ to [_,_])
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Type.Discrete
open import Experimental.DependentTypes.SigmaType
open import Applications.GuardedRecursion.Model.Modalities

variable
  Γ Δ : Ctx ω


Empty : Ty Γ
Empty ⟨ x , γ ⟩ = ⊥
Empty ⟪ f , x ⟫ ()
ty-cong Empty e-hom {t = ()}
ty-id Empty {t = ()}
ty-comp Empty {t = ()}

Empty-natural : (σ : Δ ⇒ Γ) → Empty [ σ ] ≅ᵗʸ Empty
func (from (Empty-natural σ)) ()
_↣_.naturality (from (Empty-natural σ)) {t = ()}
func (to (Empty-natural σ)) ()
_↣_.naturality (to (Empty-natural σ)) {t = ()}
eq (isoˡ (Empty-natural σ)) ()
eq (isoʳ (Empty-natural σ)) ()

▻'-iter : ℕ → Ty Γ → Ty Γ
▻'-iter zero    T = T
▻'-iter (suc n) T = ▻' (▻'-iter n T)

▻'-iter-diag : (n : ℕ) (T : Ty ◇) → ▻'-iter n T ⟨ n , tt ⟩ ≡ T ⟨ 0 , tt ⟩
▻'-iter-diag zero T = refl
▻'-iter-diag (suc n) T = ▻'-iter-diag n T

▻'[_]_ : Tm Γ Nat' → Ty Γ → Ty Γ
(▻'[ m ] T) ⟨ x , γ ⟩ = ▻'-iter (m ⟨ x , γ ⟩') T ⟨ x , γ ⟩
_⟪_,_⟫_ (▻'[ m ] T) f eγ = {!!}
ty-cong (▻'[ m ] T) = {!!}
ty-id (▻'[ m ] T) = {!!}
ty-comp (▻'[ m ] T) = {!!}

▻'[]-natural : (σ : Δ ⇒ Γ) (m : Tm Γ Nat') (T : Ty Γ) → (▻'[ m ] T) [ σ ] ≅ᵗʸ ▻'[ ι⁻¹[ Discr-natural ℕ σ ] (m [ σ ]') ] (T [ σ ])
▻'[]-natural σ m T = {!!}

▻'[]-cong : (m : Tm Γ Nat') {T S : Ty Γ} → T ≅ᵗʸ S → ▻'[ m ] T ≅ᵗʸ ▻'[ m ] S
▻'[]-cong m T=S = {!!}

nat-fixp : (t : Tm {C = ω} ◇ Nat') → Σ[ k ∈ ℕ ] t ⟨ k , tt ⟩' ≡ k
nat-fixp t = [ t ⟨ 0 , tt ⟩' , Tm.naturality t z≤n refl ]

module Contradiction (p : Tm {C = ω} ◇ (Sigma Nat' (▻'[ ι⁻¹[ Discr-natural _ π ] ξ ] Empty))) where

  fst-nat : ℕ
  fst-nat = proj₁ (nat-fixp (fst p))

  fst-nat-fixp : (fst p) ⟨ fst-nat , tt ⟩' ≡ fst-nat
  fst-nat-fixp = proj₂ (nat-fixp (fst p))

  step1 : ▻'-iter (fst p ⟨ fst-nat , tt ⟩') Empty ⟨ fst-nat , tt ⟩
  step1 = (ι⁻¹[ ▻'[]-cong _ (Empty-natural (tm-subst (fst p))) ] ι⁻¹[ ▻'[]-natural (tm-subst (fst p)) _ Empty ] snd p) ⟨ fst-nat , tt ⟩'

  step2 : ▻'-iter fst-nat Empty ⟨ fst-nat , tt ⟩
  step2 = subst (λ - → ▻'-iter - Empty ⟨ fst-nat , tt ⟩) fst-nat-fixp step1

  contradiction : ⊥
  contradiction = subst (λ A → A) (▻'-iter-diag fst-nat Empty) step2
