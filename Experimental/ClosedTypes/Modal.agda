module Experimental.ClosedTypes.Modal where

open import Model.BaseCategory
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.Type
open import Model.CwF-Structure.Term
open import Model.DRA

open import Experimental.ClosedTypes


private variable
  C D E : BaseCategory


s⟨_∣_⟩ : DRA C D → ClosedTy C → ClosedTy D
s⟨ μ ∣ T ⟩ = ⟨ μ ∣ T [ !◇ _ ] ⟩

module _ (μ : DRA C D) where
  smod-cong : {T S : ClosedTy C} →
              T ≅ᵗʸ S → s⟨ μ ∣ T ⟩ ≅ᵗʸ s⟨ μ ∣ S ⟩
  smod-cong T=S = dra-cong μ (ty-subst-cong-ty _ T=S)

  smod-intro : {Γ : Ctx D} {T : ClosedTy C} → SimpleTm (lock μ Γ) T → SimpleTm Γ s⟨ μ ∣ T ⟩
  smod-intro t = ι[ dra-natural μ _ ] dra-intro μ (ι[ closed-ty-natural _ _ ] t)

  smod-elim : {Γ : Ctx D} {T : ClosedTy C} → SimpleTm Γ s⟨ μ ∣ T ⟩ → SimpleTm (lock μ Γ) T
  smod-elim t = dra-elim μ (
    ι[ transᵗʸ (dra-cong μ (symᵗʸ (closed-ty-natural _ _))) (symᵗʸ (dra-natural μ _)) ] t)

s⟨𝟙∣-⟩ : {T : ClosedTy C} → s⟨ 𝟙 ∣ T ⟩ ≅ᵗʸ T
s⟨𝟙∣-⟩ = transᵗʸ (ty-subst-cong-subst (◇-terminal _ _ _) _) (ty-subst-id _)

smod-ⓜ : (μ : DRA D E) (ρ : DRA C D) {T : ClosedTy C} →
         s⟨ μ ∣ s⟨ ρ ∣ T ⟩ ⟩ ≅ᵗʸ s⟨ μ ⓓ ρ ∣ T ⟩
smod-ⓜ μ ρ = dra-cong μ (transᵗʸ (dra-natural ρ _) (dra-cong ρ (closed-ty-natural _ _)))

seq-mod : {μ ρ : DRA C D} (T : ClosedTy C) →
          μ ≅ᵈ ρ → s⟨ μ ∣ T ⟩ ≅ᵗʸ s⟨ ρ ∣ T ⟩
seq-mod {ρ = ρ} T e = transᵗʸ (eq-dra-tyʳ e _) (dra-cong ρ (closed-ty-natural _ _))

smod-intro-cong : (μ : DRA C D) {Γ : Ctx D} {T : ClosedTy C} {t t' : SimpleTm (lock μ Γ) T} →
                  t ≅ᵗᵐ t' → smod-intro μ t ≅ᵗᵐ smod-intro μ t'
smod-intro-cong μ e = ι-cong (dra-intro-cong μ (ι-cong e))

smod-intro-natural : (μ : DRA C D) {Γ Δ : Ctx D} (σ : Γ ⇒ Δ) {T : ClosedTy C} {t : SimpleTm (lock μ Δ) T} →
                     (smod-intro μ t) [ σ ]s ≅ᵗᵐ smod-intro μ (t [ lock-fmap μ σ ]s)
smod-intro-natural μ σ {t = t} =
  begin
    ι⁻¹[ closed-ty-natural _ σ ] ((ι[ dra-natural μ (!◇ _) ] dra-intro μ (ι[ closed-ty-natural _ (lock-fmap μ (!◇ _)) ] t)) [ σ ]')
  ≅⟨ {!!} ⟩
    ι[ dra-natural μ _ ] dra-intro μ (ι[ closed-ty-natural _ (lock-fmap μ (!◇ _)) ] (ι⁻¹[ closed-ty-natural _ (lock-fmap μ σ) ] (t [ lock-fmap μ σ ]'))) ∎
  where open ≅ᵗᵐ-Reasoning

smtt-mod-elim : {Γ : Ctx E} {T : ClosedTy C} {S : ClosedTy E} (ρ : DRA D E) (μ : DRA C D)
                (t : SimpleTm (Γ ,lock⟨ ρ ⟩) s⟨ μ ∣ T ⟩) (s : SimpleTm (Γ ,,ₛ s⟨ ρ ⓓ μ ∣ T ⟩) S) →
                SimpleTm Γ S
smtt-mod-elim ρ μ t s = s [ id-subst _ ,ₛ (sι⁻¹[ smod-ⓜ ρ μ ] smod-intro ρ t) ]s
