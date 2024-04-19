open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.MSTT.Soundness.Variable
  (𝒫 : MSTT-Parameter)
  where

import Relation.Binary.PropositionalEquality as Ag

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.DRA as DRA hiding
  (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; lock-fmap; lock-fmap-cong; lock-fmap-id; lock-fmap-⊚
  ; TwoCell; id-cell; _ⓣ-vert_; _ⓣ-hor_; key-subst; key-subst-natural; key-subst-eq)

open MSTT-Parameter 𝒫
open import Experimental.LogicalFramework.MSTT 𝒫

private variable
  m n o : Mode


v0-sound : (Γ : Ctx n) (μ : Modality m n) (x : Name) (T : Ty m) →
           dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩)) M.≅ᵗᵐ ⟦ v0 {Γ = Γ} {μ = μ} {x} {T} ⟧tm
v0-sound Γ μ x T =
  begin
    dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩))
  ≅⟨ M.cl-tm-subst-id (ty-closed-natural T) _ ⟨
    dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩))
      M.[ ty-closed-natural T ∣ M.id-subst _ ]cl
  ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (DRA.key-subst-eq (⟦id-cell⟧-sound μ)) ⟨
    dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩))
      M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ id-cell {μ = μ} ⟧two-cell ]cl
  ≅⟨ M.cl-tm-subst-id (ty-closed-natural T) _ ⟨
    dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩))
      M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ id-cell {μ = μ} ⟧two-cell ]cl
      M.[ ty-closed-natural T ∣ M.id-subst _ ]cl ∎
  where open M.≅ᵗᵐ-Reasoning
