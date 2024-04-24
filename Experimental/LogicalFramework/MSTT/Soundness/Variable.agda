open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.MSTT.Soundness.Variable
  (𝒫 : MSTT-Parameter)
  where

import Relation.Binary.PropositionalEquality as Ag
import Relation.Binary.PropositionalEquality.Properties as Ag

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.DRA as DRA hiding
  (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; lock-fmap; lock-fmap-cong; lock-fmap-id; lock-fmap-⊚
  ; TwoCell; id-cell; _ⓣ-vert_; _ⓣ-hor_; key-subst; key-subst-natural; key-subst-eq)

open MSTT-Parameter 𝒫
open import Experimental.LogicalFramework.MSTT 𝒫

private variable
  m n o p : Mode


v0-sound : (Γ : Ctx n) (μ : Modality m n) (x : Name) (T : Ty m) →
           dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩)) M.≅ᵗᵐ ⟦ v0 {Γ = Γ} {μ = μ} {x} {T} ⟧tm
v0-sound Γ μ x T =
  begin
    dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩))
  ≅⟨ M.cl-tm-subst-id (ty-closed-natural T) _ ⟨
    dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩))
      M.[ ty-closed-natural T ∣ M.id-subst _ ]cl
  ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (DRA.key-subst-eq ⟦id-cell⟧-sound) ⟨
    dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩))
      M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ id-cell {μ = μ} ⟧two-cell ]cl
  ≅⟨ M.cl-tm-subst-id (ty-closed-natural T) _ ⟨
    dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩))
      M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ id-cell {μ = μ} ⟧two-cell ]cl
      M.[ ty-closed-natural T ∣ M.id-subst _ ]cl ∎
  where open M.≅ᵗᵐ-Reasoning


⟦eq-cell-++ˡᵗ-locks⟧ : (μ : Modality m p) (Λ : LockTele m n) {Θ : LockTele n o} →
                       ⟦ eq-cell (++ˡᵗ-locks (lock⟨ μ ⟩, Λ) {Θ}) ⟧two-cell
                         DRA.≅ᵗᶜ
                       ⟦ id-cell ⓣ-hor eq-cell (++ˡᵗ-locks Λ) ⟧two-cell DRA.ⓣ-vert ⟦ eq-cell (mod-assoc (locksˡᵗ Θ)) ⟧two-cell
⟦eq-cell-++ˡᵗ-locks⟧ μ Λ {Θ} =
  begin
    ⟦ eq-cell (Ag.trans (mod-assoc (locksˡᵗ Θ)) (Ag.cong (μ ⓜ_) (++ˡᵗ-locks Λ))) ⟧two-cell
  ≅⟨ ⟦eq-cell-trans⟧ (mod-assoc (locksˡᵗ Θ)) _ ⟩
    ⟦ eq-cell (Ag.cong (μ ⓜ_) (++ˡᵗ-locks Λ)) ⟧two-cell DRA.ⓣ-vert ⟦ eq-cell (mod-assoc (locksˡᵗ Θ)) ⟧two-cell
  ≅⟨ DRA.ⓣ-vert-congˡ (⟦eq-cell-whisker-left⟧ μ (++ˡᵗ-locks Λ)) ⟩
    ⟦ id-cell ⓣ-hor eq-cell (++ˡᵗ-locks Λ) ⟧two-cell DRA.ⓣ-vert ⟦ eq-cell (mod-assoc (locksˡᵗ Θ)) ⟧two-cell ∎
  where open DRA.≅ᵗᶜ-Reasoning

sym-trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} (e : x Ag.≡ y) {e' : y Ag.≡ z} →
            Ag.sym (Ag.trans e e') Ag.≡ Ag.trans (Ag.sym e') (Ag.sym e)
sym-trans Ag.refl {Ag.refl} = Ag.refl

-- We could prove this from ⟦eq-cell-++ˡᵗ-locks⟧ but proving it directly is easier.
⟦eq-cell-++ˡᵗ-sym-locks⟧ : (μ : Modality m p) (Λ : LockTele m n) {Θ : LockTele n o} →
                           ⟦ eq-cell (Ag.sym (++ˡᵗ-locks (lock⟨ μ ⟩, Λ) {Θ})) ⟧two-cell
                             DRA.≅ᵗᶜ
                           ⟦ eq-cell (Ag.sym (mod-assoc (locksˡᵗ Θ))) ⟧two-cell DRA.ⓣ-vert ⟦ id-cell ⓣ-hor eq-cell (Ag.sym (++ˡᵗ-locks Λ)) ⟧two-cell
⟦eq-cell-++ˡᵗ-sym-locks⟧ μ Λ {Θ} =
  begin
    ⟦ eq-cell (Ag.sym (Ag.trans (mod-assoc (locksˡᵗ Θ)) (Ag.cong (μ ⓜ_) (++ˡᵗ-locks Λ)))) ⟧two-cell
  ≅⟨ Ag.subst (λ e → ⟦ eq-cell (Ag.sym (Ag.trans (mod-assoc (locksˡᵗ Θ)) (Ag.cong (μ ⓜ_) (++ˡᵗ-locks Λ)))) ⟧two-cell DRA.≅ᵗᶜ ⟦ eq-cell e ⟧two-cell)
              {Ag.sym (Ag.trans (mod-assoc (locksˡᵗ Θ)) (Ag.cong (μ ⓜ_) (++ˡᵗ-locks Λ)))}
              (Ag.trans (sym-trans (mod-assoc (locksˡᵗ Θ))) (Ag.cong (λ x → Ag.trans x (Ag.sym (mod-assoc (locksˡᵗ Θ)))) (Ag.sym-cong (++ˡᵗ-locks Λ))))
              DRA.reflᵗᶜ ⟩
    ⟦ eq-cell (Ag.trans (Ag.cong (μ ⓜ_) (Ag.sym (++ˡᵗ-locks Λ))) (Ag.sym (mod-assoc (locksˡᵗ Θ)))) ⟧two-cell
  ≅⟨ ⟦eq-cell-trans⟧ (Ag.cong (μ ⓜ_) (Ag.sym (++ˡᵗ-locks Λ))) _ ⟩
    ⟦ eq-cell (Ag.sym (mod-assoc (locksˡᵗ Θ))) ⟧two-cell DRA.ⓣ-vert ⟦ eq-cell (Ag.cong (μ ⓜ_) (Ag.sym (++ˡᵗ-locks Λ))) ⟧two-cell
  ≅⟨ DRA.ⓣ-vert-congʳ (⟦eq-cell-whisker-left⟧ μ (Ag.sym (++ˡᵗ-locks Λ))) ⟩
    ⟦ eq-cell (Ag.sym (mod-assoc (locksˡᵗ Θ))) ⟧two-cell DRA.ⓣ-vert ⟦ id-cell ⓣ-hor eq-cell (Ag.sym (++ˡᵗ-locks Λ)) ⟧two-cell ∎
  where open DRA.≅ᵗᶜ-Reasoning


vlocks-sound : {x : Name} {T : Ty n} {Γ : Ctx o} (Θ : LockTele o m) {Λ : LockTele m n} →
               (v : Var x T Γ (Θ ++ˡᵗ Λ)) →
               ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ eq-cell (Ag.sym (++ˡᵗ-locks Θ)) ⟧two-cell M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ))) ]cl
                        M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.from (,ˡᵗ-sound Θ)) ]cl
                 M.≅ᵗᵐ
               ⟦ vlocks Θ v ⟧var
vlocks-sound {T = T} ◇ {Λ} v =
  begin
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ eq-cell (Ag.sym (mod-unitˡ {μ = locksˡᵗ Λ})) ⟧two-cell M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound 𝟙 (locksˡᵗ Λ))) ]cl
             M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.id-subst _) ]cl
  ≅⟨ M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural T) (DRA.lock-fmap-id ⟦ locksˡᵗ Λ ⟧mod)) (M.cl-tm-subst-id (ty-closed-natural T) _) ⟩
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ eq-cell (Ag.sym (mod-unitˡ {μ = locksˡᵗ Λ})) ⟧two-cell M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound 𝟙 (locksˡᵗ Λ))) ]cl
  ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T)
      (M.transˢ (M.⊚-congˡ (DRA.key-subst-eq ⟦unitorˡ-sym⟧))
      (M.transˢ M.⊚-assoc (M.transˢ (M.⊚-congʳ (DRA.key-subst-eq (isoʳ (⟦ⓜ⟧-sound 𝟙 (locksˡᵗ Λ))))) (M.id-subst-unitʳ _)))) ⟩
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ M.id-subst _ ]cl
  ≅⟨ M.cl-tm-subst-id (ty-closed-natural T) _ ⟩
    ⟦ v ⟧var ∎
  where open M.≅ᵗᵐ-Reasoning
vlocks-sound {T = T} (lock⟨ μ ⟩, Θ) {Λ} v =
  begin
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ eq-cell (Ag.sym (++ˡᵗ-locks (LockTele.lock⟨ μ ⟩, Θ))) ⟧two-cell
                                       M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound (μ ⓜ locksˡᵗ Θ) (locksˡᵗ Λ))) ]cl
             M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (DRA.key-subst (from (⟦ⓜ⟧-sound μ (locksˡᵗ Θ))) M.⊚ M.from (,ˡᵗ-sound Θ)) ]cl
  ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-subst (ty-closed-natural T) (M.⊚-congˡ (DRA.key-subst-eq (⟦eq-cell-++ˡᵗ-sym-locks⟧ μ Θ)))) ⟩
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ id-cell {μ = μ} ⓣ-hor eq-cell (Ag.sym (++ˡᵗ-locks Θ)) ⟧two-cell
                                       M.⊚ DRA.key-subst ⟦ eq-cell (Ag.sym (mod-assoc (locksˡᵗ Λ))) ⟧two-cell
                                       M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound (μ ⓜ locksˡᵗ Θ) (locksˡᵗ Λ))) ]cl
             M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (DRA.key-subst (from (⟦ⓜ⟧-sound μ (locksˡᵗ Θ))) M.⊚ M.from (,ˡᵗ-sound Θ)) ]cl
  ≅⟨ M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural T) (M.transˢ (M.⊚-congʳ (DRA.lock-fmap-⊚ ⟦ locksˡᵗ Λ ⟧mod _ _)) (M.transˢ (M.symˢ M.⊚-assoc) (M.⊚-congˡ (M.transˢ (M.transˢ (M.⊚-congˡ M.⊚-assoc) M.⊚-assoc) (M.⊚-congʳ (⟦associator-sym-key⟧ (locksˡᵗ Λ))))))) ⟩
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ id-cell ⓣ-hor eq-cell (Ag.sym (++ˡᵗ-locks Θ)) ⟧two-cell
                                       M.⊚ (DRA.key-subst (from (⟦ⓜ⟧-sound μ (locksˡᵗ Θ ⓜ locksˡᵗ Λ)))
                                       M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ)))) ]cl
             M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.from (,ˡᵗ-sound Θ)) ]cl
  ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (M.cl-tm-subst-cong-subst-2-1 (ty-closed-natural T) (
     M.transˢ (M.transˢ (M.symˢ M.⊚-assoc) (M.⊚-congˡ (M.symˢ (
     M.transˢ (DRA.key-subst-eq (⟦ⓜ⟧-sound-natural id-cell (eq-cell (Ag.sym (++ˡᵗ-locks Θ))))) (M.⊚-congʳ (
     M.transˢ (M.⊚-congʳ (M.transˢ (DRA.lock-fmap-cong ⟦ locksˡᵗ Θ ⓜ locksˡᵗ Λ ⟧mod (DRA.key-subst-eq ⟦id-cell⟧-sound)) (DRA.lock-fmap-id ⟦ locksˡᵗ Θ ⓜ locksˡᵗ Λ ⟧mod))) (
     M.id-subst-unitʳ _))))))) M.⊚-assoc)) ⟨
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst (from (⟦ⓜ⟧-sound μ (locksˡᵗ (Θ ++ˡᵗ Λ)))) ]cl
             M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ eq-cell (Ag.sym (++ˡᵗ-locks Θ)) ⟧two-cell
                                       M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ))) ]cl
             M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.from (,ˡᵗ-sound Θ)) ]cl
  ≅⟨ vlocks-sound Θ (vlock v) ⟩
    ⟦ vlocks Θ (vlock v) ⟧var ∎
  where open M.≅ᵗᵐ-Reasoning

unvlock-sound : {x : Name} {T : Ty n} {Γ : Ctx o} {μ : Modality m o} {Λ : LockTele m n}
                (v : Var x T (Γ ,lock⟨ μ ⟩) Λ) →
                ⟦ v ⟧var M.[ ty-closed-natural T ∣ M.from (DRA.lock-iso (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))) ]cl
                  M.≅ᵗᵐ
                ⟦ unvlock v ⟧var
unvlock-sound {T = T} {μ = μ} {Λ} (vlock v) =
  begin
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ M.to (lock-iso (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))) ]cl
             M.[ ty-closed-natural T ∣ M.from (lock-iso (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))) ]cl
  ≅⟨ M.cl-tm-subst-cong-subst-2-1 (ty-closed-natural T) (M.isoˡ (lock-iso (⟦ⓜ⟧-sound μ (locksˡᵗ Λ)))) ⟩
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ M.id-subst _ ]cl
  ≅⟨ M.cl-tm-subst-id (ty-closed-natural T) _ ⟩
    ⟦ v ⟧var ∎
  where open M.≅ᵗᵐ-Reasoning

unvlocks-sound : {x : Name} {T : Ty n} {Γ : Ctx o} (Θ : LockTele o m) {Λ : LockTele m n} →
                 (v : Var x T (Γ ,ˡᵗ Θ) Λ) →
                 ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.to (,ˡᵗ-sound Θ)) ]cl
                          M.[ ty-closed-natural T ∣ DRA.key-subst (to (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ))) M.⊚ DRA.key-subst ⟦ eq-cell (++ˡᵗ-locks Θ {Λ}) ⟧two-cell ]cl
                   M.≅ᵗᵐ
                 ⟦ unvlocks Θ v ⟧var
unvlocks-sound {T = T} ◇ {Λ} v =
  begin
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.id-subst _) ]cl
             M.[ ty-closed-natural T ∣ DRA.key-subst (to (⟦ⓜ⟧-sound 𝟙 (locksˡᵗ Λ))) M.⊚ DRA.key-subst ⟦ eq-cell (mod-unitˡ {μ = locksˡᵗ Λ}) ⟧two-cell ]cl
  ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T)
       (M.transˢ (M.⊚-congʳ (DRA.key-subst-eq ⟦unitorˡ⟧)) (M.transˢ (M.symˢ M.⊚-assoc)
       (M.transˢ (M.⊚-congˡ (DRA.key-subst-eq (isoʳ (⟦ⓜ⟧-sound 𝟙 (locksˡᵗ Λ))))) (M.id-subst-unitˡ _)))) ⟩
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.id-subst _) ]cl
             M.[ ty-closed-natural T ∣ M.id-subst _ ]cl
  ≅⟨ M.cl-tm-subst-id (ty-closed-natural T) _ ⟩
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.id-subst _) ]cl
  ≅⟨ M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural T) (DRA.lock-fmap-id ⟦ locksˡᵗ Λ ⟧mod)) (M.cl-tm-subst-id (ty-closed-natural T) _) ⟩
    ⟦ v ⟧var ∎
  where open M.≅ᵗᵐ-Reasoning
unvlocks-sound {T = T} (lock⟨ μ ⟩, Θ) {Λ} v =
  begin
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.to (,ˡᵗ-sound Θ) M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Θ)))) ]cl
             M.[ ty-closed-natural T ∣ DRA.key-subst (to (⟦ⓜ⟧-sound (μ ⓜ locksˡᵗ Θ) (locksˡᵗ Λ)))
                                       M.⊚ DRA.key-subst ⟦ eq-cell (++ˡᵗ-locks (LockTele.lock⟨ μ ⟩, Θ)) ⟧two-cell ]cl
  ≅⟨ M.cl-tm-subst-cong-subst (ty-closed-natural T) (M.⊚-congʳ (DRA.key-subst-eq (⟦eq-cell-++ˡᵗ-locks⟧ μ Θ))) ⟩
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.to (,ˡᵗ-sound Θ) M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Θ)))) ]cl
             M.[ ty-closed-natural T ∣ DRA.key-subst (to (⟦ⓜ⟧-sound (μ ⓜ locksˡᵗ Θ) (locksˡᵗ Λ)))
                                       M.⊚ (DRA.key-subst ⟦ eq-cell (mod-assoc (locksˡᵗ Λ)) ⟧two-cell
                                       M.⊚ DRA.key-subst ⟦ id-cell ⓣ-hor eq-cell (++ˡᵗ-locks Θ) ⟧two-cell) ]cl
  ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (
       M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural T) (DRA.lock-fmap-⊚ ⟦ locksˡᵗ Λ ⟧mod _ _))
                 (M.symᵗᵐ (M.cl-tm-subst-⊚ (ty-closed-natural T) _))) ⟩
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.to (,ˡᵗ-sound Θ)) ]cl
             M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (DRA.key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Θ)))) ]cl
             M.[ ty-closed-natural T ∣ DRA.key-subst (to (⟦ⓜ⟧-sound (μ ⓜ locksˡᵗ Θ) (locksˡᵗ Λ)))
                                       M.⊚ (DRA.key-subst ⟦ eq-cell (mod-assoc (locksˡᵗ Λ)) ⟧two-cell
                                       M.⊚ DRA.key-subst ⟦ id-cell ⓣ-hor eq-cell (++ˡᵗ-locks Θ) ⟧two-cell) ]cl
  ≅⟨ M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural T) (
     M.transˢ (M.transˢ (M.symˢ M.⊚-assoc) (M.transˢ (M.symˢ M.⊚-assoc) (M.⊚-congˡ (⟦associator-key-to⟧ (locksˡᵗ Λ))))) M.⊚-assoc) ⟩
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.to (,ˡᵗ-sound Θ)) ]cl
             M.[ ty-closed-natural T ∣ DRA.key-subst (to (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ))) ]cl
             M.[ ty-closed-natural T ∣ DRA.key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ Θ ⓜ locksˡᵗ Λ)))
                                       M.⊚ DRA.key-subst ⟦ id-cell ⓣ-hor eq-cell (++ˡᵗ-locks Θ) ⟧two-cell ]cl
  ≅⟨ M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural T) (
     M.transˢ (M.⊚-congʳ (M.transˢ (DRA.key-subst-eq (⟦ⓜ⟧-sound-natural-to id-cell (eq-cell (++ˡᵗ-locks Θ)))) (
     M.⊚-congˡ (M.transˢ (M.⊚-congʳ (M.transˢ (DRA.lock-fmap-cong ⟦ locksˡᵗ (Θ ++ˡᵗ Λ) ⟧mod (DRA.key-subst-eq ⟦id-cell⟧-sound)) (
     DRA.lock-fmap-id ⟦ locksˡᵗ (Θ ++ˡᵗ Λ) ⟧mod))) (M.id-subst-unitʳ _))))) (M.symˢ M.⊚-assoc)) ⟩
    ⟦ v ⟧var M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.to (,ˡᵗ-sound Θ)) ]cl
             M.[ ty-closed-natural T ∣ DRA.key-subst (to (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ)))
                                       M.⊚ DRA.key-subst ⟦ eq-cell (++ˡᵗ-locks Θ) ⟧two-cell ]cl
             M.[ ty-closed-natural T ∣ DRA.key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ (Θ ++ˡᵗ Λ)))) ]cl
  ≅⟨ M.cl-tm-subst-cong-tm (ty-closed-natural T) (unvlocks-sound Θ v) ⟩
    ⟦ unvlocks Θ v ⟧var M.[ ty-closed-natural T ∣ DRA.key-subst (to (⟦ⓜ⟧-sound μ (locksˡᵗ (Θ ++ˡᵗ Λ)))) ]cl
  ≅⟨ unvlock-sound (unvlocks Θ v) ⟩
    ⟦ unvlock (unvlocks Θ v) ⟧var ∎
  where open M.≅ᵗᵐ-Reasoning
