--------------------------------------------------
-- Interpretation of nameless MSTT types, contexts and terms in a
--   presheaf model
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Interpretation.ModeTheory

module Experimental.LogicalFramework.MSTT.Interpretation.Nameless
  (ℳ : ModeTheory) (⟦ℳ⟧ : ModeTheoryInterpretation ℳ)
  where

open import Relation.Binary.PropositionalEquality

open ModeTheory ℳ
open ModeTheoryInterpretation ⟦ℳ⟧

open import Model.BaseCategory
open import Model.CwF-Structure as M
  renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.CwF-Structure.ClosedType
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Constant as M
import Model.Modality as M

open import Experimental.LogicalFramework.MSTT.Syntax.Nameless ℳ
open import Experimental.LogicalFramework.MSTT.AlphaEquivalence ℳ

private variable
  m n o : Mode
  μ κ : Modality m n
  Γ : Ctx m
  T : Ty m


⟦_⟧ty : Ty m → ClosedTy ⟦ m ⟧mode
⟦ Nat' ⟧ty = M.Nat'
⟦ Bool' ⟧ty = M.Bool'
⟦ ⟨ μ ∣ T ⟩⇛ S ⟧ty = M.⟨ ⟦ μ ⟧mod ∣ ⟦ T ⟧ty ⟩ M.⇛ ⟦ S ⟧ty
⟦ T ⊠ S ⟧ty = ⟦ T ⟧ty M.⊠ ⟦ S ⟧ty
⟦ ⟨ μ ∣ T ⟩ ⟧ty = M.⟨ ⟦ μ ⟧mod ∣ ⟦ T ⟧ty ⟩

ty-closed-natural : (T : Ty m) → IsClosedNatural ⟦ T ⟧ty
ty-closed-natural Nat' = M.const-closed
ty-closed-natural Bool' = M.const-closed
ty-closed-natural (⟨ μ ∣ T ⟩⇛ S) = M.fun-closed (M.mod-closed ⟦ μ ⟧mod (ty-closed-natural T)) (ty-closed-natural S)
ty-closed-natural (T ⊠ S) = M.prod-closed (ty-closed-natural T) (ty-closed-natural S)
ty-closed-natural ⟨ μ ∣ T ⟩ = M.mod-closed ⟦ μ ⟧mod (ty-closed-natural T)

ty-natural : (T : Ty m) {Γ Δ : SemCtx ⟦ m ⟧mode} {σ : Γ M.⇒ Δ} → ⟦ T ⟧ty M.[ σ ] M.≅ᵗʸ ⟦ T ⟧ty
ty-natural T = closed-natural (ty-closed-natural T) _

⟦_⟧ctx-nmls : Ctx m → SemCtx ⟦ m ⟧mode
⟦ ◇ ⟧ctx-nmls = M.◇
⟦ Γ ,, μ ∣ _ ∈ T ⟧ctx-nmls = ⟦ Γ ⟧ctx-nmls M.,, M.⟨ ⟦ μ ⟧mod ∣ ⟦ T ⟧ty ⟩
⟦ Γ ,lock⟨ μ ⟩ ⟧ctx-nmls = M.lock ⟦ μ ⟧mod ⟦ Γ ⟧ctx-nmls

⟦⟧var-helper : {Γ : Ctx m} {μ : Modality n o} {κ : Modality m o} (v : Var _ μ T κ Γ) →
               (ρ : Modality n m) → TwoCell μ (κ ⓜ ρ) → SemTm ⟦ Γ ,lock⟨ ρ ⟩ ⟧ctx-nmls ⟦ T ⟧ty
⟦⟧var-helper {T = T} {μ = μ} vzero ρ α =
  (M.mod-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩)))
    M.[ ty-closed-natural T ∣ M.key-subst ⟦ α ⟧two-cell ]cl
⟦⟧var-helper {T = T} (vsuc v) ρ α = (⟦⟧var-helper v ρ α) M.[ ty-closed-natural T ∣ M.lock-fmap ⟦ ρ ⟧mod M.π ]cl
⟦⟧var-helper {T = T} (skip-lock {κ = κ} φ v) ρ α =
  (⟦⟧var-helper v (φ ⓜ ρ) (transp-cellʳ (mod-assoc κ) α)) M.[ ty-closed-natural T ∣ M.to (M.eq-lock (⟦ⓜ⟧-sound φ ρ) _) ]cl

⟦_,_⟧var-nmls : {μ κ : Modality m n} → (v : Var _ μ T κ Γ) → TwoCell μ κ → SemTm ⟦ Γ ⟧ctx-nmls ⟦ T ⟧ty
⟦_,_⟧var-nmls {m = m} {T = T} v α = ⟦⟧var-helper v 𝟙 (transp-cellʳ (sym mod-unitʳ) α)

⟦_⟧tm-nmls : Tm Γ T → SemTm ⟦ Γ ⟧ctx-nmls ⟦ T ⟧ty
⟦ var' _ {v} α ⟧tm-nmls = ⟦ v , α ⟧var-nmls
⟦ mod⟨ μ ⟩ t ⟧tm-nmls = M.mod-intro ⟦ μ ⟧mod ⟦ t ⟧tm-nmls
⟦ mod-elim {T = T} {S = S} ρ μ _ t s ⟧tm-nmls =
  ⟦ s ⟧tm-nmls M.[ ty-closed-natural S
                 ∣ M.tm-to-subst (M.ι[ M.eq-mod-closed (⟦ⓜ⟧-sound ρ μ) (ty-closed-natural T) ]
                                     M.mod-intro ⟦ ρ ⟧mod ⟦ t ⟧tm-nmls)
                 ]cl
⟦ lam[_∣_∈_]_ {S = S} _ _ _ t ⟧tm-nmls = M.lamcl (ty-closed-natural S) ⟦ t ⟧tm-nmls
⟦ _∙_ {μ = μ} f t ⟧tm-nmls = M.app ⟦ f ⟧tm-nmls (M.mod-intro ⟦ μ ⟧mod ⟦ t ⟧tm-nmls)
⟦ zero ⟧tm-nmls = M.zero'
⟦ suc n ⟧tm-nmls = M.suc' ⟦ n ⟧tm-nmls
⟦ nat-elim a f n ⟧tm-nmls = M.nat-elim _ ⟦ a ⟧tm-nmls ⟦ f ⟧tm-nmls ⟦ n ⟧tm-nmls
⟦ true ⟧tm-nmls = M.true'
⟦ false ⟧tm-nmls = M.false'
⟦ if b t f ⟧tm-nmls = M.if' ⟦ b ⟧tm-nmls then' ⟦ t ⟧tm-nmls else' ⟦ f ⟧tm-nmls
⟦ pair t s ⟧tm-nmls = M.pair ⟦ t ⟧tm-nmls ⟦ s ⟧tm-nmls
⟦ fst p ⟧tm-nmls = M.fst ⟦ p ⟧tm-nmls
⟦ snd p ⟧tm-nmls = M.snd ⟦ p ⟧tm-nmls
