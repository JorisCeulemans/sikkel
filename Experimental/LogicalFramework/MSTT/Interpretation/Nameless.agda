--------------------------------------------------
-- Interpretation of nameless MSTT types, contexts and terms in a
--   presheaf model
--------------------------------------------------

module Experimental.LogicalFramework.MSTT.Interpretation.Nameless where

open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory
open import Model.CwF-Structure as M
  renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.CwF-Structure.ClosedType
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Constant as M
import Model.Modality as M

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Syntax.Nameless
open import Experimental.LogicalFramework.MSTT.AlphaEquivalence
open import Experimental.LogicalFramework.MSTT.Interpretation.ModeTheory

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

-- When interpreting a variable v : Var _ μ T κ Γ in a context Γ, all
-- variables to the right of v are removed from Γ and all locks are
-- aggregated to a single modality (viz. κ).
record PruneResult (μ : Modality n o) (T : Ty n) (κ : Modality m o) (Γ : Ctx m) : Set where
  constructor prune-result
  field
    Γ-pre : Ctx o
    from-sub : ⟦ Γ ⟧ctx-nmls M.⇒ ⟦ Γ-pre ,, μ ∣ _ ∈ T ,lock⟨ κ ⟩ ⟧ctx-nmls

prune-ctx : (v : Var _ μ T κ Γ) → PruneResult μ T κ Γ
prune-ctx {Γ = Γ ,, μ ∣ _ ∈ T} vzero = prune-result Γ (M.id-subst _)
prune-ctx (vsuc v) =
  let prune-result Γ-pre from-sub = prune-ctx v
  in prune-result Γ-pre (from-sub M.⊚ M.π)
prune-ctx (skip-lock {κ = κ} ρ v) =
  let prune-result Γ-pre from-sub = prune-ctx v
  in prune-result Γ-pre (M.to (M.eq-lock (⟦ⓜ⟧-sound κ ρ) _) M.⊚ M.lock-fmap ⟦ ρ ⟧mod from-sub)

⟦_,_⟧var-nmls : (v : Var _ μ T κ Γ) (α : TwoCell μ κ) → SemTm ⟦ Γ ⟧ctx-nmls ⟦ T ⟧ty
⟦_,_⟧var-nmls {μ = μ} {T = T} v α =
  let prune-result Γ-pre from-sub = prune-ctx v
  in (M.mod-elim ⟦ μ ⟧mod (ξcl (ty-closed-natural ⟨ μ ∣ T ⟩))) [ ty-closed-natural T ∣ M.key-subst ⟦ α ⟧two-cell M.⊚ from-sub ]cl

⟦_⟧tm-nmls : Tm Γ T → SemTm ⟦ Γ ⟧ctx-nmls ⟦ T ⟧ty
⟦ var' _ {v} α ⟧tm-nmls = ⟦ v , α ⟧var-nmls
⟦ mod⟨ μ ⟩ t ⟧tm-nmls = M.mod-intro ⟦ μ ⟧mod ⟦ t ⟧tm-nmls
⟦ mod-elim {T = T} {S = S} ρ μ _ t s ⟧tm-nmls =
  ⟦ s ⟧tm-nmls M.[ ty-closed-natural S
                 ∣ M.term-to-subst (M.ι[ M.eq-mod-closed (⟦ⓜ⟧-sound ρ μ) (ty-closed-natural T) ]
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
