--------------------------------------------------
-- Interpretation of nameless MSTT types, contexts and terms in a
--   presheaf model
--------------------------------------------------

module Experimental.LogicalFramework.MSTT.Interpretation.Nameless where

open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory
open import Model.CwF-Structure as M
  renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Discrete as M
import Model.Modality as M

open import Experimental.ClosedTypes as M
open import Experimental.ClosedTypes.Modal as M

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
⟦ T ⇛ S ⟧ty = ⟦ T ⟧ty M.⇛ ⟦ S ⟧ty
⟦ T ⊠ S ⟧ty = ⟦ T ⟧ty M.⊠ ⟦ S ⟧ty
⟦ ⟨ μ ∣ T ⟩ ⟧ty = M.s⟨ ⟦ μ ⟧mod ∣ ⟦ T ⟧ty ⟩

⟦_⟧ctx-nmls : Ctx m → SemCtx ⟦ m ⟧mode
⟦ ◇ ⟧ctx-nmls = M.◇
⟦ Γ ,, μ ∣ _ ∈ T ⟧ctx-nmls = ⟦ Γ ⟧ctx-nmls ,,ₛ M.s⟨ ⟦ μ ⟧mod ∣ ⟦ T ⟧ty ⟩
⟦ Γ ,lock⟨ μ ⟩ ⟧ctx-nmls = M.lock ⟦ μ ⟧mod ⟦ Γ ⟧ctx-nmls

⟦⟧var-helper : {Γ : Ctx m} {μ : Modality n o} {κ : Modality m o} (v : Var _ μ T κ Γ) →
               (ρ : Modality n m) → TwoCell μ (κ ⓜ ρ) → SimpleTm ⟦ Γ ,lock⟨ ρ ⟩ ⟧ctx-nmls ⟦ T ⟧ty
⟦⟧var-helper {μ = μ} vzero ρ α =
  (smod-elim ⟦ μ ⟧mod sξ) M.[ M.transf-op (M.transf ⟦ subst (TwoCell _) mod-unitˡ α ⟧two-cell) _ ]s
⟦⟧var-helper (vsuc v) ρ α = (⟦⟧var-helper v ρ α) M.[ M.lock-fmap ⟦ ρ ⟧mod M.π ]s
⟦⟧var-helper (skip-lock {κ = κ} φ v) ρ α =
  (⟦⟧var-helper v (φ ⓜ ρ) (subst (TwoCell _) (mod-assoc {μ = κ}) α)) M.[ M.to (M.eq-lock (⟦ⓜ⟧-sound φ ρ) _) ]s

⟦_,_⟧var-nmls : {μ κ : Modality m n} → (v : Var _ μ T κ Γ) → TwoCell μ κ → SimpleTm ⟦ Γ ⟧ctx-nmls ⟦ T ⟧ty
⟦_,_⟧var-nmls {m = m} v α = (⟦⟧var-helper v 𝟙 (subst (TwoCell _) (sym mod-unitʳ) α)) M.[ M.to (M.eq-lock (⟦𝟙⟧-sound {m}) _) ]s

⟦_⟧tm-nmls : Tm Γ T → SimpleTm ⟦ Γ ⟧ctx-nmls ⟦ T ⟧ty
⟦ var' _ {v} α ⟧tm-nmls = ⟦ v , α ⟧var-nmls
⟦ mod⟨ μ ⟩ t ⟧tm-nmls = smod-intro ⟦ μ ⟧mod ⟦ t ⟧tm-nmls
⟦ mod-elim ρ μ _ t s ⟧tm-nmls =
  smtt-mod-elim ⟦ ρ ⟧mod ⟦ μ ⟧mod ⟦ t ⟧tm-nmls (⟦ s ⟧tm-nmls [ M.to (M.,,ₛ-cong (seq-mod _ (⟦ⓜ⟧-sound ρ μ))) ]s)
⟦ lam[_∈_]_ _ _ t ⟧tm-nmls =
  -- The following let binding is only necessary because Agda cannot
  -- infer the mode in ⟦𝟙⟧sound, and we cannot introduce the mode in
  -- the LHS because it is a parameter and not an index in the
  -- definition of the syntax.
  let m = _
      ⟦t⟧ = ⟦_⟧tm-nmls {m} t
  in
  sλ[ _ ] (⟦t⟧ M.[ M.to (M.,,ₛ-cong (M.≅ᵗʸ-trans (seq-mod _ (⟦𝟙⟧-sound {m})) M.s⟨𝟙∣-⟩)) ]s)
⟦ f ∙ t ⟧tm-nmls = ⟦ f ⟧tm-nmls ∙ₛ ⟦ t ⟧tm-nmls
⟦ zero ⟧tm-nmls = szero
⟦ suc ⟧tm-nmls = ssuc
⟦ nat-elim a f ⟧tm-nmls = snat-elim ⟦ a ⟧tm-nmls ⟦ f ⟧tm-nmls
⟦ true ⟧tm-nmls = strue
⟦ false ⟧tm-nmls = sfalse
⟦ if b t f ⟧tm-nmls = sif ⟦ b ⟧tm-nmls ⟦ t ⟧tm-nmls ⟦ f ⟧tm-nmls
⟦ pair t s ⟧tm-nmls = spair ⟦ t ⟧tm-nmls ⟦ s ⟧tm-nmls
⟦ fst p ⟧tm-nmls = sfst ⟦ p ⟧tm-nmls
⟦ snd p ⟧tm-nmls = ssnd ⟦ p ⟧tm-nmls
