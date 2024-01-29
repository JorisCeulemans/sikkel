--------------------------------------------------
-- Interpretation of nameless MSTT types, contexts and terms in a
--   presheaf model
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension using (TyExt)
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension using (TmExt)
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics using (TmExtSem)
open import Data.Unit using (⊤)

module Experimental.LogicalFramework.MSTT.Interpretation.Nameless
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯 ⊤) (⟦𝓉⟧ : TmExtSem ℳ 𝒯 𝓉)
  where

open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality

open ModeTheory ℳ
open TyExt 𝒯
open TmExtSem ⟦𝓉⟧
open Experimental.LogicalFramework.MSTT.Parameter.TypeExtension ℳ
open Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics ℳ 𝒯

open import Model.CwF-Structure as M
  renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.CwF-Structure.ClosedType
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Constant as M
open import Model.DRA as DRA hiding (TwoCell; _,lock⟨_⟩; ⟨_∣_⟩; 𝟙)

open import Experimental.LogicalFramework.MSTT.Syntax.Nameless ℳ 𝒯 𝓉
open import Experimental.LogicalFramework.MSTT.Interpretation.TypeContext ℳ 𝒯

private variable
  m n o : Mode
  μ κ : Modality m n
  Γ : Ctx m
  T : Ty m


⟦⟧var-helper : {Γ : Ctx m} {μ : Modality n o} {κ : Modality m o} (v : Var _ μ T κ Γ) →
               (ρ : Modality n m) → TwoCell μ (κ ⓜ ρ) → SemTm ⟦ Γ ,lock⟨ ρ ⟩ ⟧ctx-nmls ⟦ T ⟧ty
⟦⟧var-helper {T = T} {μ = μ} vzero ρ α =
  (DRA.dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩)))
    M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
⟦⟧var-helper {T = T} (vsuc v) ρ α = (⟦⟧var-helper v ρ α) M.[ ty-closed-natural T ∣ lock-fmap ⟦ ρ ⟧mod M.π ]cl
⟦⟧var-helper {T = T} (skip-lock {κ = κ} φ v) ρ α =
  (⟦⟧var-helper v (φ ⓜ ρ) (transp-cellʳ (mod-assoc κ) α)) M.[ ty-closed-natural T ∣ M.to (DRA.lock-iso (⟦ⓜ⟧-sound φ ρ)) ]cl

⟦_,_⟧var-nmls : {μ κ : Modality m n} → (v : Var _ μ T κ Γ) → TwoCell μ κ → SemTm ⟦ Γ ⟧ctx-nmls ⟦ T ⟧ty
⟦_,_⟧var-nmls {m = m} {T = T} v α = ⟦⟧var-helper v 𝟙 (transp-cellʳ (sym mod-unitʳ) α)

⟦_⟧tm-nmls : Tm Γ T → SemTm ⟦ Γ ⟧ctx-nmls ⟦ T ⟧ty
apply-sem-tm-constructor : ∀ {arginfos} → SemTmConstructor arginfos Γ T → TmExtArgs arginfos Γ → SemTm ⟦ Γ ⟧ctx-nmls ⟦ T ⟧ty

⟦ var' _ {v} α ⟧tm-nmls = ⟦ v , α ⟧var-nmls
⟦ mod⟨ μ ⟩ t ⟧tm-nmls = dra-intro ⟦ μ ⟧mod ⟦ t ⟧tm-nmls
⟦ mod-elim {T = T} {S = S} ρ μ _ t s ⟧tm-nmls =
  ⟦ s ⟧tm-nmls M.[ ty-closed-natural S
                 ∣ M.tm-to-subst (M.ι[ eq-dra-ty-closed (⟦ⓜ⟧-sound ρ μ) (ty-closed-natural T) ]
                                     dra-intro ⟦ ρ ⟧mod ⟦ t ⟧tm-nmls)
                 ]cl
⟦ lam[_∣_∈_]_ {S = S} _ _ _ t ⟧tm-nmls = M.lamcl (ty-closed-natural S) ⟦ t ⟧tm-nmls
⟦ _∙_ {μ = μ} f t ⟧tm-nmls = M.app ⟦ f ⟧tm-nmls (dra-intro ⟦ μ ⟧mod ⟦ t ⟧tm-nmls)
⟦ zero ⟧tm-nmls = M.zero'
⟦ suc n ⟧tm-nmls = M.suc' ⟦ n ⟧tm-nmls
⟦ nat-rec a f n ⟧tm-nmls = M.nat-rec _ ⟦ a ⟧tm-nmls ⟦ f ⟧tm-nmls ⟦ n ⟧tm-nmls
⟦ true ⟧tm-nmls = M.true'
⟦ false ⟧tm-nmls = M.false'
⟦ if b t f ⟧tm-nmls = M.if' ⟦ b ⟧tm-nmls then' ⟦ t ⟧tm-nmls else' ⟦ f ⟧tm-nmls
⟦ pair t s ⟧tm-nmls = M.pair ⟦ t ⟧tm-nmls ⟦ s ⟧tm-nmls
⟦ fst p ⟧tm-nmls = M.fst ⟦ p ⟧tm-nmls
⟦ snd p ⟧tm-nmls = M.snd ⟦ p ⟧tm-nmls
⟦ ext c args refl ⟧tm-nmls = apply-sem-tm-constructor ⟦ c ⟧tm-code args

apply-sem-tm-constructor {arginfos = []}    t args         = t
apply-sem-tm-constructor {arginfos = _ ∷ _} f (arg , args) =
  apply-sem-tm-constructor (f ⟦ arg ⟧tm-nmls) args
