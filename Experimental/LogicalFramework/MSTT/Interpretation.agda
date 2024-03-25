--------------------------------------------------
-- Interpretation of MSTT terms and substitutions in a presheaf model
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics using (TmExtSem)

module Experimental.LogicalFramework.MSTT.Interpretation
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯) (⟦𝓉⟧ : TmExtSem ℳ 𝒯 𝓉)
  where

open import Data.List
open import Data.Product

open ModeTheory ℳ
open TmExtSem ⟦𝓉⟧

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.DRA as DRA hiding (⟨_∣_⟩; 𝟙; _,lock⟨_⟩)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Constant as M

open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics ℳ 𝒯 hiding (TmExtSem)
open import Experimental.LogicalFramework.MSTT.Syntax ℳ 𝒯 𝓉

private variable
  m n : Mode
  Γ Δ : Ctx m
  T S : Ty m
  x : Name


--------------------------------------------------
-- Reexporting interpretation of types and contexts

open import Experimental.LogicalFramework.MSTT.Interpretation.TypeContext ℳ 𝒯 public


--------------------------------------------------
-- Interpretation of terms

⟦_⟧var : {x : Name} {T : Ty n} {Γ : Ctx m} {Λ : LockTele m n} →
         Var x T Γ Λ →
         SemTm (⟦ Γ ⟧ctx DRA.,lock⟨ ⟦ locksˡᵗ Λ ⟧mod ⟩) ⟦ T ⟧ty
⟦_⟧var {T = T} (vzero {μ = μ} α) =
  (dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩)))
    M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
⟦_⟧var {T = T} {Λ = Λ} (vsuc v) =
  ⟦ v ⟧var M.[ ty-closed-natural T ∣ lock-fmap ⟦ locksˡᵗ Λ ⟧mod M.π ]cl
⟦_⟧var {T = T} (vlock {ρ = ρ} {Λ = Λ} v) =
  ⟦ v ⟧var M.[ ty-closed-natural T ∣ M.to (DRA.lock-iso (⟦ⓜ⟧-sound ρ (locksˡᵗ Λ))) ]cl

⟦_⟧tm : Tm Γ T → SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty
apply-sem-tm-constructor : ∀ {arginfos} → SemTmConstructor arginfos Γ T → ExtTmArgs arginfos Γ → SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty

⟦ var' _ {v} ⟧tm = ⟦ v ⟧var
⟦ mod⟨ μ ⟩ t ⟧tm = dra-intro ⟦ μ ⟧mod ⟦ t ⟧tm
⟦ mod-elim {T = T} {S = S} ρ μ _ t s ⟧tm =
  dra-let ⟦ ρ ⟧mod ⟦ μ ⟧mod (ty-closed-natural T) (ty-closed-natural S)
          ⟦ t ⟧tm
          (⟦ s ⟧tm M.[ ty-closed-natural S ∣ M.to (M.,,-cong (eq-dra-ty-closed (⟦ⓜ⟧-sound ρ μ) (ty-closed-natural T))) ]cl)
⟦ lam[_∣_∈_]_ {S = S} _ _ _ t ⟧tm = M.lamcl (ty-closed-natural S) ⟦ t ⟧tm
⟦ _∙_ {μ = μ} f t ⟧tm = M.app ⟦ f ⟧tm (dra-intro ⟦ μ ⟧mod ⟦ t ⟧tm)
⟦ zero ⟧tm = M.zero'
⟦ suc n ⟧tm = M.suc' ⟦ n ⟧tm
⟦ nat-rec a f n ⟧tm = M.nat-rec _ ⟦ a ⟧tm ⟦ f ⟧tm ⟦ n ⟧tm
⟦ true ⟧tm = M.true'
⟦ false ⟧tm = M.false'
⟦ if b t f ⟧tm = M.if' ⟦ b ⟧tm then' ⟦ t ⟧tm else' ⟦ f ⟧tm
⟦ pair t s ⟧tm = M.pair ⟦ t ⟧tm ⟦ s ⟧tm
⟦ fst p ⟧tm = M.fst ⟦ p ⟧tm
⟦ snd p ⟧tm = M.snd ⟦ p ⟧tm
⟦ ext c args refl ⟧tm = apply-sem-tm-constructor ⟦ c ⟧tm-code args

apply-sem-tm-constructor {arginfos = []}    t args         = t
apply-sem-tm-constructor {arginfos = _ ∷ _} f (arg , args) =
  apply-sem-tm-constructor (f ⟦ arg ⟧tm) args


--------------------------------------------------
-- Interpretation of renamings and substitutions as presheaf morphisms

,ˡᵗ-sound : {Γ : Ctx m} (Λ : LockTele m n) → ⟦ Γ ,ˡᵗ Λ ⟧ctx M.≅ᶜ DRA.lock ⟦ locksˡᵗ Λ ⟧mod ⟦ Γ ⟧ctx
,ˡᵗ-sound {m} ◇ = M.reflᶜ
,ˡᵗ-sound (lock⟨ μ ⟩, Λ) =
  M.transᶜ (,ˡᵗ-sound Λ) (M.symᶜ (lock-iso (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))))

⟦_⟧asub : AtomicSub Δ Γ → (⟦ Δ ⟧ctx M.⇒ ⟦ Γ ⟧ctx)
⟦ []ᵃˢ ⟧asub = M.!◇ _
⟦ idᵃˢ ⟧asub = M.id-subst _
⟦ _∷ᵃˢ_/_ {μ = μ} {T = T} σ t x ⟧asub = ⟦ σ ⟧asub M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ (dra-intro ⟦ μ ⟧mod ⟦ t ⟧tm)
⟦ σ ⊚πᵃˢ ⟧asub = ⟦ σ ⟧asub M.⊚ M.π
⟦ σ ,lockᵃˢ⟨ μ ⟩ ⟧asub = lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧asub
⟦ keyᵃˢ Λ₁ Λ₂ α ⟧asub =
  M.to (,ˡᵗ-sound Λ₂)
  M.⊚ (DRA.key-subst ⟦ α ⟧two-cell)
  M.⊚ M.from (,ˡᵗ-sound Λ₁)

⟦_⟧sub : Sub Δ Γ → (⟦ Δ ⟧ctx M.⇒ ⟦ Γ ⟧ctx)
⟦ idˢ ⟧sub = M.id-subst _
⟦ idˢ ⊚a τᵃ ⟧sub = ⟦ τᵃ ⟧asub
⟦ σ   ⊚a τᵃ ⟧sub = ⟦ σ ⟧sub M.⊚ ⟦ τᵃ ⟧asub

⟦_⟧aren : AtomicRen Δ Γ → (⟦ Δ ⟧ctx M.⇒ ⟦ Γ ⟧ctx)
⟦ []ᵃʳ ⟧aren = M.!◇ _
⟦ idᵃʳ ⟧aren = M.id-subst _
⟦ _∷ᵃʳ_/_ {μ = μ} {T = T} σ (somevar v) x ⟧aren =
  ⟦ σ ⟧aren M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ (dra-intro ⟦ μ ⟧mod ⟦ v ⟧var)
⟦ σ ⊚πᵃʳ ⟧aren = ⟦ σ ⟧aren M.⊚ M.π
⟦ σ ,lockᵃʳ⟨ μ ⟩ ⟧aren = lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧aren
⟦ keyᵃʳ Λ₁ Λ₂ α ⟧aren =
  M.to (,ˡᵗ-sound Λ₂)
  M.⊚ (DRA.key-subst ⟦ α ⟧two-cell)
  M.⊚ M.from (,ˡᵗ-sound Λ₁)

⟦_⟧ren : Ren Δ Γ → (⟦ Δ ⟧ctx M.⇒ ⟦ Γ ⟧ctx)
⟦ idʳ ⟧ren = M.id-subst _
⟦ idʳ ⊚a σ ⟧ren = ⟦ σ ⟧aren
⟦ σs  ⊚a σ ⟧ren = ⟦ σs ⟧ren M.⊚ ⟦ σ ⟧aren
