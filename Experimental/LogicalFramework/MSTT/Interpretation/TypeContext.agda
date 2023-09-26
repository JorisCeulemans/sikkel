open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension using (TyExt)

module Experimental.LogicalFramework.MSTT.Interpretation.TypeContext
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ)
  where

open import Data.List
open import Data.Product
open import Data.Unit

open ModeTheory ℳ
open TyExt 𝒯
open Experimental.LogicalFramework.MSTT.Parameter.TypeExtension ℳ

open import Model.CwF-Structure as M
  renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.CwF-Structure.ClosedType
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Constant as M
import Model.Modality as M

open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯 ⊤

private variable
  m n o : Mode
  μ κ : Modality m n
  Γ : Ctx m
  T : Ty m


⟦_⟧ty : Ty m → ClosedTy ⟦ m ⟧mode
apply-sem-ty-constructor : ∀ {margs} → SemTyConstructor margs m → TyExtArgs margs → ClosedTy ⟦ m ⟧mode

⟦ Nat' ⟧ty = M.Nat'
⟦ Bool' ⟧ty = M.Bool'
⟦ ⟨ μ ∣ T ⟩⇛ S ⟧ty = M.⟨ ⟦ μ ⟧mod ∣ ⟦ T ⟧ty ⟩ M.⇛ ⟦ S ⟧ty
⟦ T ⊠ S ⟧ty = ⟦ T ⟧ty M.⊠ ⟦ S ⟧ty
⟦ ⟨ μ ∣ T ⟩ ⟧ty = M.⟨ ⟦ μ ⟧mod ∣ ⟦ T ⟧ty ⟩
⟦ Ext c Args ⟧ty = apply-sem-ty-constructor ⟦ c ⟧ty-code Args

apply-sem-ty-constructor {margs = []}        T Args       = T
apply-sem-ty-constructor {margs = m ∷ margs} F (A , Args) = apply-sem-ty-constructor (F ⟦ A ⟧ty) Args


ty-closed-natural : (T : Ty m) → IsClosedNatural ⟦ T ⟧ty
ext-ty-natural : ∀{margs} {F : SemTyConstructor margs m} → SemTyConstructorNatural F → (args : TyExtArgs margs) →
                 IsClosedNatural (apply-sem-ty-constructor F args)

ty-closed-natural Nat' = M.const-closed
ty-closed-natural Bool' = M.const-closed
ty-closed-natural (⟨ μ ∣ T ⟩⇛ S) = M.fun-closed (M.dra-closed ⟦ μ ⟧mod (ty-closed-natural T)) (ty-closed-natural S)
ty-closed-natural (T ⊠ S) = M.prod-closed (ty-closed-natural T) (ty-closed-natural S)
ty-closed-natural ⟨ μ ∣ T ⟩ = M.dra-closed ⟦ μ ⟧mod (ty-closed-natural T)
ty-closed-natural (Ext c Args) = ext-ty-natural (sem-ty-code-natural c) Args

ext-ty-natural {margs = []}        nat Args       = nat
ext-ty-natural {margs = m ∷ margs} nat (A , Args) = ext-ty-natural (nat (ty-closed-natural A)) Args


ty-natural : (T : Ty m) {Γ Δ : SemCtx ⟦ m ⟧mode} {σ : Γ M.⇒ Δ} → ⟦ T ⟧ty M.[ σ ] M.≅ᵗʸ ⟦ T ⟧ty
ty-natural T = closed-natural (ty-closed-natural T) _

⟦_⟧ctx-nmls : Ctx m → SemCtx ⟦ m ⟧mode
⟦ ◇ ⟧ctx-nmls = M.◇
⟦ Γ ,, μ ∣ _ ∈ T ⟧ctx-nmls = ⟦ Γ ⟧ctx-nmls M.,, M.⟨ ⟦ μ ⟧mod ∣ ⟦ T ⟧ty ⟩
⟦ Γ ,lock⟨ μ ⟩ ⟧ctx-nmls = M.lock ⟦ μ ⟧mod ⟦ Γ ⟧ctx-nmls
