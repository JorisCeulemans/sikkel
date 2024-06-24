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
import Model.DRA as DRA

open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯

private variable
  m n o : Mode
  μ κ : Modality m n
  Γ : Ctx m
  T : Ty m


--------------------------------------------------
-- Interpretation of types

⟦_⟧ty : Ty m → ClosedTy ⟦ m ⟧mode
apply-sem-ty-constructor : ∀ {margs} → SemTyConstructor margs m → TyExtArgs margs → ClosedTy ⟦ m ⟧mode

⟦ Nat' ⟧ty = M.Nat'
⟦ Bool' ⟧ty = M.Bool'
⟦ ⟨ μ ∣ T ⟩⇛ S ⟧ty = DRA.⟨ ⟦ μ ⟧mod ∣ ⟦ T ⟧ty ⟩ M.⇛ ⟦ S ⟧ty
⟦ T ⊠ S ⟧ty = ⟦ T ⟧ty M.⊠ ⟦ S ⟧ty
⟦ ⟨ μ ∣ T ⟩ ⟧ty = DRA.⟨ ⟦ μ ⟧mod ∣ ⟦ T ⟧ty ⟩
⟦ Ext c Args ⟧ty = apply-sem-ty-constructor ⟦ c ⟧ty-code Args

apply-sem-ty-constructor {margs = []}        T Args       = T
apply-sem-ty-constructor {margs = m ∷ margs} F (A , Args) = apply-sem-ty-constructor (F ⟦ A ⟧ty) Args


ty-closed-natural : (T : Ty m) → IsClosedNatural ⟦ T ⟧ty
ext-ty-natural : ∀{margs} {F : SemTyConstructor margs m} → SemTyConstructorNatural F → (args : TyExtArgs margs) →
                 IsClosedNatural (apply-sem-ty-constructor F args)

ty-closed-natural Nat' = M.const-closed
ty-closed-natural Bool' = M.const-closed
ty-closed-natural (⟨ μ ∣ T ⟩⇛ S) = M.fun-closed (DRA.dra-closed ⟦ μ ⟧mod (ty-closed-natural T)) (ty-closed-natural S)
ty-closed-natural (T ⊠ S) = M.prod-closed (ty-closed-natural T) (ty-closed-natural S)
ty-closed-natural ⟨ μ ∣ T ⟩ = DRA.dra-closed ⟦ μ ⟧mod (ty-closed-natural T)
ty-closed-natural (Ext c Args) = ext-ty-natural (sem-ty-code-natural c) Args

ext-ty-natural {margs = []}        nat Args       = nat
ext-ty-natural {margs = m ∷ margs} nat (A , Args) = ext-ty-natural (nat (ty-closed-natural A)) Args


ty-natural : (T : Ty m) {Γ Δ : SemCtx ⟦ m ⟧mode} {σ : Γ M.⇒ Δ} → ⟦ T ⟧ty M.[ σ ] M.≅ᵗʸ ⟦ T ⟧ty
ty-natural T = closed-natural (ty-closed-natural T) _

⇛-closed-natural : (T S : Ty m) → ty-closed-natural (T ⇛ S) M.≅ᶜⁿ M.fun-closed (ty-closed-natural T) (ty-closed-natural S)
⇛-closed-natural T S =
  M.fun-closed-congᶜⁿ (DRA.𝟙-preserves-cl (ty-closed-natural T)) (M.reflᶜⁿ (ty-closed-natural S))


--------------------------------------------------
-- Interpretation of contexts and nameless telescopes

⟦_⟧ctx : Ctx m → SemCtx ⟦ m ⟧mode
⟦ ◇ ⟧ctx = M.◇
⟦ Γ ,, μ ∣ _ ∈ T ⟧ctx = ⟦ Γ ⟧ctx M.,, DRA.⟨ ⟦ μ ⟧mod ∣ ⟦ T ⟧ty ⟩
⟦ Γ ,lock⟨ μ ⟩ ⟧ctx = DRA.lock ⟦ μ ⟧mod ⟦ Γ ⟧ctx

_++⟦_⟧nltel : SemCtx ⟦ m ⟧mode → NamelessTele m n → SemCtx ⟦ n ⟧mode
sΓ ++⟦ ◇ ⟧nltel = sΓ
sΓ ++⟦ Θ ,, μ ∣ T ⟧nltel = (sΓ ++⟦ Θ ⟧nltel) M.,, DRA.⟨ ⟦ μ ⟧mod ∣ ⟦ T ⟧ty ⟩
sΓ ++⟦ Θ ,lock⟨ μ ⟩ ⟧nltel = DRA.lock ⟦ μ ⟧mod (sΓ ++⟦ Θ ⟧nltel)

++tel-++⟦⟧nltel : (Γ : Ctx m) (Θ : NamelessTele m n) (names : Names Θ) →
                  ⟦ Γ ++tel add-names Θ names ⟧ctx M.≅ᶜ ⟦ Γ ⟧ctx ++⟦ Θ ⟧nltel
++tel-++⟦⟧nltel Γ ◇ names = M.reflᶜ
++tel-++⟦⟧nltel Γ (Θ ,, μ ∣ T) (names , _) = M.ctx-functor-cong (,,-functor (ty-closed-natural ⟨ μ ∣ T ⟩)) (++tel-++⟦⟧nltel Γ Θ names)
++tel-++⟦⟧nltel Γ (Θ ,lock⟨ μ ⟩) names = M.ctx-functor-cong (DRA.ctx-functor ⟦ μ ⟧mod) (++tel-++⟦⟧nltel Γ Θ names)

apply-nltel-sub : {sΓ sΔ : SemCtx ⟦ m ⟧mode} (σ : sΓ M.⇒ sΔ) (Θ : NamelessTele m n) →
                  (sΓ ++⟦ Θ ⟧nltel M.⇒ sΔ ++⟦ Θ ⟧nltel)
apply-nltel-sub σ ◇ = σ
apply-nltel-sub σ (Θ ,, μ ∣ T) = lift-cl-subst (ty-closed-natural ⟨ μ ∣ T ⟩) (apply-nltel-sub σ Θ)
apply-nltel-sub σ (Θ ,lock⟨ μ ⟩) = DRA.lock-fmap ⟦ μ ⟧mod (apply-nltel-sub σ Θ)
