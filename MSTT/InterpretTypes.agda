--------------------------------------------------
-- Interpretation of types and contexts in a presheaf model
--------------------------------------------------

open import MSTT.Parameter.ModeTheory
open import MSTT.Parameter.TypeExtension using (TyExt)

module MSTT.InterpretTypes (mt : ModeTheory) (ty-ext : TyExt mt) where

open import Data.List
open import Data.Product using (_×_; proj₁; proj₂)

open import Model.CwF-Structure as M hiding (◇; _,,_)
open import Model.Type.Discrete as M hiding (Nat'; Bool')
open import Model.Type.Function as M hiding (_⇛_; lam; app)
open import Model.Type.Product as M hiding (_⊠_; pair; fst; snd)
open import Model.Modality as M hiding (𝟙; _ⓜ_; ⟨_∣_⟩; _,lock⟨_⟩; mod-intro; mod-elim)

open import MSTT.TCMonad
open import MSTT.Syntax.Type mt ty-ext
open import MSTT.Syntax.Context mt ty-ext
open MSTT.Parameter.TypeExtension mt hiding (TyExt)

open ModeTheory mt
open TyExt ty-ext

private
  variable
    m : ModeExpr
    margs : List ModeExpr


⟦_⟧ty : TyExpr m → ClosedTy ⟦ m ⟧mode
interpret-ext-ty : TyConstructor margs m → TyExtArgs margs → ClosedTy ⟦ m ⟧mode

⟦ Nat' ⟧ty = M.Nat'
⟦ Bool' ⟧ty = M.Bool'
⟦ T1 ⇛ T2 ⟧ty = ⟦ T1 ⟧ty M.⇛ ⟦ T2 ⟧ty
⟦ T1 ⊠ T2 ⟧ty = ⟦ T1 ⟧ty M.⊠ ⟦ T2 ⟧ty
⟦ ⟨ μ ∣ T ⟩ ⟧ty = M.⟨ ⟦ μ ⟧modality ∣ ⟦ T ⟧ty ⟩
⟦ Ext code args ⟧ty = interpret-ext-ty (interpret-code code) args

interpret-ext-ty {[]}        T args = T
interpret-ext-ty {m ∷ margs} F args = interpret-ext-ty (F ⟦ proj₁ args ⟧ty) (proj₂ args)

⟦_⟧ctx : CtxExpr m → Ctx ⟦ m ⟧mode
⟦ ◇ ⟧ctx = M.◇
⟦ Γ , μ ∣ _ ∈ T ⟧ctx = ⟦ Γ ⟧ctx M.,, M.⟨ ⟦ μ ⟧modality ∣ ⟦ T ⟧ty ⟩
⟦ Γ ,lock⟨ μ ⟩ ⟧ctx = ⟦ Γ ⟧ctx M.,lock⟨ ⟦ μ ⟧modality ⟩

⟦⟧ty-natural : (T : TyExpr m) → IsClosedNatural ⟦ T ⟧ty
interpret-ext-ty-natural : {F : TyConstructor margs m} → TyConstructorNatural F → (args : TyExtArgs margs) →
                           IsClosedNatural (interpret-ext-ty F args)

⟦⟧ty-natural Nat' = M.discr-closed
⟦⟧ty-natural Bool' = M.discr-closed
⟦⟧ty-natural (T1 ⇛ T2) = M.fun-closed {{⟦⟧ty-natural T1}} {{⟦⟧ty-natural T2}}
⟦⟧ty-natural (T1 ⊠ T2) = M.prod-closed {{⟦⟧ty-natural T1}} {{⟦⟧ty-natural T2}}
⟦⟧ty-natural ⟨ μ ∣ T ⟩ = M.mod-closed {μ = ⟦ μ ⟧modality} {{⟦⟧ty-natural T}}
⟦⟧ty-natural (Ext code args) = interpret-ext-ty-natural (interpret-code-natural code) args

interpret-ext-ty-natural {[]}        nat args = nat
interpret-ext-ty-natural {m ∷ margs} nat args = interpret-ext-ty-natural (nat (⟦⟧ty-natural (proj₁ args)))
                                                                         (proj₂ args)
