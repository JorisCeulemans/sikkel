--------------------------------------------------
-- Interpretation of modes, modalities, types and contexts in a presheaf model
--------------------------------------------------

open import Applications.Parametricity.MSTT.Builtin

module Applications.Parametricity.MSTT.InterpretTypes (builtin : BuiltinTypes) where

open BuiltinTypes builtin

open import Model.CwF-Structure as M hiding (◇)
open import Model.Type.Discrete as M hiding (Nat'; Bool')
open import Model.Type.Function as M hiding (_⇛_)
open import Model.Type.Product as M hiding (_⊠_)
open import Model.Modality as M hiding (⟨_∣_⟩; _,lock⟨_⟩)
open import Applications.Parametricity.Model as M

open import Applications.Parametricity.MSTT.ModeTheory
open import Applications.Parametricity.MSTT.Syntax builtin

private
  variable
    m : ModeExpr


⟦_⟧ty : TyExpr m → ClosedTy ⟦ m ⟧mode
⟦ Nat' ⟧ty = M.Nat'
⟦ Bool' ⟧ty = M.Bool'
⟦ T1 ⇛ T2 ⟧ty = ⟦ T1 ⟧ty M.⇛ ⟦ T2 ⟧ty
⟦ T1 ⊠ T2 ⟧ty = ⟦ T1 ⟧ty M.⊠ ⟦ T2 ⟧ty
⟦ ⟨ μ ∣ T ⟩ ⟧ty = M.⟨_∣_⟩ ⟦ μ ⟧modality ⟦ T ⟧ty
⟦ Builtin c ⟧ty = M.FromRel (CodeLeft c) (CodeRight c) (CodeRelation c)

⟦_⟧ctx : CtxExpr m → Ctx ⟦ m ⟧mode
⟦ ◇ ⟧ctx = M.◇
⟦ Γ , _ ∈ T ⟧ctx = ⟦ Γ ⟧ctx M.,, ⟦ T ⟧ty
⟦ Γ ,lock⟨ μ ⟩ ⟧ctx = ⟦ Γ ⟧ctx M.,lock⟨ ⟦ μ ⟧modality ⟩

⟦⟧ty-natural : (T : TyExpr m) → IsClosedNatural ⟦ T ⟧ty
⟦⟧ty-natural Nat' = M.discr-closed
⟦⟧ty-natural Bool' = M.discr-closed
⟦⟧ty-natural (T1 ⇛ T2) = M.fun-closed {{⟦⟧ty-natural T1}} {{⟦⟧ty-natural T2}}
⟦⟧ty-natural (T1 ⊠ T2) = M.prod-closed {{⟦⟧ty-natural T1}} {{⟦⟧ty-natural T2}}
⟦⟧ty-natural ⟨ μ ∣ T ⟩ = M.mod-closed {μ = ⟦ μ ⟧modality} {{⟦⟧ty-natural T}}
⟦⟧ty-natural (Builtin c) = M.fromrel-natural
