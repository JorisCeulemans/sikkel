--------------------------------------------------
-- Interpretation of types and contexts in a presheaf model
--------------------------------------------------

module Applications.GuardedRecursion.MSTT.InterpretTypes where

open import Model.CwF-Structure as M
open import Model.Type.Discrete as M hiding (Nat'; Bool')
open import Model.Type.Function as M hiding (_⇛_)
open import Model.Type.Product as M hiding (_⊠_)
open import Model.Modality as M hiding (⟨_∣_⟩; _,lock⟨_⟩)
open import Applications.GuardedRecursion.Model.Streams.Guarded as M hiding (GStream)

open import Applications.GuardedRecursion.MSTT.ModeTheory
open import Applications.GuardedRecursion.MSTT.Syntax

private
  variable
    m m' : ModeExpr


⟦_⟧ty : TyExpr m → ClosedTy ⟦ m ⟧mode
⟦ Nat' ⟧ty = M.Nat'
⟦ Bool' ⟧ty = M.Bool'
⟦ T1 ⇛ T2 ⟧ty = ⟦ T1 ⟧ty M.⇛ ⟦ T2 ⟧ty
⟦ T1 ⊠ T2 ⟧ty = ⟦ T1 ⟧ty M.⊠ ⟦ T2 ⟧ty
⟦ ⟨ μ ∣ T ⟩ ⟧ty = M.⟨_∣_⟩ ⟦ μ ⟧modality ⟦ T ⟧ty
⟦ GStream T ⟧ty = M.GStream ⟦ T ⟧ty

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
⟦⟧ty-natural (GStream T) = M.gstream-closed {{⟦⟧ty-natural T}}
