open import Experimental.DeepEmbedding.Generic.Builtin.ModeTheory

module Experimental.DeepEmbedding.Generic.InterpretTypes (mt : ModeTheory) where

open import CwF-Structure as M hiding (◇; _,,_; var; _ⓣ-vert_; _ⓣ-hor_)
open import Types.Discrete as M hiding (Nat'; Bool')
open import Types.Functions as M hiding (_⇛_; lam; app)
open import Types.Products as M hiding (_⊠_; pair; fst; snd)
open import Types.Instances as M
open import Modalities as M hiding (𝟙; _ⓜ_; ⟨_∣_⟩; _,lock⟨_⟩; mod-intro; mod-elim)

open import Experimental.DeepEmbedding.Generic.TCMonad
open import Experimental.DeepEmbedding.Generic.Syntax mt

open ModeTheory mt

private
  variable
    m : ModeExpr


⟦_⟧ty : TyExpr m → ClosedType ⟦ m ⟧mode
⟦ Nat' ⟧ty = M.Nat'
⟦ Bool' ⟧ty = M.Bool'
⟦ T1 ⇛ T2 ⟧ty = ⟦ T1 ⟧ty M.⇛ ⟦ T2 ⟧ty
⟦ T1 ⊠ T2 ⟧ty = ⟦ T1 ⟧ty M.⊠ ⟦ T2 ⟧ty
⟦ ⟨ μ ∣ T ⟩ ⟧ty = M.⟨ ⟦ μ ⟧modality ∣ ⟦ T ⟧ty ⟩

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
