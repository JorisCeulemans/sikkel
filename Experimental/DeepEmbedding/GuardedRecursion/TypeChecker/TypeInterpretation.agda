--------------------------------------------------
-- Interpretation of modes, modalities, types and contexts in a presheaf model
--------------------------------------------------

module Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.TypeInterpretation where

open import Categories as M hiding (★; ω)
open import CwF-Structure as M hiding (◇; _,,_; var)
open import Types.Discrete as M hiding (Nat'; Bool')
open import Types.Functions as M hiding (_⇛_; lam; app)
open import Types.Products as M hiding (_⊠_; pair; fst; snd)
open import Types.Instances as M
open import Modalities as M hiding (𝟙; _ⓜ_; ⟨_∣_⟩; _,lock⟨_⟩; mod-intro; mod-elim)
open import GuardedRecursion.Modalities as M hiding (timeless; allnow; later; ▻'; next'; _⊛'_; löb)
open import GuardedRecursion.Streams.Guarded as M hiding (GStream; g-cons; g-head; g-tail)

open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Syntax

private
  variable
    m m' : ModeExpr


⟦_⟧mode : ModeExpr → Category
⟦ ★ ⟧mode = M.★
⟦ ω ⟧mode = M.ω

⟦_⟧modality : ModalityExpr m m' → Modality ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ 𝟙 ⟧modality = M.𝟙
⟦ μ ⓜ ρ ⟧modality = ⟦ μ ⟧modality M.ⓜ ⟦ ρ ⟧modality
⟦ timeless ⟧modality = M.timeless
⟦ allnow ⟧modality = M.allnow
⟦ later ⟧modality = M.later

⟦_⟧ty : TyExpr m → ClosedType ⟦ m ⟧mode
⟦ Nat' ⟧ty = M.Nat'
⟦ Bool' ⟧ty = M.Bool'
⟦ T1 ⇛ T2 ⟧ty = ⟦ T1 ⟧ty M.⇛ ⟦ T2 ⟧ty
⟦ T1 ⊠ T2 ⟧ty = ⟦ T1 ⟧ty M.⊠ ⟦ T2 ⟧ty
⟦ ⟨ μ ∣ T ⟩ ⟧ty = M.⟨_∣_⟩ ⟦ μ ⟧modality ⟦ T ⟧ty
⟦ ▻' T ⟧ty = M.▻' ⟦ T ⟧ty
⟦ GStream T ⟧ty = M.GStream ⟦ T ⟧ty

⟦_⟧ctx : CtxExpr m → Ctx ⟦ m ⟧mode
⟦ ◇ ⟧ctx = M.◇
⟦ Γ , T ⟧ctx = ⟦ Γ ⟧ctx M.,, ⟦ T ⟧ty
⟦ Γ ,lock⟨ μ ⟩ ⟧ctx = ⟦ Γ ⟧ctx M.,lock⟨ ⟦ μ ⟧modality ⟩

⟦⟧ty-natural : (T : TyExpr m) → IsClosedNatural ⟦ T ⟧ty
⟦⟧ty-natural Nat' = M.discr-closed
⟦⟧ty-natural Bool' = M.discr-closed
⟦⟧ty-natural (T1 ⇛ T2) = M.fun-closed {{⟦⟧ty-natural T1}} {{⟦⟧ty-natural T2}}
⟦⟧ty-natural (T1 ⊠ T2) = M.prod-closed {{⟦⟧ty-natural T1}} {{⟦⟧ty-natural T2}}
⟦⟧ty-natural ⟨ μ ∣ T ⟩ = M.mod-closed {μ = ⟦ μ ⟧modality} {{⟦⟧ty-natural T}}
⟦⟧ty-natural (▻' T) = M.▻'-closed {{⟦⟧ty-natural T}}
⟦⟧ty-natural (GStream T) = M.gstream-closed {{⟦⟧ty-natural T}}
