--------------------------------------------------
-- Interpretation of modes, modalities, types and contexts in a presheaf model
--------------------------------------------------

module Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.TypeInterpretation where

open import Categories
open import CwF-Structure
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import Types.Instances
open import Modalities
open Modality
open import GuardedRecursion.Modalities
open import GuardedRecursion.Streams.Guarded

open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Syntax

private
  variable
    m m' : ModeExpr


⟦_⟧mode : ModeExpr → Category
⟦ e-★ ⟧mode = ★
⟦ e-ω ⟧mode = ω

⟦_⟧modality : ModalityExpr m m' → Modality ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ e-𝟙 ⟧modality = 𝟙
⟦ μ e-ⓜ ρ ⟧modality = ⟦ μ ⟧modality ⓜ ⟦ ρ ⟧modality
⟦ e-timeless ⟧modality = timeless
⟦ e-allnow ⟧modality = allnow
⟦ e-later ⟧modality = later

⟦_⟧ty : TyExpr m → ClosedType ⟦ m ⟧mode
⟦ e-Nat ⟧ty = Nat'
⟦ e-Bool ⟧ty = Bool'
⟦ T1 e→ T2 ⟧ty = ⟦ T1 ⟧ty ⇛ ⟦ T2 ⟧ty
⟦ T1 e-⊠ T2 ⟧ty = ⟦ T1 ⟧ty ⊠ ⟦ T2 ⟧ty
⟦ e-mod μ T ⟧ty = mod ⟦ μ ⟧modality ⟦ T ⟧ty
⟦ e-▻' T ⟧ty = ▻' ⟦ T ⟧ty
⟦ e-GStream T ⟧ty = GStream ⟦ T ⟧ty

⟦_⟧ctx : CtxExpr m → Ctx ⟦ m ⟧mode
⟦ e-◇ ⟧ctx = ◇
⟦ Γ , T ⟧ctx = ⟦ Γ ⟧ctx ,, ⟦ T ⟧ty
⟦ Γ ,lock⟨ μ ⟩ ⟧ctx = ctx-op ⟦ μ ⟧modality ⟦ Γ ⟧ctx

⟦⟧ty-natural : (T : TyExpr m) → IsClosedNatural ⟦ T ⟧ty
⟦⟧ty-natural e-Nat = discr-closed
⟦⟧ty-natural e-Bool = discr-closed
⟦⟧ty-natural (T1 e→ T2) = fun-closed {{⟦⟧ty-natural T1}} {{⟦⟧ty-natural T2}}
⟦⟧ty-natural (T1 e-⊠ T2) = prod-closed {{⟦⟧ty-natural T1}} {{⟦⟧ty-natural T2}}
⟦⟧ty-natural (e-mod μ T) = record { closed-natural = λ σ → ≅ᵗʸ-trans (mod-natural ⟦ μ ⟧modality σ) (mod-cong ⟦ μ ⟧modality (closed-natural {{⟦⟧ty-natural T}} _)) }
⟦⟧ty-natural (e-▻' T) = ▻'-closed {{⟦⟧ty-natural T}}
⟦⟧ty-natural (e-GStream T) = gstream-closed {{⟦⟧ty-natural T}}
