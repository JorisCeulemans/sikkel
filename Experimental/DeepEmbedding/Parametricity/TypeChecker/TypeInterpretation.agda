--------------------------------------------------
-- Interpretation of modes, modalities, types and contexts in a presheaf model
--------------------------------------------------

open import Experimental.DeepEmbedding.Parametricity.TypeChecker.Builtin

module Experimental.DeepEmbedding.Parametricity.TypeChecker.TypeInterpretation (builtin : BuiltinTypes) where

open BuiltinTypes builtin

open import Categories as M hiding (★; ω)
open import CwF-Structure as M hiding (◇; _,,_; var; _ⓣ-vert_; _ⓣ-hor_)
open import Types.Discrete as M hiding (Nat'; Bool')
open import Types.Functions as M hiding (_⇛_; lam; app)
open import Types.Products as M hiding (_⊠_; pair; fst; snd)
open import Types.Instances as M
open import Modalities as M hiding (𝟙; _ⓜ_; ⟨_∣_⟩; _,lock⟨_⟩; mod-intro; mod-elim)
open import Parametricity.Binary.TypeSystem as M hiding (forget-left; forget-right)

open import Experimental.DeepEmbedding.Parametricity.TypeChecker.Syntax builtin

private
  variable
    m m' : ModeExpr


⟦_⟧mode : ModeExpr → Category
⟦ ★ ⟧mode = M.★
⟦ ⋀ ⟧mode = M.⋀

⟦_⟧modality : ModalityExpr m m' → Modality ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ 𝟙 ⟧modality = M.𝟙
-- ⟦ μ ⓜ ρ ⟧modality = ⟦ μ ⟧modality M.ⓜ ⟦ ρ ⟧modality
⟦ forget-left ⟧modality = M.forget-left
⟦ forget-right ⟧modality = M.forget-right

{-
⟦_⟧two-cell : {μ ρ : ModalityExpr m m'} → TwoCellExpr μ ρ → TwoCell ⟦ μ ⟧modality ⟦ ρ ⟧modality
⟦ id-cell _ ⟧two-cell = two-cell (id-ctx-transf _)
⟦ α ⓣ-vert β ⟧two-cell = two-cell (transf ⟦ β ⟧two-cell M.ⓣ-vert transf ⟦ α ⟧two-cell)
⟦ α ⓣ-hor β ⟧two-cell = two-cell (transf ⟦ β ⟧two-cell M.ⓣ-hor transf ⟦ α ⟧two-cell)
⟦ 𝟙≤later ⟧two-cell = M.𝟙≤later
⟦ timeless∘allnow≤𝟙 ⟧two-cell = M.timeless∘allnow≤𝟙
-}

⟦_⟧ty : TyExpr m → ClosedType ⟦ m ⟧mode
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
