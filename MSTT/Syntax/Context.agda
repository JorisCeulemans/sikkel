--------------------------------------------------
-- Definition of the MSTT syntax for contexts
--------------------------------------------------

open import MSTT.Parameter.ModeTheory
open import MSTT.Parameter.TypeExtension using (TyExt)

module MSTT.Syntax.Context (mt : ModeTheory) (ty-ext : TyExt mt)  where

open import Data.String

open import MSTT.TCMonad
open import MSTT.Syntax.Type mt ty-ext

open ModeTheory mt

private variable
  m m' : ModeExpr


--------------------------------------------------
-- Expressions for MSTT contexts

infixl 4 _,_∣_∈_ _,lock⟨_⟩
data CtxExpr (m : ModeExpr) : Set where
  ◇ : CtxExpr m
  _,_∣_∈_ : (Γ : CtxExpr m) → ModalityExpr m' m → String → (T : TyExpr m') → CtxExpr m
  _,lock⟨_⟩ : (Γ : CtxExpr m') → ModalityExpr m m' → CtxExpr m


--------------------------------------------------
-- Printing context expressions (mostly for type errors)

show-ctx : CtxExpr m → String
show-ctx ◇ = "◇"
show-ctx (Γ , μ ∣ x ∈ T) = show-ctx Γ ++ " , " ++ show-modality μ ++ " | " ++ x ++ " ∈ " ++ show-type T
show-ctx (Γ ,lock⟨ μ ⟩) = show-ctx Γ ++ " .lock⟨ " ++ show-modality μ ++ " ⟩"
