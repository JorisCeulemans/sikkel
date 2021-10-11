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

infixl 4 _,_∈_ _,lock⟨_⟩
data CtxExpr (m : ModeExpr) : Set where
  ◇ : CtxExpr m
  _,_∈_ : (Γ : CtxExpr m) → String → (T : TyExpr m) → CtxExpr m
  _,lock⟨_⟩ : (Γ : CtxExpr m') → ModalityExpr m m' → CtxExpr m


--------------------------------------------------
-- Printing context expressions (mostly for type errors)

show-ctx : CtxExpr m → String
show-ctx ◇ = "◇"
show-ctx (Γ , x ∈ T) = show-ctx Γ ++ " , " ++ x ++ " ∈ " ++ show-type T
show-ctx (Γ ,lock⟨ μ ⟩) = show-ctx Γ ++ " .lock⟨ " ++ show-modality μ ++ " ⟩"


--------------------------------------------------
-- Deciding whether a context is of the form Γ ,lock⟨ μ ⟩ , Δ.

data Telescope (m : ModeExpr) : Set where
  [] : Telescope m
  _,,_∈_ : Telescope m → String → TyExpr m → Telescope m

infixl 3 _+tel_
_+tel_ : CtxExpr m → Telescope m → CtxExpr m
Γ +tel [] = Γ
Γ +tel (Δ ,, v ∈ T) = (Γ +tel Δ) , v ∈ T

data IsLockedCtxExpr : CtxExpr m → Set where
  locked-ctx : (n : ModeExpr) (Γ' : CtxExpr n) (μ : ModalityExpr m n) (Δ : Telescope m) →
               IsLockedCtxExpr (Γ' ,lock⟨ μ ⟩ +tel Δ)

is-locked-ctx : (Γ : CtxExpr m) → TCM (IsLockedCtxExpr Γ)
is-locked-ctx ◇ = type-error "Expected a context which contains a lock but received instead: ◇"
is-locked-ctx (Γ , x ∈ T) = modify-error-msg (_++ " , " ++ x ++ " ∈ " ++ show-type T) (do
  locked-ctx _ Γ' μ Δ ← is-locked-ctx Γ
  return (locked-ctx _ Γ' μ (Δ ,, x ∈ T)))
is-locked-ctx (Γ ,lock⟨ μ ⟩) = return (locked-ctx _ Γ μ [])
