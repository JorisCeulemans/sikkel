--------------------------------------------------
-- Definition of the MSTT syntax for types
--------------------------------------------------

open import MSTT.Parameter.ModeTheory
open import MSTT.Parameter.TypeExtension using (TyExt)

module MSTT.Syntax.Type (mt : ModeTheory) (ty-ext : TyExt mt)  where

open import Data.List hiding (_++_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.String
open import Data.Unit

open import MSTT.TCMonad

open ModeTheory mt
open TyExt ty-ext
open MSTT.Parameter.TypeExtension mt hiding (TyExt)

private variable
  m m' : ModeExpr
  margs : List ModeExpr


--------------------------------------------------
-- Expressions for MSTT types.

data TyExpr : ModeExpr → Set
TyExtArgs : List ModeExpr → Set

infixr 6 _⇛_
infixl 5 _⊠_
data TyExpr where
  Nat' : TyExpr m
  Bool' : TyExpr m
  _⇛_ : TyExpr m → TyExpr m → TyExpr m
  _⊠_ : TyExpr m → TyExpr m → TyExpr m
  ⟨_∣_⟩ : ModalityExpr m m' → TyExpr m → TyExpr m'
  Ext : ∀ {margs m} → TyExtCode margs m → TyExtArgs margs → TyExpr m

TyExtArgs [] = ⊤
TyExtArgs (m ∷ margs) = TyExpr m × TyExtArgs margs


--------------------------------------------------
-- Printing type expressions (mostly for type errors).

show-type : TyExpr m → String
show-ext-type : TyExtShow margs → TyExtArgs margs → String

show-type Nat' = "Nat"
show-type Bool' = "Bool"
show-type (T1 ⇛ T2) = show-type T1 ++ " → " ++ show-type T2
show-type (T1 ⊠ T2) = show-type T1 ++ " ⊠ " ++ show-type T2
show-type ⟨ μ ∣ T ⟩ = "⟨ " ++ show-modality μ ++ " | " ++ show-type T ++ " ⟩"
show-type (Ext code args) = show-ext-type (show-code code) args

show-ext-type {[]}        s args = s
show-ext-type {m ∷ margs} f args = show-ext-type (f (show-type (proj₁ args))) (proj₂ args)


--------------------------------------------------
-- Deciding whether a type expression is a function type, a product type or a modal type.

data IsFuncTyExpr : TyExpr m → Set where
  func-ty : (T S : TyExpr m) → IsFuncTyExpr (T ⇛ S)

is-func-ty : (T : TyExpr m) → TCM (IsFuncTyExpr T)
is-func-ty (T1 ⇛ T2) = return (func-ty T1 T2)
is-func-ty T = type-error ("Expected a function type but received instead: " ++ show-type T)

data IsProdTyExpr : TyExpr m → Set where
  prod-ty : (T S : TyExpr m) → IsProdTyExpr (T ⊠ S)

is-prod-ty : (T : TyExpr m) → TCM (IsProdTyExpr T)
is-prod-ty (T1 ⊠ T2) = return (prod-ty T1 T2)
is-prod-ty T = type-error ("Expected a product type but received instead: " ++ show-type T)

data IsModalTyExpr : TyExpr m → Set where
  modal-ty : (n : ModeExpr) (μ : ModalityExpr n m) (T : TyExpr n) → IsModalTyExpr ⟨ μ ∣ T ⟩

is-modal-ty : (T : TyExpr m) → TCM (IsModalTyExpr T)
is-modal-ty ⟨ μ ∣ T ⟩ = return (modal-ty _ μ T)
is-modal-ty T = type-error ("Expected a modal type but received instead: " ++ show-type T)
