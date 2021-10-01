--------------------------------------------------
-- Definition of the syntax of the deeply embedded language
--------------------------------------------------

open import Applications.Parametricity.MSTT.Builtin

module Applications.Parametricity.MSTT.Syntax (builtin : BuiltinTypes) where

open BuiltinTypes builtin

open import Data.Nat
open import Data.String
open import Level hiding (suc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Applications.Parametricity.Model using (_⟨→⟩_)

open import Applications.Parametricity.MSTT.TCMonad
open import Applications.Parametricity.MSTT.ModeTheory

private variable
  m m' : ModeExpr


--------------------------------------------------
-- Expressions representing types, contexts and terms

infixr 6 _⇛_
infixl 5 _⊠_
data TyExpr : ModeExpr → Set where
  Nat' : TyExpr m
  Bool' : TyExpr m
  _⇛_ : TyExpr m → TyExpr m → TyExpr m
  _⊠_ : TyExpr m → TyExpr m → TyExpr m
  ⟨_∣_⟩ : ModalityExpr m' m → TyExpr m' → TyExpr m
  Builtin : Code → TyExpr ⋀

infixl 4 _,_∈_
data CtxExpr (m : ModeExpr) : Set where
  ◇ : CtxExpr m
  _,_∈_ : (Γ : CtxExpr m) → String → (T : TyExpr m) → CtxExpr m
  _,lock⟨_⟩ : (Γ : CtxExpr m') → ModalityExpr m m' → CtxExpr m

infixl 50 _∙_
infixr 4 lam[_∈_]_
data TmExpr : ModeExpr → Set where
  ann_∈_ : TmExpr m → TyExpr m → TmExpr m   -- term with a type annotation
  var : String → TmExpr m
  lam[_∈_]_ : String → TyExpr m → TmExpr m → TmExpr m
  _∙_ : TmExpr m → TmExpr m → TmExpr m
  lit : ℕ → TmExpr m
  suc plus : TmExpr m
  true false : TmExpr m
  if : TmExpr m → TmExpr m → TmExpr m → TmExpr m
  pair : TmExpr m → TmExpr m → TmExpr m
  fst snd : TmExpr m → TmExpr m
  mod-intro : ModalityExpr m m' → TmExpr m → TmExpr m'
  mod-elim : ModalityExpr m m' → TmExpr m' → TmExpr m
  from-rel : (c : Code) (a : CodeLeft c) (b : CodeRight c) →
             CodeRelation c a b → TmExpr ⋀
  from-rel1 : (c1 c2 : Code)
              (f : CodeLeft  c1 → CodeLeft  c2)
              (g : CodeRight c1 → CodeRight c2) →
              (CodeRelation c1 ⟨→⟩ CodeRelation c2) f g →
              TmExpr ⋀
  from-rel2 : (c1 c2 c3 : Code)
              (f : CodeLeft  c1 → CodeLeft  c2 → CodeLeft  c3)
              (g : CodeRight c1 → CodeRight c2 → CodeRight c3) →
              (CodeRelation c1 ⟨→⟩ CodeRelation c2 ⟨→⟩ CodeRelation c3) f g →
              TmExpr ⋀


--------------------------------------------------
-- Printing type and context expressions (mostly for type errors)

show-type : TyExpr m → String
show-type Nat' = "Nat"
show-type Bool' = "Bool"
show-type (T1 ⇛ T2) = show-type T1 ++ " → " ++ show-type T2
show-type (T1 ⊠ T2) = show-type T1 ++ " ⊠ " ++ show-type T2
show-type ⟨ μ ∣ T ⟩ = "⟨ " ++ show-modality μ ++ " | " ++ show-type T ++ " ⟩"
show-type (Builtin c) = "Builtin " ++ show-code c

show-ctx : CtxExpr m → String
show-ctx ◇ = "◇"
show-ctx (Γ , x ∈ T) = show-ctx Γ ++ " , " ++ x ++ " ∈ " ++ show-type T
show-ctx (Γ ,lock⟨ μ ⟩) = show-ctx Γ ++ " .lock⟨ " ++ show-modality μ ++ " ⟩"


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
