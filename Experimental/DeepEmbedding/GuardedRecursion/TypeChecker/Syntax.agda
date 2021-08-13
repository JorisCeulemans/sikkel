--------------------------------------------------
-- Definition of the syntax of the deeply embedded language
--------------------------------------------------

module Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Syntax where

open import Data.Nat
open import Data.String
open import Relation.Binary.PropositionalEquality

open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Monad


--------------------------------------------------
-- Expressions representing modes, modalities, types, contexts and terms

data ModeExpr : Set where
  e-★ e-ω : ModeExpr

private
  variable
    m m' m'' : ModeExpr

data ModalityExpr : ModeExpr → ModeExpr → Set where
  e-𝟙 : ModalityExpr m m
  _e-ⓜ_ : ModalityExpr m' m'' → ModalityExpr m m' → ModalityExpr m m''
  e-timeless : ModalityExpr e-★ e-ω
  e-allnow : ModalityExpr e-ω e-★
  e-later : ModalityExpr e-ω e-ω

infixr 6 _e→_
infixl 5 _e-⊠_
data TyExpr : ModeExpr → Set where
  e-Nat : TyExpr m
  e-Bool : TyExpr m
  _e→_ : TyExpr m → TyExpr m → TyExpr m
  _e-⊠_ : TyExpr m → TyExpr m → TyExpr m
  e-mod : ModalityExpr m' m → TyExpr m' → TyExpr m
  e-▻' : TyExpr e-ω → TyExpr e-ω
  e-GStream : TyExpr e-★ → TyExpr e-ω

data CtxExpr (m : ModeExpr) : Set where
  e-◇ : CtxExpr m
  _,_ : (Γ : CtxExpr m) (T : TyExpr m) → CtxExpr m
  _,lock⟨_⟩ : (Γ : CtxExpr m') → ModalityExpr m m' → CtxExpr m

infixl 5 _e-⊛'_
data TmExpr : ModeExpr → Set where
  e-ann_∈_ : TmExpr m → TyExpr m → TmExpr m   -- term with type annotation
  e-var : ℕ → TmExpr m
  e-lam : TyExpr m → TmExpr m → TmExpr m
  e-app : TmExpr m → TmExpr m → TmExpr m
  e-lit : ℕ → TmExpr m
  e-suc e-plus : TmExpr m
  e-true e-false : TmExpr m
  e-if : TmExpr m → TmExpr m → TmExpr m → TmExpr m
  e-timeless-if : TmExpr e-ω → TmExpr e-ω → TmExpr e-ω → TmExpr e-ω
  e-pair : TmExpr m → TmExpr m → TmExpr m
  e-fst e-snd : TmExpr m → TmExpr m
  e-mod-intro : ModalityExpr m m' → TmExpr m → TmExpr m'
  e-mod-elim : ModalityExpr m m' → TmExpr m' → TmExpr m
  e-next' : TmExpr e-ω → TmExpr e-ω
  _e-⊛'_ : TmExpr e-ω → TmExpr e-ω → TmExpr e-ω
  e-löb : TyExpr e-ω → TmExpr e-ω → TmExpr e-ω
  e-cons e-head e-tail : TyExpr e-★ → TmExpr e-ω


--------------------------------------------------
-- Printing mode, modality, type, and context expressions
--  (mostly for type errors)

show-mode : ModeExpr → String
show-mode e-★ = "★"
show-mode e-ω = "ω"

show-modality : ModalityExpr m m' → String
show-modality e-𝟙 = "𝟙"
show-modality (μ e-ⓜ ρ) = show-modality μ ++ " ⓜ " ++ show-modality ρ
show-modality e-timeless = "timeless"
show-modality e-allnow = "allnow"
show-modality e-later = "later"

show-type : TyExpr m → String
show-type e-Nat = "Nat"
show-type e-Bool = "Bool"
show-type (T1 e→ T2) = show-type T1 ++ " → " ++ show-type T2
show-type (T1 e-⊠ T2) = show-type T1 ++ " ⊠ " ++ show-type T2
show-type (e-mod μ T) = "⟨ " ++ show-modality μ ++ " | " ++ show-type T ++ " ⟩"
show-type (e-▻' T) = "▻' " ++ show-type T
show-type (e-GStream T) = "GStream " ++ show-type T

show-ctx : CtxExpr m → String
show-ctx e-◇ = "◇"
show-ctx (Γ , T) = show-ctx Γ ++ " . " ++ show-type T
show-ctx (Γ ,lock⟨ μ ⟩) = show-ctx Γ ++ ".lock⟨ " ++ show-modality μ ++ " ⟩"


--------------------------------------------------
-- Deciding whether a type expression is a function type, a product type or
--   a modal type and whether a context is of the form Γ ,lock⟨ μ ⟩.

record IsFuncTyExpr (T : TyExpr m) : Set where
  constructor func-ty
  field
    dom cod : TyExpr m
    is-func : T ≡ dom e→ cod

is-func-ty : (T : TyExpr m) → TCM (IsFuncTyExpr T)
is-func-ty (T1 e→ T2) = return (func-ty T1 T2 refl)
is-func-ty T = type-error ("Expected a function type but received instead: " ++ show-type T)

record IsProdTyExpr (T : TyExpr m) : Set where
  constructor prod-ty
  field
    comp₁ comp₂ : TyExpr m
    is-prod : T ≡ comp₁ e-⊠ comp₂

is-prod-ty : (T : TyExpr m) → TCM (IsProdTyExpr T)
is-prod-ty (T1 e-⊠ T2) = return (prod-ty T1 T2 refl)
is-prod-ty T = type-error ("Expected a product type but received instead: " ++ show-type T)

record IsModalTyExpr (T : TyExpr m) : Set where
  constructor modal-ty
  field
    {n} : ModeExpr
    S : TyExpr n
    μ : ModalityExpr n m
    is-modal : T ≡ e-mod μ S

is-modal-ty : (T : TyExpr m) → TCM (IsModalTyExpr T)
is-modal-ty (e-mod μ T) = return (modal-ty T μ refl)
is-modal-ty T = type-error ("Expected a modal type but received instead: " ++ show-type T)

record IsLaterTyExpr (T : TyExpr e-ω) : Set where
  constructor later-ty
  field
    S : TyExpr e-ω
    is-later : T ≡ e-▻' S

is-later-ty : (T : TyExpr e-ω) → TCM (IsLaterTyExpr T)
is-later-ty (e-▻' T) = return (later-ty T refl)
is-later-ty T = type-error ("Expected a type of the form ▻' T but received instead: " ++ show-type T)

record IsModalCtxExpr (Γ : CtxExpr m) : Set where
  constructor modal-ctx
  field
    {n} : ModeExpr
    Γ' : CtxExpr n
    μ : ModalityExpr m n
    is-modal : Γ ≡ (Γ' ,lock⟨ μ ⟩)

is-modal-ctx : (Γ : CtxExpr m) → TCM (IsModalCtxExpr Γ)
is-modal-ctx (Γ ,lock⟨ μ ⟩) = return (modal-ctx Γ μ refl)
is-modal-ctx Γ = type-error ("Expected a context with a lock applied but received instead: " ++ show-ctx Γ)
