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
  ★ ω : ModeExpr

private
  variable
    m m' m'' : ModeExpr

infixl 5 _ⓜ_
data ModalityExpr : ModeExpr → ModeExpr → Set where
  𝟙 : ModalityExpr m m
  _ⓜ_ : ModalityExpr m' m'' → ModalityExpr m m' → ModalityExpr m m''
  timeless : ModalityExpr ★ ω
  allnow : ModalityExpr ω ★
  later : ModalityExpr ω ω

data TwoCellExpr : ModalityExpr m m' → ModalityExpr m m' → Set where
  id-cell : (μ : ModalityExpr m m') → TwoCellExpr μ μ
  _ⓣ-vert_ : {μ ρ κ : ModalityExpr m m'} → TwoCellExpr ρ κ → TwoCellExpr μ ρ → TwoCellExpr μ κ
    -- ^ Vertical composition of 2-cells.
  _ⓣ-hor_ : {μ μ' : ModalityExpr m' m''} {ρ ρ' : ModalityExpr m m'} →
            TwoCellExpr μ μ' → TwoCellExpr ρ ρ' → TwoCellExpr (μ ⓜ ρ) (μ' ⓜ ρ')
    -- ^ Horizontal composition of 2-cells.
  𝟙≤later : TwoCellExpr 𝟙 later
  timeless∘allnow≤𝟙 : TwoCellExpr (timeless ⓜ allnow) 𝟙

infixr 6 _⇛_
infixl 5 _⊠_
data TyExpr : ModeExpr → Set where
  Nat' : TyExpr m
  Bool' : TyExpr m
  _⇛_ : TyExpr m → TyExpr m → TyExpr m
  _⊠_ : TyExpr m → TyExpr m → TyExpr m
  ⟨_∣_⟩ : ModalityExpr m' m → TyExpr m' → TyExpr m
  GStream : TyExpr ★ → TyExpr ω

▻ : TyExpr ω → TyExpr ω
▻ T = ⟨ later ∣ T ⟩

data CtxExpr (m : ModeExpr) : Set where
  ◇ : CtxExpr m
  _,_ : (Γ : CtxExpr m) (T : TyExpr m) → CtxExpr m
  _,lock⟨_⟩ : (Γ : CtxExpr m') → ModalityExpr m m' → CtxExpr m

infixl 50 _∙_
data TmExpr : ModeExpr → Set where
  ann_∈_ : TmExpr m → TyExpr m → TmExpr m   -- term with a type annotation
  var : ℕ → TmExpr m
  lam : TyExpr m → TmExpr m → TmExpr m
  _∙_ : TmExpr m → TmExpr m → TmExpr m
  lit : ℕ → TmExpr m
  suc plus : TmExpr m
  true false : TmExpr m
  if : TmExpr m → TmExpr m → TmExpr m → TmExpr m
  timeless-if : TmExpr ω → TmExpr ω → TmExpr ω → TmExpr ω
  pair : TmExpr m → TmExpr m → TmExpr m
  fst snd : TmExpr m → TmExpr m
  mod-intro : ModalityExpr m m' → TmExpr m → TmExpr m'
  mod-elim : ModalityExpr m m' → TmExpr m' → TmExpr m
  coe : (μ ρ : ModalityExpr m m') → TwoCellExpr μ ρ → TmExpr m' → TmExpr m'
  löb : TyExpr ω → TmExpr ω → TmExpr ω
  g-cons g-head g-tail : TyExpr ★ → TmExpr ω

syntax coe μ ρ α t = coe[ α ∈ μ ⇒ ρ ] t


--------------------------------------------------
-- Printing mode, modality, type, and context expressions
--  (mostly for type errors)

show-mode : ModeExpr → String
show-mode ★ = "★"
show-mode ω = "ω"

show-modality : ModalityExpr m m' → String
show-modality 𝟙 = "𝟙"
show-modality (μ ⓜ ρ) = show-modality μ ++ " ⓜ " ++ show-modality ρ
show-modality timeless = "timeless"
show-modality allnow = "allnow"
show-modality later = "later"

show-type : TyExpr m → String
show-type Nat' = "Nat"
show-type Bool' = "Bool"
show-type (T1 ⇛ T2) = show-type T1 ++ " → " ++ show-type T2
show-type (T1 ⊠ T2) = show-type T1 ++ " ⊠ " ++ show-type T2
show-type ⟨ μ ∣ T ⟩ = "⟨ " ++ show-modality μ ++ " | " ++ show-type T ++ " ⟩"
show-type (GStream T) = "GStream " ++ show-type T

show-ctx : CtxExpr m → String
show-ctx ◇ = "◇"
show-ctx (Γ , T) = show-ctx Γ ++ " , " ++ show-type T
show-ctx (Γ ,lock⟨ μ ⟩) = show-ctx Γ ++ " .lock⟨ " ++ show-modality μ ++ " ⟩"


--------------------------------------------------
-- Deciding whether a type expression is a function type, a product type or
--   a modal type and whether a context is of the form Γ ,lock⟨ μ ⟩.

record IsFuncTyExpr (T : TyExpr m) : Set where
  constructor func-ty
  field
    dom cod : TyExpr m
    is-func : T ≡ dom ⇛ cod

is-func-ty : (T : TyExpr m) → TCM (IsFuncTyExpr T)
is-func-ty (T1 ⇛ T2) = return (func-ty T1 T2 refl)
is-func-ty T = type-error ("Expected a function type but received instead: " ++ show-type T)

record IsProdTyExpr (T : TyExpr m) : Set where
  constructor prod-ty
  field
    comp₁ comp₂ : TyExpr m
    is-prod : T ≡ comp₁ ⊠ comp₂

is-prod-ty : (T : TyExpr m) → TCM (IsProdTyExpr T)
is-prod-ty (T1 ⊠ T2) = return (prod-ty T1 T2 refl)
is-prod-ty T = type-error ("Expected a product type but received instead: " ++ show-type T)

record IsModalTyExpr (T : TyExpr m) : Set where
  constructor modal-ty
  field
    {n} : ModeExpr
    S : TyExpr n
    μ : ModalityExpr n m
    is-modal : T ≡ ⟨ μ ∣ S ⟩

is-modal-ty : (T : TyExpr m) → TCM (IsModalTyExpr T)
is-modal-ty ⟨ μ ∣ T ⟩ = return (modal-ty T μ refl)
is-modal-ty T = type-error ("Expected a modal type but received instead: " ++ show-type T)

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
