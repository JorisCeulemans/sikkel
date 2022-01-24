--------------------------------------------------
-- Definition of the MSTT syntax for terms
--------------------------------------------------

open import MSTT.Parameter.ModeTheory
open import MSTT.Parameter.TypeExtension using (TyExt)
open import MSTT.Parameter.TermExtension using (TmExt)

module MSTT.Syntax.Term (mt : ModeTheory) (ty-ext : TyExt mt) (tm-ext : TmExt mt ty-ext) where

open import Data.List
open import Data.Nat
open import Data.Product using (_×_)
open import Data.String
open import Data.Unit

open import MSTT.Syntax.Type mt ty-ext

open ModeTheory mt
open TmExt tm-ext

private variable
  m m' m'' : ModeExpr
  margs : List ModeExpr


data TmExpr : ModeExpr → Set
TmExtArgs : List ModeExpr → Set

infixl 50 _∙_
infixr 4 lam[_∈_]_ mod⟨_⟩_
data TmExpr where
  ann_∈_ : TmExpr m → TyExpr m → TmExpr m
  var : String → TwoCellExpr → TmExpr m
  lam[_∈_]_ : String → TyExpr m → TmExpr m → TmExpr m
  _∙_ : TmExpr m → TmExpr m → TmExpr m
  lit : ℕ → TmExpr m
  suc : TmExpr m
  nat-elim : TmExpr m → TmExpr m → TmExpr m
  plus : TmExpr m
    -- ^ plus is not implemented in terms of nat-elim for performance reasons.
  true false : TmExpr m
  if : TmExpr m → TmExpr m → TmExpr m → TmExpr m
  pair : TmExpr m → TmExpr m → TmExpr m
  fst snd : TmExpr m → TmExpr m
  mod⟨_⟩_ : ModalityExpr m m' → TmExpr m → TmExpr m'
  mod-elim : ModalityExpr m' m → ModalityExpr m'' m' → String → TmExpr m' → TmExpr m → TmExpr m
  ext : (code : TmExtCode margs m) → TmExtArgs margs → TmExpr m
    -- ^ Every code in the universe of tm-ext gives rise to a new term constructor,
    --   whose arguments are expressed by TmExtArgs.

TmExtArgs [] = ⊤
TmExtArgs (m ∷ margs) = TmExpr m × TmExtArgs margs


-- Variables that can be accessed via the trivial 2-cell (which is very common).
svar : String → TmExpr m
svar x = var x id-cell

-- More readable syntax for the pattern-matching modal elimination + a version
--   where the first modality ρ is trivial.
syntax mod-elim ρ μ x t s = let⟨ ρ ⟩ mod⟨ μ ⟩ x ← t in' s

mod-elim' : ModalityExpr m' m → String → TmExpr m → TmExpr m → TmExpr m
mod-elim' = mod-elim 𝟙

syntax mod-elim' μ x t s = let' mod⟨ μ ⟩ x ← t in' s

-- Abstraction and application for modal functions, implemented in terms of ordinary
--   functions and modal operators.
-- The following definition introduces a variable x which is subsequently shadowed
--   when type-checking b. More precisely, b is checked in context
--   Γ , 𝟙 ∣ x ∈ ⟨ μ ∣ T ⟩ , μ ∣ x ∈ T
--   so any occurrence of x in b will resolve to the final x which appears in the
--   context under the modality μ but with type T.
infixr 4 lam[_∣_∈_]_
lam[_∣_∈_]_ : ModalityExpr m' m → String → TyExpr m' → TmExpr m → TmExpr m
lam[ μ ∣ x ∈ T ] b = lam[ x ∈ ⟨ μ ∣ T ⟩ ] (let' mod⟨ μ ⟩ x ← svar x in' b)

-- If Γ ⊢ f : [ μ ∣ T ]⇛ S and Γ ,lock⟨ μ ⟩ ⊢ t : T then
--   Γ ⊢ f ∙⟨ μ ⟩ t : S
infixl 50 _∙⟨_⟩_
_∙⟨_⟩_ : TmExpr m → ModalityExpr m' m → TmExpr m' → TmExpr m
f ∙⟨ μ ⟩ t = f ∙ (mod⟨ μ ⟩ t)
