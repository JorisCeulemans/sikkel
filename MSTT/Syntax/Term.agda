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
  m m' : ModeExpr
  margs : List ModeExpr


data TmExpr : ModeExpr → Set
TmExtArgs : List ModeExpr → Set

infixl 50 _∙_
infixr 4 lam[_∈_]_
data TmExpr where
  ann_∈_ : TmExpr m → TyExpr m → TmExpr m
  var : String → TmExpr m
  lam[_∈_]_ : String → TyExpr m → TmExpr m → TmExpr m
  _∙_ : TmExpr m → TmExpr m → TmExpr m
  lit : ℕ → TmExpr m
  suc plus : TmExpr m
  nat-elim : TmExpr m → TmExpr m → TmExpr m
  true false : TmExpr m
  if : TmExpr m → TmExpr m → TmExpr m → TmExpr m
  pair : TmExpr m → TmExpr m → TmExpr m
  fst snd : TmExpr m → TmExpr m
  mod-intro : ModalityExpr m m' → TmExpr m → TmExpr m'
  mod-elim : ModalityExpr m m' → TmExpr m' → TmExpr m
  coe : (μ ρ : ModalityExpr m m') → TwoCellExpr μ ρ → TmExpr m' → TmExpr m'
  ext : (code : TmExtCode margs m) → TmExtArgs margs → TmExpr m
    -- ^ Every code in the universe of tm-ext gives rise to a new term constructor,
    --   whose arguments are expressed by TmExtArgs.

TmExtArgs [] = ⊤
TmExtArgs (m ∷ margs) = TmExpr m × TmExtArgs margs

syntax coe μ ρ α t = coe[ α ∈ μ ⇒ ρ ] t
