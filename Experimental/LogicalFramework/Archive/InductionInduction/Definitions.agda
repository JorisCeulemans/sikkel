module Experimental.LogicalFramework.Archive.InductionInduction.Definitions where

open import Data.Bool hiding (T; _∧_)
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Relation.Binary.PropositionalEquality


nat-rec : {A : Set} → A → (A → A) → ℕ → A
nat-rec a f zero    = a
nat-rec a f (suc n) = f (nat-rec a f n)


infixr 6 _⇛_
infixl 5 _⊠_
data TyExpr : Set where
  Nat' : TyExpr
  Bool' : TyExpr
  _⇛_ : TyExpr → TyExpr → TyExpr
  _⊠_ : TyExpr → TyExpr → TyExpr

private variable
  T S : TyExpr


data CtxExpr : Set
data Var : CtxExpr → TyExpr → Set
data TmExpr : CtxExpr → TyExpr → Set
data Formula : CtxExpr → Set

private variable
  Γ Δ : CtxExpr
  t s : TmExpr Γ T
  φ ψ : Formula Γ

infixl 2 _,,ᵛ_ _,,ᶠ_
data CtxExpr where
  ◇ : CtxExpr
  _,,ᵛ_ : (Γ : CtxExpr) (T : TyExpr) → CtxExpr
  _,,ᶠ_ : (Γ : CtxExpr) (φ : Formula Γ) → CtxExpr

data Var where
  vzero    : Var (Γ ,,ᵛ T) T
  vsuc     : Var Γ T → Var (Γ ,,ᵛ S) T
  skip-frm : Var Γ T → Var (Γ ,,ᶠ φ) T

infixl 50 _∙_
data TmExpr where
  var : Var Γ T → TmExpr Γ T
  lam : TmExpr (Γ ,,ᵛ T) S → TmExpr Γ (T ⇛ S)
  _∙_ : TmExpr Γ (T ⇛ S) → TmExpr Γ T → TmExpr Γ S
  lit : ℕ → TmExpr Γ Nat'
  suc : TmExpr Γ (Nat' ⇛ Nat')
  nat-elim : {A : TyExpr} → TmExpr Γ A → TmExpr Γ (A ⇛ A) → TmExpr Γ (Nat' ⇛ A)
  true false : TmExpr Γ Bool'
  if : {A : TyExpr} → TmExpr Γ Bool' → (t f : TmExpr Γ A) → TmExpr Γ A
  pair : TmExpr Γ T → TmExpr Γ S → TmExpr Γ (T ⊠ S)
  fst : TmExpr Γ (T ⊠ S) → TmExpr Γ T
  snd : TmExpr Γ (T ⊠ S) → TmExpr Γ S

data Formula where
  _≡ᶠ_ : {T : TyExpr} (t1 t2 : TmExpr Γ T) → Formula Γ
  _⊃_ _∧_ : (φ ψ : Formula Γ) → Formula Γ
  ∀[_]_ : (T : TyExpr) → Formula (Γ ,,ᵛ T) → Formula Γ


{-
module AgdaInterpretation where
  -- Interpretation of syntax in Agda (standard set model).
  ⟦_⟧ty : TyExpr → Set
  ⟦ Nat' ⟧ty = ℕ
  ⟦ Bool' ⟧ty = Bool
  ⟦ T ⇛ S ⟧ty = ⟦ T ⟧ty → ⟦ S ⟧ty
  ⟦ T ⊠ S ⟧ty = ⟦ T ⟧ty × ⟦ S ⟧ty

  ⟦_⟧ctx : CtxExpr → Set
  ⟦_⟧var : Var Γ T → (⟦ Γ ⟧ctx → ⟦ T ⟧ty)
  ⟦_⟧tm : TmExpr Γ T → (⟦ Γ ⟧ctx → ⟦ T ⟧ty)
  ⟦_⟧frm : Formula Γ → (⟦ Γ ⟧ctx → Set)

  ⟦ ◇ ⟧ctx = ⊤
  ⟦ Γ ,,ᵛ T ⟧ctx = ⟦ Γ ⟧ctx × ⟦ T ⟧ty
  ⟦ Γ ,,ᶠ φ ⟧ctx = Σ[ γ ∈ ⟦ Γ ⟧ctx ] (⟦ φ ⟧frm γ)

  ⟦ vzero ⟧var (_ , t) = t
  ⟦ vsuc x ⟧var (γ , _) = ⟦ x ⟧var γ
  ⟦ skip-frm x ⟧var (γ , _) = ⟦ x ⟧var γ

  ⟦ var x ⟧tm = ⟦ x ⟧var
  ⟦ lam t ⟧tm γ = λ x → ⟦ t ⟧tm (γ , x)
  ⟦ f ∙ t ⟧tm γ = ⟦ f ⟧tm γ (⟦ t ⟧tm γ)
  ⟦ lit n ⟧tm _ = n
  ⟦ suc ⟧tm _ = suc
  ⟦ nat-elim a f ⟧tm γ = nat-rec (⟦ a ⟧tm γ) (⟦ f ⟧tm γ)
  ⟦ true ⟧tm _ = true
  ⟦ false ⟧tm _ = false
  ⟦ if b t f ⟧tm γ = if ⟦ b ⟧tm γ then ⟦ t ⟧tm γ else ⟦ f ⟧tm γ
  ⟦ pair t s ⟧tm γ = ⟦ t ⟧tm γ , ⟦ s ⟧tm γ
  ⟦ fst p ⟧tm γ = proj₁ (⟦ p ⟧tm γ)
  ⟦ snd p ⟧tm γ = proj₂ (⟦ p ⟧tm γ)

  ⟦ t1 ≡ᶠ t2 ⟧frm γ = ⟦ t1 ⟧tm γ ≡ ⟦ t2 ⟧tm γ
  ⟦ φ ⊃ ψ ⟧frm γ = ⟦ φ ⟧frm γ → ⟦ ψ ⟧frm γ
  ⟦ φ ∧ ψ ⟧frm γ = ⟦ φ ⟧frm γ × ⟦ ψ ⟧frm γ
  ⟦ ∀[ T ] φ ⟧frm γ = (t : ⟦ T ⟧ty) → ⟦ φ ⟧frm (γ , t)
-}

open import Model.BaseCategory
import Model.CwF-Structure as M hiding (ClosedTy)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Sum as M
import Model.Type.Constant as M
import Experimental.ClosedTypes as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.Function as M

⟦_⟧ty : TyExpr → M.ClosedTy ★
⟦ Nat' ⟧ty = M.Nat'
⟦ Bool' ⟧ty = M.Bool'
⟦ T ⇛ S ⟧ty = ⟦ T ⟧ty M.⇛ ⟦ S ⟧ty
⟦ T ⊠ S ⟧ty = ⟦ T ⟧ty M.⊠ ⟦ S ⟧ty

⟦_⟧ctx : CtxExpr → M.Ctx ★
⟦_⟧var : Var Γ T → M.SimpleTm ⟦ Γ ⟧ctx ⟦ T ⟧ty
⟦_⟧tm : TmExpr Γ T → M.SimpleTm ⟦ Γ ⟧ctx ⟦ T ⟧ty
⟦_⟧frm : Formula Γ → M.Ty ⟦ Γ ⟧ctx

⟦ ◇ ⟧ctx = M.◇
⟦ Γ ,,ᵛ T ⟧ctx = ⟦ Γ ⟧ctx M.,,ₛ ⟦ T ⟧ty
⟦ Γ ,,ᶠ φ ⟧ctx = ⟦ Γ ⟧ctx M.,, ⟦ φ ⟧frm

⟦ vzero ⟧var = M.sξ
⟦ vsuc x ⟧var = ⟦ x ⟧var M.[ M.π ]s
⟦ skip-frm x ⟧var = ⟦ x ⟧var M.[ M.π ]s

⟦ var x ⟧tm = ⟦ x ⟧var
⟦ lam t ⟧tm = M.sλ[ _ ] ⟦ t ⟧tm
⟦ f ∙ t ⟧tm = ⟦ f ⟧tm M.∙ₛ ⟦ t ⟧tm
⟦ lit n ⟧tm = M.sconst n
⟦ suc ⟧tm = M.sconst-func suc
⟦ nat-elim a f ⟧tm = M.snat-elim ⟦ a ⟧tm ⟦ f ⟧tm
⟦ true ⟧tm = M.strue
⟦ false ⟧tm = M.sfalse
⟦ if b t f ⟧tm = M.sif ⟦ b ⟧tm ⟦ t ⟧tm ⟦ f ⟧tm
⟦ pair t s ⟧tm = M.spair ⟦ t ⟧tm ⟦ s ⟧tm
⟦ fst p ⟧tm = M.sfst ⟦ p ⟧tm
⟦ snd p ⟧tm = M.ssnd ⟦ p ⟧tm

⟦ t1 ≡ᶠ t2 ⟧frm = M.Id ⟦ t1 ⟧tm ⟦ t2 ⟧tm
⟦ φ ⊃ ψ ⟧frm = ⟦ φ ⟧frm M.⇛ ⟦ ψ ⟧frm
⟦ φ ∧ ψ ⟧frm = ⟦ φ ⟧frm M.⊠ ⟦ ψ ⟧frm
⟦ ∀[ T ] φ ⟧frm = M.Pi _ ⟦ φ ⟧frm
