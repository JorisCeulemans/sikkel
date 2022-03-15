--------------------------------------------------
-- A Simple Type Theory for which we will provide a logic
--------------------------------------------------

module Experimental.ProgramLogic.STT where

open import Data.Nat

open import Model.BaseCategory
open import Model.CwF-Structure as M using (Ctx; Ty; Tm; ClosedTy)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Discrete as M


--------------------------------------------------
-- Definition of syntactic types, contexts and terms

infixr 6 _⇛_
infixl 5 _⊠_
data TyExpr : Set where
  Nat' : TyExpr
  Bool' : TyExpr
  _⇛_ : TyExpr → TyExpr → TyExpr
  _⊠_ : TyExpr → TyExpr → TyExpr

private variable
  T S : TyExpr


infixl 4 _,,_
data CtxExpr : Set where
  ◇ : CtxExpr
  _,,_ : (Γ : CtxExpr) (T : TyExpr) → CtxExpr

private variable
  Γ Δ : CtxExpr


-- Variables are represented as de Bruijn indices.
data Var : CtxExpr → TyExpr → Set where
  vzero : Var (Γ ,, T) T
  vsuc : Var Γ T → Var (Γ ,, S) T

infixl 50 _∙_
data TmExpr (Γ : CtxExpr) : TyExpr → Set where
  var : Var Γ T → TmExpr Γ T
  lam : TmExpr (Γ ,, T) S → TmExpr Γ (T ⇛ S)
  _∙_ : TmExpr Γ (T ⇛ S) → TmExpr Γ T → TmExpr Γ S
  lit : ℕ → TmExpr Γ Nat'
  suc : TmExpr Γ (Nat' ⇛ Nat')
  nat-elim : {A : TyExpr} → TmExpr Γ A → TmExpr Γ (A ⇛ A) → TmExpr Γ (Nat' ⇛ A)
  true false : TmExpr Γ Bool'
  if : {A : TyExpr} → TmExpr Γ Bool' → (t f : TmExpr Γ A) → TmExpr Γ A
  pair : TmExpr Γ T → TmExpr Γ S → TmExpr Γ (T ⊠ S)
  fst : TmExpr Γ (T ⊠ S) → TmExpr Γ T
  snd : TmExpr Γ (T ⊠ S) → TmExpr Γ S


--------------------------------------------------
-- Interpretation of types, contexts and terms in the presheaf
--   model over the trivial base category

⟦_⟧ty : TyExpr → ClosedTy ★
⟦ Nat' ⟧ty = M.Nat'
⟦ Bool' ⟧ty = M.Bool'
⟦ T ⇛ S ⟧ty = ⟦ T ⟧ty M.⇛ ⟦ S ⟧ty
⟦ T ⊠ S ⟧ty = ⟦ T ⟧ty M.⊠ ⟦ S ⟧ty

⟦_⟧ctx : CtxExpr → Ctx ★
⟦ ◇ ⟧ctx = M.◇
⟦ Γ ,, T ⟧ctx = ⟦ Γ ⟧ctx M.,, ⟦ T ⟧ty

ty-closed : (T : TyExpr) {Δ Γ : Ctx ★} {σ : Δ M.⇒ Γ} → ⟦ T ⟧ty M.[ σ ] M.≅ᵗʸ ⟦ T ⟧ty
ty-closed Nat' = M.Discr-natural ℕ _
ty-closed Bool' = M.Discr-natural _ _
ty-closed (T ⇛ S) = M.≅ᵗʸ-trans (M.⇛-natural _) (M.⇛-cong (ty-closed T) (ty-closed S))
ty-closed (T ⊠ S) = M.≅ᵗʸ-trans (M.⊠-natural _) (M.⊠-cong (ty-closed T) (ty-closed S))

⟦_⟧var : Var Γ T → Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty
⟦ vzero {_} {T} ⟧var = M.ι⁻¹[ ty-closed T ] M.ξ
⟦ vsuc {_} {T} x ⟧var = M.ι⁻¹[ ty-closed T ] (⟦ x ⟧var M.[ M.π ]')

⟦_⟧tm : TmExpr Γ T → Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty
⟦ var x ⟧tm = ⟦ x ⟧var
⟦ lam {_} {S} t ⟧tm = M.lam _ (M.ι[ ty-closed S ] ⟦ t ⟧tm)
⟦ f ∙ t ⟧tm = M.app ⟦ f ⟧tm ⟦ t ⟧tm
⟦ lit n ⟧tm = M.discr n
⟦ suc ⟧tm = M.suc'
⟦ nat-elim a f ⟧tm = M.nat-elim _ ⟦ a ⟧tm ⟦ f ⟧tm
⟦ true ⟧tm = M.true'
⟦ false ⟧tm = M.false'
⟦ if b t f ⟧tm = M.if' ⟦ b ⟧tm then' ⟦ t ⟧tm else' ⟦ f ⟧tm
⟦ pair t s ⟧tm = M.app (M.app M.pair ⟦ t ⟧tm) ⟦ s ⟧tm
⟦ fst p ⟧tm = M.app M.fst ⟦ p ⟧tm
⟦ snd p ⟧tm = M.app M.snd ⟦ p ⟧tm
