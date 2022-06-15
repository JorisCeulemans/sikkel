{-# OPTIONS --allow-unsolved-metas #-}

module Experimental.LogicalFramework.Archive.BadClosedTypes.Derivation.SplitEnvironment where

open import Data.Nat

open import Model.BaseCategory
open import Model.CwF-Structure as M using (Ctx; Ty; Tm)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Discrete as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.Function as MDF

open import Experimental.LogicalFramework.Archive.BadClosedTypes.STT
open import Experimental.LogicalFramework.Archive.BadClosedTypes.Formula

private variable
  Γ Δ : CtxExpr
  T S : TyExpr
  φ ψ : Formula Γ


-- A formula environment will keep track of all assumptions.
data FrmEnv (Γ : CtxExpr) : Set where
  [] : FrmEnv Γ
  _∷_ : FrmEnv Γ → Formula Γ → FrmEnv Γ

private variable
  φs ψs : FrmEnv Γ

_[_]frm-env : FrmEnv Γ → SubstExpr Δ Γ → FrmEnv Δ
[]       [ σ ]frm-env = []
(φs ∷ φ) [ σ ]frm-env = (φs [ σ ]frm-env) ∷ (φ [ σ ]frm)

weaken-frm-env : FrmEnv Γ → FrmEnv (Γ ,, T)
weaken-frm-env φs = φs [ π ]frm-env


data Assumption : FrmEnv Γ → Formula Γ → Set where
  azero : Assumption (φs ∷ φ) φ
  asuc : Assumption φs φ → Assumption (φs ∷ ψ) φ

infix 1 _∣_⊢_
data _∣_⊢_ : (Γ : CtxExpr) → FrmEnv Γ → Formula Γ → Set where
  -- Structural rules for ≡ᶠ
  refl : {t : TmExpr Γ T} → Γ ∣ φs ⊢ t ≡ᶠ t
  sym : {t1 t2 : TmExpr Γ T} → (Γ ∣ φs ⊢ t1 ≡ᶠ t2) → (Γ ∣ φs ⊢ t2 ≡ᶠ t1)
  trans : {t1 t2 t3 : TmExpr Γ T} →
          (Γ ∣ φs ⊢ t1 ≡ᶠ t2) → (Γ ∣ φs ⊢ t2 ≡ᶠ t3) →
          (Γ ∣ φs ⊢ t1 ≡ᶠ t3)
  cong : (f : TmExpr Γ (T ⇛ S)) {t1 t2 : TmExpr Γ T} →
         (Γ ∣ φs ⊢ t1 ≡ᶠ t2) →
         (Γ ∣ φs ⊢ f ∙ t1 ≡ᶠ f ∙ t2)
  fun-cong : {f g : TmExpr Γ (T ⇛ S)} →
             (Γ ∣ φs ⊢ f ≡ᶠ g) →
             (t : TmExpr Γ T) →
             (Γ ∣ φs ⊢ f ∙ t ≡ᶠ g ∙ t)

  -- Introduction and elimination for logical combinators ⊃, ∧ and ∀.
  assume : (Γ ∣ φs ∷ φ ⊢ ψ) → (Γ ∣ φs ⊢ φ ⊃ ψ)
  assumption : Assumption φs φ → Γ ∣ φs ⊢ φ
  ∧-intro : (Γ ∣ φs ⊢ φ) → (Γ ∣ φs ⊢ ψ) → (Γ ∣ φs ⊢ φ ∧ ψ)
  ∧-elimˡ : (Γ ∣ φs ⊢ φ ∧ ψ) → (Γ ∣ φs ⊢ φ)
  ∧-elimʳ : (Γ ∣ φs ⊢ φ ∧ ψ) → (Γ ∣ φs ⊢ ψ)
  ∀-intro : (Γ ,, T ∣ φs [ π ]frm-env ⊢ φ) → (Γ ∣ φs ⊢ ∀[ T ] φ)
  ∀-elim : (Γ ∣ φs ⊢ ∀[ T ] φ) → (t : TmExpr Γ T) → (Γ ∣ φs ⊢ φ [ id-subst ∷ t ]frm)

  -- Specific computation rules for term formers (currently no eta rules).
  fun-β : {b : TmExpr (Γ ,, T) S} {t : TmExpr Γ T} →
          (Γ ∣ φs ⊢ lam b ∙ t ≡ᶠ (b [ id-subst ∷ t ]tm))
  suc-lit : {n : ℕ} → (Γ ∣ φs ⊢ (suc ∙ lit n) ≡ᶠ lit (suc n))
  nat-elim-β-zero : {A : TyExpr} {a : TmExpr Γ A} {f : TmExpr Γ (A ⇛ A)} →
                    (Γ ∣ φs ⊢ nat-elim a f ∙ lit 0 ≡ᶠ a)
  nat-elim-β-suc : {A : TyExpr} {a : TmExpr Γ A} {f : TmExpr Γ (A ⇛ A)} {n : TmExpr Γ Nat'} →
                   (Γ ∣ φs ⊢ nat-elim a f ∙ (suc ∙ n) ≡ᶠ f ∙ (nat-elim a f ∙ n))
  if-β-true : {t f : TmExpr Γ T} → (Γ ∣ φs ⊢ if true t f ≡ᶠ t)
  if-β-false : {t f : TmExpr Γ T} → (Γ ∣ φs ⊢ if false t f ≡ᶠ f)
  pair-β-fst : {t : TmExpr Γ T} {s : TmExpr Γ S} →
               (Γ ∣ φs ⊢ fst (pair t s) ≡ᶠ t)
  pair-β-snd : {t : TmExpr Γ T} {s : TmExpr Γ S} →
               (Γ ∣ φs ⊢ snd (pair t s) ≡ᶠ s)

  -- Induction schemata for Bool' and Nat'.
  bool-induction : (Γ ∣ φs [ id-subst ∷ true ]frm-env ⊢ φ [ id-subst ∷ true ]frm) →
                   (Γ ∣ φs [ id-subst ∷ false ]frm-env ⊢ φ [ id-subst ∷ false ]frm) →
                   (Γ ,, Bool' ∣ φs ⊢ φ)
  nat-induction : (Γ ∣ φs [ id-subst ∷ lit 0 ]frm-env ⊢ φ [ id-subst ∷ lit 0 ]frm) →
                  (Γ ,, Nat' ∣ (φs [ π ∷ (suc ∙ var vzero) ]frm-env) ∷ φ ⊢ φ [ π ∷ (suc ∙ var vzero) ]frm) →
                  (Γ ,, Nat' ∣ φs ⊢ φ)


⟦_∣_⟧ctx-env : (Γ : CtxExpr) → FrmEnv Γ → Ctx ★
forget-assumptions : {Γ : CtxExpr} (φs : FrmEnv Γ) → ⟦ Γ ∣ φs ⟧ctx-env M.⇒ ⟦ Γ ⟧ctx

⟦ Γ ∣ []     ⟧ctx-env = ⟦ Γ ⟧ctx
⟦ Γ ∣ φs ∷ φ ⟧ctx-env = ⟦ Γ ∣ φs ⟧ctx-env M.,, (⟦ φ ⟧frm M.[ forget-assumptions φs ])

forget-assumptions [] = M.id-subst _
forget-assumptions (φs ∷ φ) = forget-assumptions φs M.⊚ M.π


interpret-assumption : Assumption φs φ → Tm ⟦ Γ ∣ φs ⟧ctx-env (⟦ φ ⟧frm M.[ forget-assumptions φs ])
interpret-assumption azero    = M.ι⁻¹[ M.ty-subst-comp _ _ _ ] M.ξ
interpret-assumption (asuc x) = M.ι⁻¹[ M.ty-subst-comp _ _ _ ] (interpret-assumption x M.[ M.π ]')

⟦_⟧der : (Γ ∣ φs ⊢ φ) → Tm ⟦ Γ ∣ φs ⟧ctx-env (⟦ φ ⟧frm M.[ forget-assumptions φs ])
⟦ refl ⟧der = (M.refl' _) M.[ _ ]'
⟦ sym d ⟧der = M.ι[ M.Id-natural _ ] M.sym' (M.ι⁻¹[ M.Id-natural _ ] ⟦ d ⟧der)
⟦ trans d1 d2 ⟧der = M.ι[ M.Id-natural _ ] M.trans' (M.ι⁻¹[ M.Id-natural _ ] ⟦ d1 ⟧der) (M.ι⁻¹[ M.Id-natural _ ] ⟦ d2 ⟧der)
⟦ cong f {t1 = t1} {t2 = t2} d ⟧der = M.ι[ M.≅ᵗʸ-trans (M.Id-natural _) (M.Id-cong' (M.app-natural _ ⟦ f ⟧tm ⟦ t1 ⟧tm) (M.app-natural _ ⟦ f ⟧tm ⟦ t2 ⟧tm)) ]
  M.cong' (M.ι⁻¹[ M.⇛-natural _ ] (⟦ f ⟧tm M.[ _ ]')) (M.ι⁻¹[ M.Id-natural _ ] ⟦ d ⟧der)
⟦ fun-cong d t ⟧der = {!!}
⟦ assume d ⟧der = M.ι[ M.⇛-natural _ ] M.lam _ (M.ι[ M.ty-subst-comp _ _ _ ] ⟦ d ⟧der)
⟦ assumption x ⟧der = interpret-assumption x
⟦ ∧-intro d1 d2 ⟧der = M.ι[ M.⊠-natural _ ] M.app (M.app M.pair ⟦ d1 ⟧der) ⟦ d2 ⟧der
⟦ ∧-elimˡ d ⟧der = M.app M.fst (M.ι⁻¹[ M.⊠-natural _ ] ⟦ d ⟧der)
⟦ ∧-elimʳ d ⟧der = M.app M.snd (M.ι⁻¹[ M.⊠-natural _ ] ⟦ d ⟧der)
⟦ ∀-intro d ⟧der = {!!}
⟦ ∀-elim d t ⟧der = {!!}
⟦ fun-β ⟧der = {!!} M.[ _ ]'
⟦ suc-lit ⟧der = M.≅ᵗᵐ-to-Id M.suc'-discr M.[ _ ]'
⟦ nat-elim-β-zero {a = a} ⟧der = M.≅ᵗᵐ-to-Id (M.β-nat-zero ⟦ a ⟧tm _) M.[ _ ]'
⟦ nat-elim-β-suc {a = a} {f = f} {n = n} ⟧der = M.≅ᵗᵐ-to-Id (M.β-nat-suc ⟦ a ⟧tm ⟦ f ⟧tm ⟦ n ⟧tm) M.[ _ ]'
⟦ if-β-true {t = t} {f = f} ⟧der = M.≅ᵗᵐ-to-Id (M.β-bool-true ⟦ t ⟧tm ⟦ f ⟧tm) M.[ _ ]'
⟦ if-β-false {t = t} {f = f} ⟧der = M.≅ᵗᵐ-to-Id (M.β-bool-false ⟦ t ⟧tm ⟦ f ⟧tm) M.[ _ ]'
⟦ pair-β-fst {t = t} {s = s} ⟧der = M.≅ᵗᵐ-to-Id (M.β-⊠-prim-fst ⟦ t ⟧tm ⟦ s ⟧tm) M.[ _ ]'
⟦ pair-β-snd {t = t} {s = s} ⟧der = M.≅ᵗᵐ-to-Id (M.β-⊠-prim-snd ⟦ t ⟧tm ⟦ s ⟧tm) M.[ _ ]'
⟦ bool-induction d1 d2 ⟧der = {!!}
⟦ nat-induction d1 d2 ⟧der = {!!}
