{-# OPTIONS --allow-unsolved-metas #-}

module Experimental.LogicalFramework.Archive.BadClosedTypes.Derivation.OneEnvironment where

open import Data.Nat

open import Model.BaseCategory
open import Model.CwF-Structure as M using (Ctx; Ty; Tm)
open import Model.CwF-Structure.Reflection.SubstitutionSequence renaming (_∷_ to _∷ˢ_)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Constant as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.Function as MDF

open import Experimental.LogicalFramework.Archive.BadClosedTypes.STT
open import Experimental.LogicalFramework.Archive.BadClosedTypes.Formula

private variable
  Γ Δ : CtxExpr
  T S : TyExpr
  φ ψ : Formula Γ


-- Environment consisiting of (STT) variables and formulas.
data Env : Set
to-ctx : Env → CtxExpr

infixl 2 _∷ᵛ_ _∷ᶠ_
data Env where
  [] : Env
  _∷ᵛ_ : (Ξ : Env) (T : TyExpr) → Env
  _∷ᶠ_ : (Ξ : Env) (φ : Formula (to-ctx Ξ)) → Env

to-ctx []       = ◇
to-ctx (Ξ ∷ᵛ T) = to-ctx Ξ ,, T
to-ctx (Ξ ∷ᶠ φ) = to-ctx Ξ

private variable
  Ξ : Env


data Assumption : (Ξ : Env) → Formula (to-ctx Ξ) → Set where
  azero : Assumption (Ξ ∷ᶠ φ) φ
  asuc  : Assumption Ξ φ → Assumption (Ξ ∷ᶠ ψ) φ
  skip-var : Assumption Ξ φ → Assumption (Ξ ∷ᵛ T) (φ [ π ]frm)


infix 1 _⊢_
data _⊢_ : (Ξ : Env) → Formula (to-ctx Ξ) → Set where
  -- Structural rules for ≡ᶠ
  refl : {t : TmExpr (to-ctx Ξ) T} → Ξ ⊢ t ≡ᶠ t
  sym : {t1 t2 : TmExpr (to-ctx Ξ) T} → (Ξ ⊢ t1 ≡ᶠ t2) → (Ξ ⊢ t2 ≡ᶠ t1)
  trans : {t1 t2 t3 : TmExpr (to-ctx Ξ) T} →
          (Ξ ⊢ t1 ≡ᶠ t2) → (Ξ ⊢ t2 ≡ᶠ t3) →
          (Ξ ⊢ t1 ≡ᶠ t3)
  cong : (f : TmExpr (to-ctx Ξ) (T ⇛ S)) {t1 t2 : TmExpr (to-ctx Ξ) T} →
         (Ξ ⊢ t1 ≡ᶠ t2) →
         (Ξ ⊢ f ∙ t1 ≡ᶠ f ∙ t2)
  fun-cong : {f g : TmExpr (to-ctx Ξ) (T ⇛ S)} →
             (Ξ ⊢ f ≡ᶠ g) →
             (t : TmExpr (to-ctx Ξ) T) →
             (Ξ ⊢ f ∙ t ≡ᶠ g ∙ t)

  -- Introduction and elimination for logical combinators ⊃, ∧ and ∀.
  assume : (Ξ ∷ᶠ φ ⊢ ψ) → (Ξ ⊢ φ ⊃ ψ)
  assumption : Assumption Ξ φ → Ξ ⊢ φ
  ∧-intro : (Ξ ⊢ φ) → (Ξ ⊢ ψ) → (Ξ ⊢ φ ∧ ψ)
  ∧-elimˡ : (Ξ ⊢ φ ∧ ψ) → (Ξ ⊢ φ)
  ∧-elimʳ : (Ξ ⊢ φ ∧ ψ) → (Ξ ⊢ ψ)
  ∀-intro : (Ξ ∷ᵛ T ⊢ φ) → (Ξ ⊢ ∀[ T ] φ)
  ∀-elim : (Ξ ⊢ ∀[ T ] φ) → (t : TmExpr (to-ctx Ξ) T) → (Ξ ⊢ φ [ id-subst ∷ t ]frm)

  -- Specific computation rules for term formers (currently no eta rules).
  fun-β : {b : TmExpr (to-ctx Ξ ,, T) S} {t : TmExpr (to-ctx Ξ) T} →
          (Ξ ⊢ lam b ∙ t ≡ᶠ (b [ id-subst ∷ t ]tm))
  suc-lit : {n : ℕ} → (Ξ ⊢ (suc ∙ lit n) ≡ᶠ lit (suc n))
  nat-elim-β-zero : {A : TyExpr} {a : TmExpr (to-ctx Ξ) A} {f : TmExpr (to-ctx Ξ) (A ⇛ A)} →
                    (Ξ ⊢ nat-elim a f ∙ lit 0 ≡ᶠ a)
  nat-elim-β-suc : {A : TyExpr} {a : TmExpr (to-ctx Ξ) A} {f : TmExpr (to-ctx Ξ) (A ⇛ A)} {n : TmExpr (to-ctx Ξ) Nat'} →
                   (Ξ ⊢ nat-elim a f ∙ (suc ∙ n) ≡ᶠ f ∙ (nat-elim a f ∙ n))
  if-β-true : {t f : TmExpr (to-ctx Ξ) T} → (Ξ ⊢ if true t f ≡ᶠ t)
  if-β-false : {t f : TmExpr (to-ctx Ξ) T} → (Ξ ⊢ if false t f ≡ᶠ f)
  pair-β-fst : {t : TmExpr (to-ctx Ξ) T} {s : TmExpr (to-ctx Ξ) S} →
               (Ξ ⊢ fst (pair t s) ≡ᶠ t)
  pair-β-snd : {t : TmExpr (to-ctx Ξ) T} {s : TmExpr (to-ctx Ξ) S} →
               (Ξ ⊢ snd (pair t s) ≡ᶠ s)

  -- Induction schemata for Bool' and Nat'.
  bool-induction : (Ξ ⊢ φ [ id-subst ∷ true ]frm) →
                   (Ξ ⊢ φ [ id-subst ∷ false ]frm) →
                   (Ξ ∷ᵛ Bool' ⊢ φ)
  nat-induction : (Ξ ⊢ φ [ id-subst ∷ lit 0 ]frm) →
                  (Ξ ∷ᵛ Nat' ∷ᶠ φ ⊢ φ [ π ∷ (suc ∙ var vzero) ]frm) →
                  (Ξ ∷ᵛ Nat' ⊢ φ)


⟦_⟧env : Env → Ctx ★
to-ctx-subst : (Ξ : Env) → ⟦ Ξ ⟧env M.⇒ ⟦ to-ctx Ξ ⟧ctx

⟦ [] ⟧env = M.◇
⟦ Ξ ∷ᵛ T ⟧env = ⟦ Ξ ⟧env M.,, ⟦ T ⟧ty
⟦ Ξ ∷ᶠ φ ⟧env = ⟦ Ξ ⟧env M.,, (⟦ φ ⟧frm M.[ to-ctx-subst Ξ ])

to-ctx-subst [] = M.id-subst M.◇
to-ctx-subst (Ξ ∷ᵛ T) = ((to-ctx-subst Ξ) M.⊹) M.⊚ M._≅ᶜ_.to (M.,,-cong (ty-closed T))
to-ctx-subst (Ξ ∷ᶠ φ) = to-ctx-subst Ξ M.⊚ M.π

interpret-assumption : Assumption Ξ φ → Tm ⟦ Ξ ⟧env (⟦ φ ⟧frm M.[ to-ctx-subst Ξ ])
interpret-assumption azero = M.ι⁻¹[ M.ty-subst-comp _ _ _ ] M.ξ
interpret-assumption (asuc x) = M.ι⁻¹[ M.ty-subst-comp _ _ _ ] (interpret-assumption x M.[ M.π ]')
interpret-assumption (skip-var x) = {!interpret-assumption x!}

⟦_⟧der : (Ξ ⊢ φ) → Tm ⟦ Ξ ⟧env (⟦ φ ⟧frm M.[ to-ctx-subst Ξ ])
⟦ refl ⟧der = (M.refl' _) M.[ _ ]'
⟦ sym d ⟧der = M.ι[ M.Id-natural _ ] M.sym' (M.ι⁻¹[ M.Id-natural _ ] ⟦ d ⟧der)
⟦ trans d1 d2 ⟧der = M.ι[ M.Id-natural _ ] M.trans' (M.ι⁻¹[ M.Id-natural _ ] ⟦ d1 ⟧der) (M.ι⁻¹[ M.Id-natural _ ] ⟦ d2 ⟧der)
⟦ cong f {t1} {t2} d ⟧der =
  M.ι[ M.transᵗʸ (M.Id-natural _ {M.app ⟦ f ⟧tm ⟦ t1 ⟧tm} {M.app ⟦ f ⟧tm ⟦ t2 ⟧tm}) (M.Id-cong' (M.app-natural _ ⟦ f ⟧tm ⟦ t1 ⟧tm) (M.app-natural _ ⟦ f ⟧tm ⟦ t2 ⟧tm)) ]
    M.cong' (M.ι⁻¹[ M.⇛-natural _ ] (⟦ f ⟧tm M.[ _ ]')) {⟦ t1 ⟧tm M.[ _ ]'} {⟦ t2 ⟧tm M.[ _ ]'} (M.ι⁻¹[ M.Id-natural _ {⟦ t1 ⟧tm} {⟦ t2 ⟧tm} ] ⟦ d ⟧der)
⟦ fun-cong {f = f} {g = g} d t ⟧der =
  M.ι[ M.transᵗʸ (M.Id-natural _) (M.Id-cong' (M.app-natural _ ⟦ f ⟧tm ⟦ t ⟧tm) (M.app-natural _ ⟦ g ⟧tm ⟦ t ⟧tm)) ]
    M.fun-cong' (M.≅ᵗᵐ-to-Id (M.ι⁻¹-cong (M.⇛-natural _) (M.eq-reflect (M.ι⁻¹[ M.Id-natural _ ] ⟦ d ⟧der)))) (⟦ t ⟧tm M.[ _ ]')
⟦ assume d ⟧der = M.ι[ M.⇛-natural _ ] M.lam _ (M.ι[ M.ty-subst-comp _ _ _ ] ⟦ d ⟧der)
⟦ assumption x ⟧der = interpret-assumption x
⟦ ∧-intro d1 d2 ⟧der = M.ι[ M.⊠-natural _ ] M.prim-pair ⟦ d1 ⟧der ⟦ d2 ⟧der
⟦ ∧-elimˡ d ⟧der = M.prim-fst (M.ι⁻¹[ M.⊠-natural _ ] ⟦ d ⟧der)
⟦ ∧-elimʳ d ⟧der = M.prim-snd (M.ι⁻¹[ M.⊠-natural _ ] ⟦ d ⟧der)
⟦ ∀-intro {Ξ = Ξ} {T = T} {φ = φ} d ⟧der = M.ι[ M.transᵗʸ (MDF.Pi-natural _) (MDF.Pi-cong (ty-closed T) proof) ] (MDF.lam _ ⟦ d ⟧der)
  where
    proof : ⟦ φ ⟧frm M.[ (to-ctx-subst Ξ) M.⊹ ] M.≅ᵗʸ
              (⟦ φ ⟧frm M.[ ((to-ctx-subst Ξ) M.⊹) M.⊚ M.to (M.,,-cong (ty-closed T)) ]) M.[ M.from (M.,,-cong (ty-closed T)) ]
    proof = ty-subst-seq-cong (((to-ctx-subst Ξ) M.⊹) ◼)
                              (((to-ctx-subst Ξ) M.⊹) M.⊚ M.to (M.,,-cong (ty-closed T)) ∷ˢ M.from (M.,,-cong (ty-closed T)) ◼)
                              ⟦ φ ⟧frm
                              (M.symˢ (M.transˢ M.⊚-assoc (M.transˢ (M.⊚-congˡ (M.isoˡ (M.,,-cong (ty-closed T)))) (M.⊚-id-substʳ _))))
⟦ ∀-elim d t ⟧der = {!!}
⟦ fun-β ⟧der = {!!}
⟦ suc-lit ⟧der = M.≅ᵗᵐ-to-Id M.suc'-const M.[ _ ]'
⟦ nat-elim-β-zero {a = a} {f = f} ⟧der = M.≅ᵗᵐ-to-Id (M.β-nat-zero ⟦ a ⟧tm ⟦ f ⟧tm) M.[ _ ]'
⟦ nat-elim-β-suc {a = a} {f = f} {n = n} ⟧der = M.≅ᵗᵐ-to-Id (M.β-nat-suc ⟦ a ⟧tm ⟦ f ⟧tm ⟦ n ⟧tm) M.[ _ ]'
⟦ if-β-true {t = t} {f = f} ⟧der = M.≅ᵗᵐ-to-Id (M.β-bool-true ⟦ t ⟧tm ⟦ f ⟧tm) M.[ _ ]'
⟦ if-β-false {t = t} {f = f} ⟧der = M.≅ᵗᵐ-to-Id (M.β-bool-false ⟦ t ⟧tm ⟦ f ⟧tm) M.[ _ ]'
⟦ pair-β-fst {t = t} {s = s} ⟧der = M.≅ᵗᵐ-to-Id (M.β-⊠-prim-fst ⟦ t ⟧tm ⟦ s ⟧tm) M.[ _ ]'
⟦ pair-β-snd {t = t} {s = s} ⟧der = M.≅ᵗᵐ-to-Id (M.β-⊠-prim-snd ⟦ t ⟧tm ⟦ s ⟧tm) M.[ _ ]'
⟦ bool-induction d1 d2 ⟧der = {!!}
⟦ nat-induction d1 d2 ⟧der = {!!}
