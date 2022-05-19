module Experimental.ProgramLogic.InductionInduction.Derivations where

open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Experimental.ProgramLogic.InductionInduction.Definitions


private variable
  Γ Δ : CtxExpr
  T S : TyExpr
  φ ψ : Formula Γ

infix 1 _⊢_
data _⊢_ : (Γ : CtxExpr) → Formula Γ → Set where
  -- Structural rules for ≡ᶠ
  refl' : {t : TmExpr Γ T} → Γ ⊢ t ≡ᶠ t
  sym' : {t1 t2 : TmExpr Γ T} → (Γ ⊢ t1 ≡ᶠ t2) → (Γ ⊢ t2 ≡ᶠ t1)
  trans' : {t1 t2 t3 : TmExpr Γ T} →
          (Γ ⊢ t1 ≡ᶠ t2) → (Γ ⊢ t2 ≡ᶠ t3) →
          (Γ ⊢ t1 ≡ᶠ t3)
  cong' : (f : TmExpr Γ (T ⇛ S)) {t1 t2 : TmExpr Γ T} →
         (Γ ⊢ t1 ≡ᶠ t2) →
         (Γ ⊢ f ∙ t1 ≡ᶠ f ∙ t2)
  fun-cong : {f g : TmExpr Γ (T ⇛ S)} →
             (Γ ⊢ f ≡ᶠ g) →
             (t : TmExpr Γ T) →
             (Γ ⊢ f ∙ t ≡ᶠ g ∙ t)

  -- Introduction and elimination for logical combinators ⊃, ∧ and ∀.
  -- assume : (Γ ,,ᶠ φ ⊢ ψ) → (Γ ⊢ φ ⊃ {!!})
  -- assumption : Assumption Γ φ → Γ ⊢ φ
  ∧-intro : (Γ ⊢ φ) → (Γ ⊢ ψ) → (Γ ⊢ φ ∧ ψ)
  ∧-elimˡ : (Γ ⊢ φ ∧ ψ) → (Γ ⊢ φ)
  ∧-elimʳ : (Γ ⊢ φ ∧ ψ) → (Γ ⊢ ψ)
  ∀-intro : (Γ ,,ᵛ T ⊢ φ) → (Γ ⊢ ∀[ T ] φ)
  -- ∀-elim : (Γ ⊢ ∀[ T ] φ) → (t : TmExpr Γ T) → (Γ ⊢ φ [ id-subst ∷ t ]frm)

  -- -- Specific computation rules for term formers (currently no eta rules).
  -- fun-β : {b : TmExpr (to-ctx Γ ,, T) S} {t : TmExpr Γ T} →
  --         (Γ ⊢ lam b ∙ t ≡ᶠ (b [ id-subst ∷ t ]tm))
  -- suc-lit : {n : ℕ} → (Γ ⊢ (suc ∙ lit n) ≡ᶠ lit (suc n))
  -- nat-elim-β-zero : {A : TyExpr} {a : TmExpr Γ A} {f : TmExpr Γ (A ⇛ A)} →
  --                   (Γ ⊢ nat-elim a f ∙ lit 0 ≡ᶠ a)
  -- nat-elim-β-suc : {A : TyExpr} {a : TmExpr Γ A} {f : TmExpr Γ (A ⇛ A)} {n : TmExpr Γ Nat'} →
  --                  (Γ ⊢ nat-elim a f ∙ (suc ∙ n) ≡ᶠ f ∙ (nat-elim a f ∙ n))
  -- if-β-true : {t f : TmExpr Γ T} → (Γ ⊢ if true t f ≡ᶠ t)
  -- if-β-false : {t f : TmExpr Γ T} → (Γ ⊢ if false t f ≡ᶠ f)
  -- pair-β-fst : {t : TmExpr Γ T} {s : TmExpr Γ S} →
  --              (Γ ⊢ fst (pair t s) ≡ᶠ t)
  -- pair-β-snd : {t : TmExpr Γ T} {s : TmExpr Γ S} →
  --              (Γ ⊢ snd (pair t s) ≡ᶠ s)

  -- -- Induction schemata for Bool' and Nat'.
  -- bool-induction : (Γ ⊢ φ [ id-subst ∷ true ]frm) →
  --                  (Γ ⊢ φ [ id-subst ∷ false ]frm) →
  --                  (Γ ∷ᵛ Bool' ⊢ φ)
  -- nat-induction : (Γ ⊢ φ [ id-subst ∷ lit 0 ]frm) →
  --                 (Γ ∷ᵛ Nat' ∷ᶠ φ ⊢ φ [ π ∷ (suc ∙ var vzero) ]frm) →
  --                 (Γ ∷ᵛ Nat' ⊢ φ)

import Model.CwF-Structure as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Model.Type.Product as M
import Experimental.DependentTypes.Model.Function as M
import Model.Type.Function as M hiding (lam)

⟦_⟧der : Γ ⊢ φ → M.Tm ⟦ Γ ⟧ctx ⟦ φ ⟧frm
⟦ refl' ⟧der = M.refl' _
⟦ sym' d ⟧der = M.sym' ⟦ d ⟧der
⟦ trans' d1 d2 ⟧der = M.trans' ⟦ d1 ⟧der ⟦ d2 ⟧der
⟦ cong' f d ⟧der = M.cong' _ ⟦ d ⟧der
⟦ fun-cong d t ⟧der =
  M.fun-cong' (M.ι⁻¹[ M.Id-cong (M.⇛-natural _)
                                (M.≅ᵗᵐ-sym (M.ι-symʳ (M.⇛-natural _) _))
                                (M.≅ᵗᵐ-sym (M.ι-symʳ (M.⇛-natural _) _))
                    ] ⟦ d ⟧der)
              ⟦ t ⟧tm
⟦ ∧-intro dφ dψ ⟧der = M.prim-pair ⟦ dφ ⟧der ⟦ dψ ⟧der
⟦ ∧-elimˡ d ⟧der = M.prim-fst ⟦ d ⟧der
⟦ ∧-elimʳ d ⟧der = M.prim-snd ⟦ d ⟧der
⟦ ∀-intro d ⟧der = M.lam _ ⟦ d ⟧der
