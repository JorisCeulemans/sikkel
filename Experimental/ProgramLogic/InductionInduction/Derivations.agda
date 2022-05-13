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


⟦_⟧der : Γ ⊢ φ → ((γ : ⟦ Γ ⟧ctx) → ⟦ φ ⟧frm γ)
⟦ refl' ⟧der γ = refl
⟦ sym' d ⟧der γ = sym (⟦ d ⟧der γ)
⟦ trans' d1 d2 ⟧der γ = trans (⟦ d1 ⟧der γ) (⟦ d2 ⟧der γ)
⟦ cong' f d ⟧der γ = cong (⟦ f ⟧tm γ) (⟦ d ⟧der γ)
⟦ fun-cong d t ⟧der γ = cong (λ x → x (⟦ t ⟧tm γ)) (⟦ d ⟧der γ)
⟦ ∧-intro dφ dψ ⟧der γ = (⟦ dφ ⟧der γ) , (⟦ dψ ⟧der γ)
⟦ ∧-elimˡ d ⟧der γ = proj₁ (⟦ d ⟧der γ)
⟦ ∧-elimʳ d ⟧der γ = proj₂ (⟦ d ⟧der γ)
⟦ ∀-intro d ⟧der γ = λ t → ⟦ d ⟧der (γ , t)
