module Experimental.LogicalFramework.Derivation where

open import Data.Nat
import Relation.Binary.PropositionalEquality as A≡

open import Model.BaseCategory
open import Model.CwF-Structure as M using (Ctx; Ty; Tm)
open import Model.CwF-Structure.Reflection.SubstitutionSequence renaming (_∷_ to _∷ˢ_)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Discrete as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.Function as MDF

import Experimental.ClosedTypes as M
import Experimental.ClosedTypes.Pi as M
import Experimental.ClosedTypes.Identity as M

open import Experimental.LogicalFramework.STT
open import Experimental.LogicalFramework.Formula

private variable
  Γ Δ : CtxExpr
  T S R U : TyExpr
  φ ψ : Formula Γ


--------------------------------------------------
-- Definition of proof judgments and inference rules


-- A proof context can, apart from STT variables, also consist of formulas (assumptions).
data ProofCtx : Set
to-ctx : ProofCtx → CtxExpr

infixl 2 _∷ᵛ_ _∷ᶠ_
data ProofCtx where
  [] : ProofCtx
  _∷ᵛ_ : (Ξ : ProofCtx) (T : TyExpr) → ProofCtx
  _∷ᶠ_ : (Ξ : ProofCtx) (φ : Formula (to-ctx Ξ)) → ProofCtx

to-ctx []       = ◇
to-ctx (Ξ ∷ᵛ T) = to-ctx Ξ ,, T
to-ctx (Ξ ∷ᶠ φ) = to-ctx Ξ

private variable
  Ξ : ProofCtx


data Assumption : (Ξ : ProofCtx) → Formula (to-ctx Ξ) → Set where
  azero : Assumption (Ξ ∷ᶠ φ) φ
  asuc  : Assumption Ξ φ → Assumption (Ξ ∷ᶠ ψ) φ
  skip-var : Assumption Ξ φ → Assumption (Ξ ∷ᵛ T) (φ [ π ]frm)


infix 1 _⊢_
data _⊢_ : (Ξ : ProofCtx) → Formula (to-ctx Ξ) → Set where
  -- Structural rules for ≡ᶠ
  refl : {t : TmExpr (to-ctx Ξ) T} → Ξ ⊢ t ≡ᶠ t
  sym : {t1 t2 : TmExpr (to-ctx Ξ) T} → (Ξ ⊢ t1 ≡ᶠ t2) → (Ξ ⊢ t2 ≡ᶠ t1)
  trans : {t1 t2 t3 : TmExpr (to-ctx Ξ) T} →
          (Ξ ⊢ t1 ≡ᶠ t2) → (Ξ ⊢ t2 ≡ᶠ t3) →
          (Ξ ⊢ t1 ≡ᶠ t3)
  subst : (φ : Formula (to-ctx (Ξ ∷ᵛ T))) {t1 t2 : TmExpr (to-ctx Ξ) T} →
          (Ξ ⊢ t1 ≡ᶠ t2) →
          (Ξ ⊢ φ [ t1 /var0 ]frm) →
          (Ξ ⊢ φ [ t2 /var0 ]frm)

  -- Introduction and elimination for logical combinators ⊃, ∧ and ∀.
  assume : (Ξ ∷ᶠ φ ⊢ ψ) → (Ξ ⊢ φ ⊃ ψ)
  assumption : Assumption Ξ φ → Ξ ⊢ φ
  ∧-intro : (Ξ ⊢ φ) → (Ξ ⊢ ψ) → (Ξ ⊢ φ ∧ ψ)
  ∧-elimˡ : (Ξ ⊢ φ ∧ ψ) → (Ξ ⊢ φ)
  ∧-elimʳ : (Ξ ⊢ φ ∧ ψ) → (Ξ ⊢ ψ)
  ∀-intro : (Ξ ∷ᵛ T ⊢ φ) → (Ξ ⊢ ∀[ T ] φ)
  ∀-elim : (Ξ ⊢ ∀[ T ] φ) → (t : TmExpr (to-ctx Ξ) T) → (Ξ ⊢ φ [ t /var0 ]frm)

  -- Specific computation rules for term formers (currently no eta rules).
  fun-β : {b : TmExpr (to-ctx Ξ ,, T) S} {t : TmExpr (to-ctx Ξ) T} →
          (Ξ ⊢ lam b ∙ t ≡ᶠ (b [ t /var0 ]tm))
  nat-elim-β-zero : {A : TyExpr} {a : TmExpr (to-ctx Ξ) A} {f : TmExpr (to-ctx Ξ) (A ⇛ A)} →
                    (Ξ ⊢ nat-elim a f ∙ zero ≡ᶠ a)
  nat-elim-β-suc : {A : TyExpr} {a : TmExpr (to-ctx Ξ) A} {f : TmExpr (to-ctx Ξ) (A ⇛ A)} {n : TmExpr (to-ctx Ξ) Nat'} →
                   (Ξ ⊢ nat-elim a f ∙ (suc ∙ n) ≡ᶠ f ∙ (nat-elim a f ∙ n))
  if-β-true : {t f : TmExpr (to-ctx Ξ) T} → (Ξ ⊢ if true t f ≡ᶠ t)
  if-β-false : {t f : TmExpr (to-ctx Ξ) T} → (Ξ ⊢ if false t f ≡ᶠ f)
  pair-β-fst : {t : TmExpr (to-ctx Ξ) T} {s : TmExpr (to-ctx Ξ) S} →
               (Ξ ⊢ fst (pair t s) ≡ᶠ t)
  pair-β-snd : {t : TmExpr (to-ctx Ξ) T} {s : TmExpr (to-ctx Ξ) S} →
               (Ξ ⊢ snd (pair t s) ≡ᶠ s)

  -- Induction schemata for Bool' and Nat'.
  bool-induction : (Ξ ⊢ φ [ true /var0 ]frm) →
                   (Ξ ⊢ φ [ false /var0 ]frm) →
                   (Ξ ∷ᵛ Bool' ⊢ φ)
  nat-induction : (Ξ ⊢ φ [ zero /var0 ]frm) →
                  (Ξ ∷ᵛ Nat' ∷ᶠ φ ⊢ φ [ π ∷ (suc ∙ var vzero) ]frm) →
                  (Ξ ∷ᵛ Nat' ⊢ φ)


--------------------------------------------------
-- Some rules derivable from the basic ones

TmConstructor₁ : (T S : TyExpr) → Set
TmConstructor₁ T S = ∀ {Γ} → TmExpr Γ T → TmExpr Γ S

-- The naturality condition could be more strict (requiring the same
-- condition for all substitutions instead of restricting to those of
-- the form r /var0), but this condition suffices to show that the
-- corresponding constructor is congruent and this condition will be
-- provable by reflexivity for most term constructors.
TmConstructorNatural₁ : TmConstructor₁ T S → Set
TmConstructorNatural₁ {T} op = ∀ {Γ R} → (r : TmExpr Γ R) (t : TmExpr (Γ ,, R) T) → (op t) [ r /var0 ]tm A≡.≡ op (t [ r /var0 ]tm)

tm-constructor-cong₁ : (op : TmConstructor₁ T S) (op-nat : TmConstructorNatural₁ op) →
                      {t t' : TmExpr (to-ctx Ξ) T} →
                      (Ξ ⊢ t ≡ᶠ t') →
                      (Ξ ⊢ op t ≡ᶠ op t')
tm-constructor-cong₁ {Ξ = Ξ} op op-nat {t} {t'} et =
  -- goal : Ξ ⊢ op t ≡ᶠ op t'
  A≡.subst (λ x → Ξ ⊢ x ≡ᶠ op t') (tm-weaken-subst-trivial (op t) t') (
  -- goal : Ξ ⊢ (op t) [ π ]tm [ t' /var0 ]tm ≡ᶠ op t'
  A≡.subst (λ x → Ξ ⊢ ((op t) [ π ]tm [ t' /var0 ]tm) ≡ᶠ x) (op-nat t' (var vzero)) (
  -- goal : Ξ ⊢ (op t) [ π ]tm [ t' /var0 ]tm ≡ᶠ (op (var vzero)) [ t' /var0 ]tm
  subst (((op t) [ π ]tm) ≡ᶠ op (var vzero)) et (
  -- goal : Ξ ⊢ (op t) [ π ]tm [ t /var0 ]tm ≡ᶠ (op (var vzero)) [ t /var0 ]tm
  A≡.subst (λ x → Ξ ⊢ x ≡ᶠ ((op (var vzero)) [ t /var0 ]tm)) (A≡.sym (tm-weaken-subst-trivial (op t) t)) (
  -- goal : Ξ ⊢ op t ≡ᶠ (op (var vzero)) [ t /var0 ]tm
  A≡.subst (λ x → Ξ ⊢ op t ≡ᶠ x) (A≡.sym (op-nat t (var vzero)))
  -- goal : Ξ ⊢ op t ≡ᶠ op t
  refl))))

TmConstructor₂ : (T S R : TyExpr) → Set
TmConstructor₂ T S R = ∀ {Γ} → TmExpr Γ T → TmExpr Γ S → TmExpr Γ R

TmConstructorNatural₂ : TmConstructor₂ T S R → Set
TmConstructorNatural₂ {T} {S} op =
  ∀ {Γ W} → (w : TmExpr Γ W) (t : TmExpr (Γ ,, W) T) (s : TmExpr (Γ ,, W) S) →
  (op t s) [ w /var0 ]tm A≡.≡ op (t [ w /var0 ]tm) (s [ w /var0 ]tm)

tm-constructor-cong₂ : (op : TmConstructor₂ T S R) → TmConstructorNatural₂ op →
                       {t t' : TmExpr (to-ctx Ξ) T} {s s' : TmExpr (to-ctx Ξ) S} →
                       (Ξ ⊢ t ≡ᶠ t') →
                       (Ξ ⊢ s ≡ᶠ s') →
                       (Ξ ⊢ op t s ≡ᶠ op t' s')
tm-constructor-cong₂ {Ξ = Ξ} op op-nat {t} {t'} {s} {s'} et es =
  -- goal : Ξ ⊢ op t s ≡ᶠ op t' s'
  A≡.subst (λ x → Ξ ⊢ x ≡ᶠ op t' s') (tm-weaken-subst-trivial (op t s) t') (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ t' /var0 ]tm ≡ᶠ op t' s'
  A≡.subst (λ x → Ξ ⊢ ((op t s) [ π ]tm [ t' /var0 ]tm) ≡ᶠ op t' x) (tm-weaken-subst-trivial s' t') (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ t' /var0 ]tm ≡ᶠ op t' (s' [ π ]tm [ t' /var0 ]tm)
  A≡.subst (λ x → Ξ ⊢ ((op t s) [ π ]tm [ t' /var0 ]tm) ≡ᶠ x) (op-nat t' (var vzero) (s' [ π ]tm)) (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ t' /var0 ]tm ≡ᶠ (op (var vzero) (s' [ π ]tm)) [ t' /var0 ]tm
  subst (((op t s) [ π ]tm) ≡ᶠ op (var vzero) (s' [ π ]tm)) et (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ t /var0 ]tm ≡ᶠ (op (var vzero) (s' [ π ]tm)) [ t /var0 ]tm
  A≡.subst (λ x → Ξ ⊢ x ≡ᶠ ((op (var vzero) (s' [ π ]tm)) [ t /var0 ]tm)) (A≡.sym (tm-weaken-subst-trivial (op t s) t)) (
  -- goal : Ξ ⊢ op t s ≡ᶠ (op (var vzero) (s' [ π ]tm)) [ t /var0 ]tm
  A≡.subst (λ x → Ξ ⊢ op t s ≡ᶠ x) (A≡.sym (op-nat t (var vzero) (s' [ π ]tm))) (
  -- goal : Ξ ⊢ op t s ≡ᶠ op t (s' [ π ]tm [ t /var0 ]tm)
  A≡.subst (λ x → Ξ ⊢ op t s ≡ᶠ op t x) (A≡.sym (tm-weaken-subst-trivial s' t)) (
  -- goal : Ξ ⊢ op t s ≡ᶠ op t s'
  A≡.subst (λ x → Ξ ⊢ x ≡ᶠ op t s') (tm-weaken-subst-trivial (op t s) s') (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ s' /var0 ]tm ≡ᶠ op t s'
  A≡.subst (λ x → Ξ ⊢ ((op t s) [ π ]tm [ s' /var0 ]tm) ≡ᶠ op x s') (tm-weaken-subst-trivial t s') (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ s' /var0 ]tm ≡ᶠ op (t [ π ]tm [ s' /var0 ]tm) s'
  A≡.subst (λ x → Ξ ⊢ ((op t s) [ π ]tm [ s' /var0 ]tm) ≡ᶠ x) (op-nat s' (t [ π ]tm) (var vzero)) (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ s' /var0 ]tm ≡ᶠ (op (t [ π ]tm) (var vzero)) [ s' /var0 ]tm
  subst (((op t s) [ π ]tm) ≡ᶠ op (t [ π ]tm) (var vzero)) es (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ s /var0 ]tm ≡ᶠ (op (t [ π ]tm) (var vzero)) [ s /var0 ]tm
  A≡.subst (λ x → Ξ ⊢ x ≡ᶠ ((op (t [ π ]tm) (var vzero)) [ s /var0 ]tm)) (A≡.sym (tm-weaken-subst-trivial (op t s) s)) (
  -- goal : Ξ ⊢ op t s ≡ᶠ (op (t [ π ]tm) (var vzero)) [ s /var0 ]tm
  A≡.subst (λ x → Ξ ⊢ op t s ≡ᶠ x) (A≡.sym (op-nat s (t [ π ]tm) (var vzero))) (
  -- goal : Ξ ⊢ op t s ≡ᶠ op (t [ π ]tm [ s /var0 ]tm) s
  A≡.subst (λ x → Ξ ⊢ op t s ≡ᶠ op x s) (A≡.sym (tm-weaken-subst-trivial t s)) (
  -- goal : Ξ ⊢ op t s ≡ᶠ op t s
  refl))))))))))))))

TmConstructor₃ : (R S T U : TyExpr) → Set
TmConstructor₃ R S T U = ∀ {Γ} → TmExpr Γ R → TmExpr Γ S → TmExpr Γ T → TmExpr Γ U

TmConstructorNatural₃ : TmConstructor₃ R S T U → Set
TmConstructorNatural₃ {R} {S} {T} op =
  ∀ {Γ V} → (v : TmExpr Γ V) (r : TmExpr (Γ ,, V) R) (s : TmExpr (Γ ,, V) S) (t : TmExpr (Γ ,, V) T) →
  (op r s t) [ v /var0 ]tm A≡.≡ op (r [ v /var0 ]tm) (s [ v /var0 ]tm) (t [ v /var0 ]tm)

tm-constructor-cong₃ : (op : TmConstructor₃ R S T U) → TmConstructorNatural₃ op →
                       {r r' : TmExpr (to-ctx Ξ) R} {s s' : TmExpr (to-ctx Ξ) S} {t t' : TmExpr (to-ctx Ξ) T} →
                       (Ξ ⊢ r ≡ᶠ r') →
                       (Ξ ⊢ s ≡ᶠ s') →
                       (Ξ ⊢ t ≡ᶠ t') →
                       (Ξ ⊢ op r s t ≡ᶠ op r' s' t')
tm-constructor-cong₃ {Ξ = Ξ} op op-nat {r} {r'} {s} {s'} {t} {t'} er es et =
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r' s' t'
  A≡.subst (λ x → Ξ ⊢ x ≡ᶠ op r' s' t') (tm-weaken-subst-trivial (op r s t) r') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ r' /var0 ]tm ≡ᶠ op r' s' t'
  A≡.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ r' /var0 ]tm) ≡ᶠ op r' x t') (tm-weaken-subst-trivial s' r') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ r' /var0 ]tm ≡ᶠ op r' (s' [ π ]tm [ r' /var0 ]tm) t'
  A≡.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ r' /var0 ]tm) ≡ᶠ op r' (s' [ π ]tm [ r' /var0 ]tm) x) (tm-weaken-subst-trivial t' r') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ r' /var0 ]tm ≡ᶠ op r' (s' [ π ]tm [ r' /var0 ]tm) (t' [ π ]tm [ r' /var0 ]tm)
  A≡.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ r' /var0 ]tm) ≡ᶠ x) (op-nat r' (var vzero) (s' [ π ]tm) (t' [ π ]tm)) (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ r' /var0 ]tm ≡ᶠ (op (var vzero) (s' [ π ]tm) (t' [ π ]tm)) [ r' /var0 ]tm
  subst (((op r s t) [ π ]tm) ≡ᶠ op (var vzero) (s' [ π ]tm) (t' [ π ]tm)) er (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ r /var0 ]tm ≡ᶠ (op (var vzero) (s' [ π ]tm) (t' [ π ]tm)) [ r /var0 ]tm
  A≡.subst (λ x → Ξ ⊢ x ≡ᶠ ((op (var vzero) (s' [ π ]tm) (t' [ π ]tm)) [ r /var0 ]tm)) (A≡.sym (tm-weaken-subst-trivial (op r s t) r)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ (op (var vzero) (s' [ π ]tm) (t' [ π ]tm)) [ r /var0 ]tm
  A≡.subst (λ x → Ξ ⊢ op r s t ≡ᶠ x) (A≡.sym (op-nat r (var vzero) (s' [ π ]tm) (t' [ π ]tm))) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r (s' [ π ]tm [ r /var0 ]tm) (t' [ π ]tm [ r /var0 ]tm)
  A≡.subst (λ x → Ξ ⊢ op r s t ≡ᶠ op r x (t' [ π ]tm [ r /var0 ]tm)) (A≡.sym (tm-weaken-subst-trivial s' r)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r s' (t' [ π ]tm [ r /var0 ]tm)
  A≡.subst (λ x → Ξ ⊢ op r s t ≡ᶠ op r s' x) (A≡.sym (tm-weaken-subst-trivial t' r)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r s' t'
  A≡.subst (λ x → Ξ ⊢ x ≡ᶠ op r s' t') (tm-weaken-subst-trivial (op r s t) s') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ s' /var0 ]tm ≡ᶠ op r s' t'
  A≡.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ s' /var0 ]tm) ≡ᶠ op x s' t') (tm-weaken-subst-trivial r s') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ s' /var0 ]tm ≡ᶠ op (r [ π ]tm [ s' /var0 ]tm) s' t'
  A≡.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ s' /var0 ]tm) ≡ᶠ op (r [ π ]tm [ s' /var0 ]tm) s' x) (tm-weaken-subst-trivial t' s') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ s' /var0 ]tm ≡ᶠ op (r [ π ]tm [ s' /var0 ]tm) s' (t' [ π ]tm [ s' /var0 ]tm)
  A≡.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ s' /var0 ]tm) ≡ᶠ x) (op-nat s' (r [ π ]tm) (var vzero) (t' [ π ]tm)) (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ s' /var0 ]tm ≡ᶠ (op (r [ π ]tm) (var vzero) (t' [ π ]tm)) [ s' /var0 ]tm
  subst (((op r s t) [ π ]tm) ≡ᶠ op (r [ π ]tm) (var vzero) (t' [ π ]tm)) es (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ s /var0 ]tm ≡ᶠ (op (r [ π ]tm) (var vzero) (t' [ π ]tm)) [ s /var0 ]tm
  A≡.subst (λ x → Ξ ⊢ x ≡ᶠ ((op (r [ π ]tm) (var vzero) (t' [ π ]tm)) [ s /var0 ]tm)) (A≡.sym (tm-weaken-subst-trivial (op r s t) s)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ (op (r [ π ]tm) (var vzero) (t' [ π ]tm)) [ s /var0 ]tm
  A≡.subst (λ x → Ξ ⊢ op r s t ≡ᶠ x) (A≡.sym (op-nat s (r [ π ]tm) (var vzero) (t' [ π ]tm))) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op (r [ π ]tm [ s /var0 ]tm) s (t' [ π ]tm [ s /var0 ]tm)
  A≡.subst (λ x → Ξ ⊢ op r s t ≡ᶠ op x s (t' [ π ]tm [ s /var0 ]tm)) (A≡.sym (tm-weaken-subst-trivial r s)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r s (t' [ π ]tm [ s /var0 ]tm)
  A≡.subst (λ x → Ξ ⊢ op r s t ≡ᶠ op r s x) (A≡.sym (tm-weaken-subst-trivial t' s)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r s t'
  A≡.subst (λ x → Ξ ⊢ x ≡ᶠ op r s t') (tm-weaken-subst-trivial (op r s t) t') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ t' /var0 ]tm ≡ᶠ op r s t'
  A≡.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ t' /var0 ]tm) ≡ᶠ op x s t') (tm-weaken-subst-trivial r t') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ t' /var0 ]tm ≡ᶠ op (r [ π ]tm [ t' /var0 ]tm) s t'
  A≡.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ t' /var0 ]tm) ≡ᶠ op (r [ π ]tm [ t' /var0 ]tm) x t') (tm-weaken-subst-trivial s t') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ t' /var0 ]tm ≡ᶠ op (r [ π ]tm [ t' /var0 ]tm) (s [ π ]tm [ t' /var0 ]tm) t' 
  A≡.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ t' /var0 ]tm) ≡ᶠ x) (op-nat t' (r [ π ]tm) (s [ π ]tm) (var vzero)) (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ t' /var0 ]tm ≡ᶠ (op (r [ π ]tm) (s [ π ]tm) (var vzero)) [ t' /var0 ]tm
  subst (((op r s t) [ π ]tm) ≡ᶠ op (r [ π ]tm) (s [ π ]tm) (var vzero)) et (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ t /var0 ]tm ≡ᶠ (op (r [ π ]tm) (s [ π ]tm) (var vzero)) [ t /var0 ]tm
  A≡.subst (λ x → Ξ ⊢ x ≡ᶠ ((op (r [ π ]tm) (s [ π ]tm) (var vzero)) [ t /var0 ]tm)) (A≡.sym (tm-weaken-subst-trivial (op r s t) t)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ (op (r [ π ]tm) (s [ π ]tm) (var vzero)) [ t /var0 ]tm
  A≡.subst (λ x → Ξ ⊢ op r s t ≡ᶠ x) (A≡.sym (op-nat t (r [ π ]tm) (s [ π ]tm) (var vzero))) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op (r [ π ]tm [ t /var0 ]tm) (s [ π ]tm [ t /var0 ]tm) t
  A≡.subst (λ x → Ξ ⊢ op r s t ≡ᶠ op x (s [ π ]tm [ t /var0 ]tm) t) (A≡.sym (tm-weaken-subst-trivial r t)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r (s [ π ]tm [ s /var0 ]tm) t
  A≡.subst (λ x → Ξ ⊢ op r s t ≡ᶠ op r x t) (A≡.sym (tm-weaken-subst-trivial s t)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r s t'
  refl)))))))))))))))))))))))))))

fst-cong : {p p' : TmExpr (to-ctx Ξ) (T ⊠ S)} →
           (Ξ ⊢ p ≡ᶠ p') →
           (Ξ ⊢ fst p ≡ᶠ fst p')
fst-cong = tm-constructor-cong₁ fst (λ _ _ → A≡.refl)

snd-cong : {p p' : TmExpr (to-ctx Ξ) (T ⊠ S)} →
           (Ξ ⊢ p ≡ᶠ p') →
           (Ξ ⊢ snd p ≡ᶠ snd p')
snd-cong = tm-constructor-cong₁ snd (λ _ _ → A≡.refl)

simultaneous-fun-cong : {f f' : TmExpr (to-ctx Ξ) (T ⇛ S)} {t t' : TmExpr (to-ctx Ξ) T} →
                        (Ξ ⊢ f ≡ᶠ f') →
                        (Ξ ⊢ t ≡ᶠ t') →
                        (Ξ ⊢ f ∙ t ≡ᶠ f' ∙ t')
simultaneous-fun-cong = tm-constructor-cong₂ _∙_ (λ _ _ _ → A≡.refl)

cong : (f : TmExpr (to-ctx Ξ) (T ⇛ S)) {t1 t2 : TmExpr (to-ctx Ξ) T} →
       (Ξ ⊢ t1 ≡ᶠ t2) →
       (Ξ ⊢ f ∙ t1 ≡ᶠ f ∙ t2)
cong f = simultaneous-fun-cong refl

fun-cong : {f g : TmExpr (to-ctx Ξ) (T ⇛ S)} →
           (Ξ ⊢ f ≡ᶠ g) →
           (t : TmExpr (to-ctx Ξ) T) →
           (Ξ ⊢ f ∙ t ≡ᶠ g ∙ t)
fun-cong ef t = simultaneous-fun-cong ef refl

pair-cong : {t t' : TmExpr (to-ctx Ξ) T} {s s' : TmExpr (to-ctx Ξ) S} →
            (Ξ ⊢ t ≡ᶠ t') →
            (Ξ ⊢ s ≡ᶠ s') →
            (Ξ ⊢ pair t s ≡ᶠ pair t' s')
pair-cong = tm-constructor-cong₂ pair (λ _ _ _ → A≡.refl)

if-cong : {b b' : TmExpr (to-ctx Ξ) Bool'} {t t' f f' : TmExpr (to-ctx Ξ) T} →
          (Ξ ⊢ b ≡ᶠ b') →
          (Ξ ⊢ t ≡ᶠ t') →
          (Ξ ⊢ f ≡ᶠ f') →
          (Ξ ⊢ if b t f ≡ᶠ if b' t' f')
if-cong = tm-constructor-cong₃ if (λ _ _ _ _ → A≡.refl)


--------------------------------------------------
-- Soundness proof of the logical framework w.r.t. a trivial presheaf model

⟦_⟧env : ProofCtx → Ctx ★
to-ctx-subst : (Ξ : ProofCtx) → ⟦ Ξ ⟧env M.⇒ ⟦ to-ctx Ξ ⟧ctx

⟦ [] ⟧env = M.◇
⟦ Ξ ∷ᵛ T ⟧env = ⟦ Ξ ⟧env M.,,ₛ ⟦ T ⟧ty
⟦ Ξ ∷ᶠ φ ⟧env = ⟦ Ξ ⟧env M.,, (⟦ φ ⟧frm M.[ to-ctx-subst Ξ ])

to-ctx-subst [] = M.id-subst M.◇
to-ctx-subst (Ξ ∷ᵛ T) = to-ctx-subst Ξ M.s⊹
to-ctx-subst (Ξ ∷ᶠ φ) = to-ctx-subst Ξ M.⊚ M.π

interpret-assumption : Assumption Ξ φ → Tm ⟦ Ξ ⟧env (⟦ φ ⟧frm M.[ to-ctx-subst Ξ ])
interpret-assumption azero = M.ι⁻¹[ M.ty-subst-comp _ _ _ ] M.ξ
interpret-assumption (asuc x) = M.ι⁻¹[ M.ty-subst-comp _ _ _ ] (interpret-assumption x M.[ M.π ]')
interpret-assumption (skip-var {Ξ = Ξ} {φ = φ} {T = T} x) =
  M.ι⁻¹[ M.≅ᵗʸ-trans (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm subst-eq-proof)
                     (M.ty-subst-cong-ty _ (frm-subst-sound φ π))
       ]
  (interpret-assumption x M.[ M.π ]')
  where
    subst-eq-proof : _ M.≅ˢ _
    subst-eq-proof = M.≅ˢ-trans (M.≅ˢ-sym (M.,ₛ-β1 _ M.sξ)) (M.⊚-congʳ (M.≅ˢ-sym (M.⊚-id-substˡ _)))

⟦_⟧der : (Ξ ⊢ φ) → Tm ⟦ Ξ ⟧env (⟦ φ ⟧frm M.[ to-ctx-subst Ξ ])
⟦ refl ⟧der = M.refl' _ M.[ _ ]'
⟦ sym d ⟧der = M.ι[ M.Id-natural _ ] M.sym' (M.ι⁻¹[ M.Id-natural _ ] ⟦ d ⟧der)
⟦ trans d1 d2 ⟧der = M.ι[ M.Id-natural _ ] M.trans' (M.ι⁻¹[ M.Id-natural _ ] ⟦ d1 ⟧der) (M.ι⁻¹[ M.Id-natural _ ] ⟦ d2 ⟧der)
⟦ subst {Ξ = Ξ} φ {t1 = t1} {t2 = t2} e d ⟧der =
  M.ι[ M.≅ᵗʸ-trans (M.ty-subst-cong-ty _ (M.≅ᵗʸ-sym (frm-subst-sound φ (t2 /var0))))
                   (ty-subst-seq-cong (_ ∷ˢ _ ◼) ((to-ctx-subst Ξ M.,ₛ (⟦ t2 ⟧tm M.[ to-ctx-subst Ξ ]s)) ◼) ⟦ φ ⟧frm
                                      (M.≅ˢ-trans (M.,ₛ-⊚ _ _ _) (M.,ₛ-cong1 (M.⊚-id-substˡ _) _)))
     ]
  M.ssubst' ⟦ φ ⟧frm (to-ctx-subst Ξ) ⟦ e ⟧der (
  M.ι⁻¹[ M.≅ᵗʸ-trans (M.ty-subst-cong-ty _ (M.≅ᵗʸ-sym (frm-subst-sound φ (t1 /var0))))
                     (ty-subst-seq-cong (_ ∷ˢ _ ◼) ((to-ctx-subst Ξ M.,ₛ (⟦ t1 ⟧tm M.[ to-ctx-subst Ξ ]s)) ◼) ⟦ φ ⟧frm
                                        (M.≅ˢ-trans (M.,ₛ-⊚ _ _ _) (M.,ₛ-cong1 (M.⊚-id-substˡ _) _)))
     ]
  ⟦ d ⟧der)
⟦ assume d ⟧der = M.ι[ M.⇛-natural _ ] M.lam _ (M.ι[ M.ty-subst-comp _ _ _ ] ⟦ d ⟧der)
⟦ assumption x ⟧der = interpret-assumption x
⟦ ∧-intro d1 d2 ⟧der = M.ι[ M.⊠-natural _ ] M.prim-pair ⟦ d1 ⟧der ⟦ d2 ⟧der
⟦ ∧-elimˡ d ⟧der = M.prim-fst (M.ι⁻¹[ M.⊠-natural _ ] ⟦ d ⟧der)
⟦ ∧-elimʳ d ⟧der = M.prim-snd (M.ι⁻¹[ M.⊠-natural _ ] ⟦ d ⟧der)
⟦ ∀-intro d ⟧der = M.ι[ M.sPi-natural _ ] (M.sdλ[ _ ] ⟦ d ⟧der)
⟦ ∀-elim {Ξ = Ξ} {φ = φ} d t ⟧der =
  M.ι[ M.≅ᵗʸ-trans (M.≅ᵗʸ-sym (M.ty-subst-cong-ty _ (frm-subst-sound φ (t /var0))))
                   (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm (subst-lemma (to-ctx Ξ) (to-ctx-subst Ξ) ⟦ t ⟧tm))
     ]
  (M.sdapp (M.ι⁻¹[ M.sPi-natural _ ] ⟦ d ⟧der) (⟦ t ⟧tm M.[ to-ctx-subst Ξ ]s))
⟦ fun-β {Ξ = Ξ} {b = b} {t = t} ⟧der =
  (M.≅ᵗᵐ-to-Id (M.≅ᵗᵐ-trans (M.sfun-β _ _) (tm-subst-sound b (id-subst _ ∷ t))))
  M.[ _ ]'
⟦ nat-elim-β-zero ⟧der = (M.≅ᵗᵐ-to-Id (M.snat-β-zero _ _)) M.[ _ ]'
⟦ nat-elim-β-suc ⟧der = (M.≅ᵗᵐ-to-Id (M.snat-β-suc _ _ _)) M.[ _ ]'
⟦ if-β-true ⟧der = (M.≅ᵗᵐ-to-Id (M.sif-β-true _ _)) M.[ _ ]'
⟦ if-β-false ⟧der = (M.≅ᵗᵐ-to-Id (M.sif-β-false _ _)) M.[ _ ]'
⟦ pair-β-fst ⟧der = (M.≅ᵗᵐ-to-Id (M.sprod-β-fst _ _)) M.[ _ ]'
⟦ pair-β-snd ⟧der = (M.≅ᵗᵐ-to-Id (M.sprod-β-snd _ _)) M.[ _ ]'
⟦ bool-induction {Ξ = Ξ} {φ = φ} d1 d2 ⟧der =
  M.sbool-induction _ (M.ι[ M.≅ᵗʸ-trans (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm
                                                           (M.≅ˢ-trans (M.⊚-congˡ (M.,ₛ-cong2 _ (M.≅ᵗᵐ-sym (M.sdiscr-natural _))))
                                                                       (M.≅ˢ-sym (subst-lemma (to-ctx Ξ) (to-ctx-subst Ξ) M.strue))))
                                        (M.ty-subst-cong-ty _ (frm-subst-sound φ (true /var0)))
                          ] ⟦ d1 ⟧der)
                      (M.ι[ M.≅ᵗʸ-trans (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm
                                                           (M.≅ˢ-trans (M.⊚-congˡ (M.,ₛ-cong2 _ (M.≅ᵗᵐ-sym (M.sdiscr-natural _))))
                                                                       (M.≅ˢ-sym (subst-lemma (to-ctx Ξ) (to-ctx-subst Ξ) M.sfalse))))
                                        (M.ty-subst-cong-ty _ (frm-subst-sound φ (false /var0)))
                          ] ⟦ d2 ⟧der)
⟦ nat-induction {Ξ = Ξ} {φ = φ} d1 d2 ⟧der =
  M.snat-induction _ (M.ι[ M.≅ᵗʸ-trans (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm
                                                           (M.≅ˢ-trans (M.⊚-congˡ (M.,ₛ-cong2 _ (M.≅ᵗᵐ-sym (M.sdiscr-natural _))))
                                                                       (M.≅ˢ-sym (subst-lemma (to-ctx Ξ) (to-ctx-subst Ξ) M.szero))))
                                       (M.ty-subst-cong-ty _ (frm-subst-sound φ (zero /var0)))
                         ] ⟦ d1 ⟧der)
                     (M.ι[ M.≅ᵗʸ-trans (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm subst-eq-proof)
                                       (M.ty-subst-cong-ty _ (frm-subst-sound φ _))
                         ] ⟦ d2 ⟧der)
  where
    subst-eq-proof : _ M.≅ˢ _
    subst-eq-proof =
      M.≅ˢ-trans (M.≅ˢ-sym M.⊚-assoc) (M.≅ˢ-trans (M.⊚-congʳ (M.≅ˢ-trans (M.,ₛ-⊚ _ _ _) (M.≅ˢ-trans
      (M.≅ˢ-trans (M.,ₛ-cong1 (M.≅ˢ-trans M.⊚-assoc (M.≅ˢ-trans (M.⊚-congˡ (M.,ₛ-β1 _ _)) (M.≅ˢ-trans (M.≅ˢ-sym (M.,ₛ-β1 _ _)) (M.⊚-congʳ (M.≅ˢ-sym (M.⊚-id-substˡ _)))))) _)
                  (M.,ₛ-cong2 _ (M.≅ᵗᵐ-trans (M.,ₛ-β2 _ _) (M.≅ᵗᵐ-sym (M.≅ᵗᵐ-trans (M.∙ₛ-natural _) (M.∙ₛ-cong (M.sdiscr-func-natural _) (M.,ₛ-β2 _ _)))))))
      (M.≅ˢ-sym (M.,ₛ-⊚ _ _ _))))) M.⊚-assoc)
