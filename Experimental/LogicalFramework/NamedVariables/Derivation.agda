module Experimental.LogicalFramework.NamedVariables.Derivation where

open import Data.Empty
open import Data.Nat
open import Data.String as Str
import Relation.Binary.PropositionalEquality as Ag
open Ag public using (refl)
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core

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

open import Experimental.LogicalFramework.NamedVariables.STT
open import Experimental.LogicalFramework.NamedVariables.Formula
open import Experimental.LogicalFramework.NamedVariables.Formula.Interpretation.Nameless using (⟦_⟧frm-nmls)
open import Experimental.LogicalFramework.NamedVariables.STT.Interpretation.Nameless using (⟦_⟧tm-nmls)

private variable
  Γ Δ : CtxExpr
  T S R U : TyExpr
  φ ψ : Formula Γ
  x y : String


--------------------------------------------------
-- Definition of proof judgments and inference rules


-- A proof context can, apart from STT variables, also consist of formulas (assumptions).
data ProofCtx : Set
to-ctx : ProofCtx → CtxExpr

infixl 2 _∷ᵛ_∈_ _∷ᶠ_∈_
data ProofCtx where
  [] : ProofCtx
  _∷ᵛ_∈_ : (Ξ : ProofCtx) (x : String) (T : TyExpr) → ProofCtx
  _∷ᶠ_∈_ : (Ξ : ProofCtx) (x : String) (φ : Formula (to-ctx Ξ)) → ProofCtx

to-ctx []       = ◇
to-ctx (Ξ ∷ᵛ x ∈ T) = to-ctx Ξ ,, x ∈ T
to-ctx (Ξ ∷ᶠ _ ∈ φ) = to-ctx Ξ

private variable
  Ξ : ProofCtx


data Assumption : String → ProofCtx → Set where
  azero : Assumption x (Ξ ∷ᶠ x ∈ φ)
  asuc  : Assumption x Ξ → Assumption x (Ξ ∷ᶠ y ∈ ψ)
  skip-var : Assumption x Ξ → Assumption x (Ξ ∷ᵛ y ∈ T)

assump-vpred : Assumption x (Ξ ∷ᵛ y ∈ T) → Assumption x Ξ
assump-vpred (skip-var a) = a

assump-apred : ¬ (x Ag.≡ y) → Assumption x (Ξ ∷ᶠ y ∈ φ) → Assumption x Ξ
assump-apred ¬x=y azero    = ⊥-elim (¬x=y Ag.refl)
assump-apred ¬x=y (asuc a) = a

assumption? : (x : String) (Ξ : ProofCtx) → Dec (Assumption x Ξ)
assumption? x [] = no (λ ())
assumption? x (Ξ ∷ᵛ y ∈ T) = map′ skip-var assump-vpred (assumption? x Ξ)
assumption? x (Ξ ∷ᶠ y ∈ φ) with x Str.≟ y
assumption? x (Ξ ∷ᶠ .x ∈ φ) | yes Ag.refl = yes azero
assumption? x (Ξ ∷ᶠ y ∈ φ)  | no ¬x=y = map′ asuc (assump-apred ¬x=y) (assumption? x Ξ)

lookup-assumption : Assumption x Ξ → Formula (to-ctx Ξ)
lookup-assumption (azero {φ = φ}) = φ
lookup-assumption (asuc a)        = lookup-assumption a
lookup-assumption (skip-var a)    = (lookup-assumption a) [ π ]frm


infix 1 _⊢_
data _⊢_ : (Ξ : ProofCtx) → Formula (to-ctx Ξ) → Set where
  -- Making sure that derivability respects alpha equivalence.
  -- This is not ideal, we would like to bake this into assumption' below.
  -- However see comment on withTmAlpha below for problems with that.
  withAlpha : {{ φ ≈αᶠ ψ }} → (Ξ ⊢ φ) → (Ξ ⊢ ψ)

  -- Structural rules for ≡ᶠ
  refl : {t s : TmExpr (to-ctx Ξ) T} → {{ t ≈α s }} → Ξ ⊢ t ≡ᶠ s
  sym : {t1 t2 : TmExpr (to-ctx Ξ) T} → (Ξ ⊢ t1 ≡ᶠ t2) → (Ξ ⊢ t2 ≡ᶠ t1)
  trans : {t1 t2 t3 : TmExpr (to-ctx Ξ) T} →
          (Ξ ⊢ t1 ≡ᶠ t2) → (Ξ ⊢ t2 ≡ᶠ t3) →
          (Ξ ⊢ t1 ≡ᶠ t3)
  subst : (φ : Formula (to-ctx (Ξ ∷ᵛ x ∈ T))) {t1 t2 : TmExpr (to-ctx Ξ) T} →
          (Ξ ⊢ t1 ≡ᶠ t2) →
          (Ξ ⊢ φ [ t1 / x ]frm) →
          (Ξ ⊢ φ [ t2 / x ]frm)

  -- Introduction and elimination for logical combinators ⊃, ∧ and ∀.
  assume[_]_ : (x : String) → (Ξ ∷ᶠ x ∈ φ ⊢ ψ) → (Ξ ⊢ φ ⊃ ψ)
  assumption' : (x : String) {a : Assumption x Ξ} → (Ξ ⊢ lookup-assumption a)
  ∧-intro : (Ξ ⊢ φ) → (Ξ ⊢ ψ) → (Ξ ⊢ φ ∧ ψ)
  ∧-elimˡ : (Ξ ⊢ φ ∧ ψ) → (Ξ ⊢ φ)
  ∧-elimʳ : (Ξ ⊢ φ ∧ ψ) → (Ξ ⊢ ψ)
  ∀-intro : (Ξ ∷ᵛ x ∈ T ⊢ φ) → (Ξ ⊢ ∀[ x ∈ T ] φ)
  ∀-elim : (Ξ ⊢ ∀[ x ∈ T ] φ) → (t : TmExpr (to-ctx Ξ) T) → (Ξ ⊢ φ [ t / x ]frm)

  -- Specific computation rules for term formers (currently no eta rules).
  fun-β : {b : TmExpr (to-ctx Ξ ,, x ∈ T) S} {t : TmExpr (to-ctx Ξ) T} →
          (Ξ ⊢ (lam[ x ∈ T ] b) ∙ t ≡ᶠ b [ t / x ]tm)
  nat-elim-β-zero : {A : TyExpr} {a : TmExpr (to-ctx Ξ) A} {f : TmExpr (to-ctx Ξ) (A ⇛ A)} →
                    (Ξ ⊢ nat-elim a f ∙ zero ≡ᶠ a)
  nat-elim-β-suc : {A : TyExpr} {a : TmExpr (to-ctx Ξ) A} {f : TmExpr (to-ctx Ξ) (A ⇛ A)} {n : TmExpr (to-ctx Ξ) Nat'} →
                   (Ξ ⊢ nat-elim a f ∙ (suc ∙ n) ≡ᶠ f ∙ (nat-elim a f ∙ n))
  if-β-true : {t f : TmExpr (to-ctx Ξ) T} →
              (Ξ ⊢ if true t f ≡ᶠ t)
  if-β-false : {t f : TmExpr (to-ctx Ξ) T} →
               (Ξ ⊢ if false t f ≡ᶠ f)
  pair-β-fst : {t : TmExpr (to-ctx Ξ) T} {s : TmExpr (to-ctx Ξ) S} →
               (Ξ ⊢ fst (pair t s) ≡ᶠ t)
  pair-β-snd : {t : TmExpr (to-ctx Ξ) T} {s : TmExpr (to-ctx Ξ) S} →
               (Ξ ⊢ snd (pair t s) ≡ᶠ s)

  -- Induction schemata for Bool' and Nat'.
  bool-induction : (Ξ ⊢ φ [ true / x ]frm) →
                   (Ξ ⊢ φ [ false / x ]frm) →
                   (Ξ ∷ᵛ x ∈ Bool' ⊢ φ)
  nat-induction : (hyp : String) →
                  (Ξ ⊢ φ [ zero / x ]frm) →
                  (Ξ ∷ᵛ x ∈ Nat' ∷ᶠ hyp ∈ φ ⊢ φ [ π ∷ (suc ∙ var' x {vzero} {Ag.refl}) / x ]frm) →
                  (Ξ ∷ᵛ x ∈ Nat' ⊢ φ)

assumption : (x : String) {a : True (assumption? x Ξ)} → (Ξ ⊢ lookup-assumption (toWitness a))
assumption x {a} = assumption' x {toWitness a}


--------------------------------------------------
-- Some rules derivable from the basic ones

-- Not all of the above inference rules respect α equivalence. Since
-- refl does respect α equivalence, the following can be used for the
-- other rules. This situation is not ideal: the user does not want to
-- explicitly mention withAlpha. However, changing the types of the
-- inference rules that do not respect α equivalence so that they look
-- like the type of refl, does lead to the problem that Agda cannot
-- infer the intermediate formulas in a chain of equalities (using
-- trans) any more. We should investigate if reflection might provide
-- a solution.
withTmAlpha : {t s s' : TmExpr (to-ctx Ξ) T} →
              (Ξ ⊢ t ≡ᶠ s) →
              {{ s ≈α s' }} →
              (Ξ ⊢ t ≡ᶠ s')
withTmAlpha t=s = trans t=s refl

TmConstructor₁ : (T S : TyExpr) → Set
TmConstructor₁ T S = ∀ {Γ} → TmExpr Γ T → TmExpr Γ S

-- The naturality condition could be more strict (requiring the same
-- condition for all substitutions instead of restricting to those of
-- the form r / x), but this condition suffices to show that the
-- corresponding constructor is congruent and this condition will be
-- provable by reflexivity for most term constructors.
TmConstructorNatural₁ : TmConstructor₁ T S → Set
TmConstructorNatural₁ {T} op = ∀ {Γ R x} → (r : TmExpr Γ R) (t : TmExpr (Γ ,, x ∈ R) T) → (op t) [ r / x ]tm Ag.≡ op (t [ r / x ]tm)

tm-constructor-cong₁ : (op : TmConstructor₁ T S) (op-nat : TmConstructorNatural₁ op) →
                       {t t' : TmExpr (to-ctx Ξ) T} →
                       (Ξ ⊢ t ≡ᶠ t') →
                       (Ξ ⊢ op t ≡ᶠ op t')
tm-constructor-cong₁ {Ξ = Ξ} op op-nat {t} {t'} et =
  -- goal : Ξ ⊢ op t ≡ᶠ op t'
  Ag.subst (λ x → Ξ ⊢ x ≡ᶠ op t') (tm-weaken-subst-trivial (op t) t') (
  -- goal : Ξ ⊢ (op t) [ π ]tm [ t' / "dummy" ]tm ≡ᶠ op t'
  Ag.subst (λ x → Ξ ⊢ ((op t) [ π ]tm [ t' / "dummy" ]tm) ≡ᶠ x) (op-nat t' (var "dummy")) (
  -- goal : Ξ ⊢ (op t) [ π ]tm [ t' / "dummy" ]tm ≡ᶠ (op (var "dummy")) [ t' / "dummy" ]tm
  subst (((op t) [ π ]tm) ≡ᶠ op (var "dummy")) et (
  -- goal : Ξ ⊢ (op t) [ π ]tm [ t / "dummy" ]tm ≡ᶠ (op (var "dummy")) [ t / "dummy" ]tm
  Ag.subst (λ x → Ξ ⊢ x ≡ᶠ ((op (var "dummy")) [ t / "dummy" ]tm)) (Ag.sym (tm-weaken-subst-trivial (op t) t)) (
  -- goal : Ξ ⊢ op t ≡ᶠ (op (var "dummy")) [ t / "dummy" ]tm
  Ag.subst (λ x → Ξ ⊢ op t ≡ᶠ x) (Ag.sym (op-nat t (var "dummy")))
  -- goal : Ξ ⊢ op t ≡ᶠ op t
  refl))))

TmConstructor₂ : (T S R : TyExpr) → Set
TmConstructor₂ T S R = ∀ {Γ} → TmExpr Γ T → TmExpr Γ S → TmExpr Γ R

TmConstructorNatural₂ : TmConstructor₂ T S R → Set
TmConstructorNatural₂ {T} {S} op =
  ∀ {Γ W x} → (w : TmExpr Γ W) (t : TmExpr (Γ ,, x ∈ W) T) (s : TmExpr (Γ ,, x ∈ W) S) →
  (op t s) [ w / x ]tm Ag.≡ op (t [ w / x ]tm) (s [ w / x ]tm)

tm-constructor-cong₂ : (op : TmConstructor₂ T S R) → TmConstructorNatural₂ op →
                       {t t' : TmExpr (to-ctx Ξ) T} {s s' : TmExpr (to-ctx Ξ) S} →
                       (Ξ ⊢ t ≡ᶠ t') →
                       (Ξ ⊢ s ≡ᶠ s') →
                       (Ξ ⊢ op t s ≡ᶠ op t' s')
tm-constructor-cong₂ {Ξ = Ξ} op op-nat {t} {t'} {s} {s'} et es =
  -- goal : Ξ ⊢ op t s ≡ᶠ op t' s'
  Ag.subst (λ x → Ξ ⊢ x ≡ᶠ op t' s') (tm-weaken-subst-trivial (op t s) t') (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ t' / "dummy" ]tm ≡ᶠ op t' s'
  Ag.subst (λ x → Ξ ⊢ ((op t s) [ π ]tm [ t' / "dummy" ]tm) ≡ᶠ op t' x) (tm-weaken-subst-trivial s' t') (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ t' / "dummy" ]tm ≡ᶠ op t' (s' [ π ]tm [ t' / "dummy" ]tm)
  Ag.subst (λ x → Ξ ⊢ ((op t s) [ π ]tm [ t' / "dummy" ]tm) ≡ᶠ x) (op-nat t' (var "dummy") (s' [ π ]tm)) (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ t' / "dummy" ]tm ≡ᶠ (op (var "dummy") (s' [ π ]tm)) [ t' / "dummy" ]tm
  subst (((op t s) [ π ]tm) ≡ᶠ op (var "dummy") (s' [ π ]tm)) et (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ t / "dummy" ]tm ≡ᶠ (op (var "dummy") (s' [ π ]tm)) [ t / "dummy" ]tm
  Ag.subst (λ x → Ξ ⊢ x ≡ᶠ ((op (var "dummy") (s' [ π ]tm)) [ t / "dummy" ]tm)) (Ag.sym (tm-weaken-subst-trivial (op t s) t)) (
  -- goal : Ξ ⊢ op t s ≡ᶠ (op (var "dummy") (s' [ π ]tm)) [ t / "dummy" ]tm
  Ag.subst (λ x → Ξ ⊢ op t s ≡ᶠ x) (Ag.sym (op-nat t (var "dummy") (s' [ π ]tm))) (
  -- goal : Ξ ⊢ op t s ≡ᶠ op t (s' [ π ]tm [ t / "dummy" ]tm)
  Ag.subst (λ x → Ξ ⊢ op t s ≡ᶠ op t x) (Ag.sym (tm-weaken-subst-trivial s' t)) (
  -- goal : Ξ ⊢ op t s ≡ᶠ op t s'
  Ag.subst (λ x → Ξ ⊢ x ≡ᶠ op t s') (tm-weaken-subst-trivial (op t s) s') (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ s' / "dummy" ]tm ≡ᶠ op t s'
  Ag.subst (λ x → Ξ ⊢ ((op t s) [ π ]tm [ s' / "dummy" ]tm) ≡ᶠ op x s') (tm-weaken-subst-trivial t s') (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ s' / "dummy" ]tm ≡ᶠ op (t [ π ]tm [ s' / "dummy" ]tm) s'
  Ag.subst (λ x → Ξ ⊢ ((op t s) [ π ]tm [ s' / "dummy" ]tm) ≡ᶠ x) (op-nat s' (t [ π ]tm) (var "dummy")) (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ s' / "dummy" ]tm ≡ᶠ (op (t [ π ]tm) (var "dummy")) [ s' / "dummy" ]tm
  subst (((op t s) [ π ]tm) ≡ᶠ op (t [ π ]tm) (var "dummy")) es (
  -- goal : Ξ ⊢ (op t s) [ π ]tm [ s / "dummy" ]tm ≡ᶠ (op (t [ π ]tm) (var "dummy")) [ s / "dummy" ]tm
  Ag.subst (λ x → Ξ ⊢ x ≡ᶠ ((op (t [ π ]tm) (var' "dummy")) [ s / "dummy" ]tm)) (Ag.sym (tm-weaken-subst-trivial (op t s) s)) (
  -- goal : Ξ ⊢ op t s ≡ᶠ (op (t [ π ]tm) (var "dummy")) [ s / "dummy" ]tm
  Ag.subst (λ x → Ξ ⊢ op t s ≡ᶠ x) (Ag.sym (op-nat s (t [ π ]tm) (var' "dummy"))) (
  -- goal : Ξ ⊢ op t s ≡ᶠ op (t [ π ]tm [ s / "dummy" ]tm) s
  Ag.subst (λ x → Ξ ⊢ op t s ≡ᶠ op x s) (Ag.sym (tm-weaken-subst-trivial t s)) (
  -- goal : Ξ ⊢ op t s ≡ᶠ op t s
  refl))))))))))))))

TmConstructor₃ : (R S T U : TyExpr) → Set
TmConstructor₃ R S T U = ∀ {Γ} → TmExpr Γ R → TmExpr Γ S → TmExpr Γ T → TmExpr Γ U

TmConstructorNatural₃ : TmConstructor₃ R S T U → Set
TmConstructorNatural₃ {R} {S} {T} op =
  ∀ {Γ V x} → (v : TmExpr Γ V) (r : TmExpr (Γ ,, x ∈ V) R) (s : TmExpr (Γ ,, x ∈ V) S) (t : TmExpr (Γ ,, x ∈ V) T) →
  (op r s t) [ v / x ]tm Ag.≡ op (r [ v / x ]tm) (s [ v / x ]tm) (t [ v / x ]tm)

tm-constructor-cong₃ : (op : TmConstructor₃ R S T U) → TmConstructorNatural₃ op →
                       {r r' : TmExpr (to-ctx Ξ) R} {s s' : TmExpr (to-ctx Ξ) S} {t t' : TmExpr (to-ctx Ξ) T} →
                       (Ξ ⊢ r ≡ᶠ r') →
                       (Ξ ⊢ s ≡ᶠ s') →
                       (Ξ ⊢ t ≡ᶠ t') →
                       (Ξ ⊢ op r s t ≡ᶠ op r' s' t')
tm-constructor-cong₃ {Ξ = Ξ} op op-nat {r} {r'} {s} {s'} {t} {t'} er es et =
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r' s' t'
  Ag.subst (λ x → Ξ ⊢ x ≡ᶠ op r' s' t') (tm-weaken-subst-trivial (op r s t) r') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ r' / "dummy" ]tm ≡ᶠ op r' s' t'
  Ag.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ r' / "dummy" ]tm) ≡ᶠ op r' x t') (tm-weaken-subst-trivial s' r') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ r' / "dummy" ]tm ≡ᶠ op r' (s' [ π ]tm [ r' / "dummy" ]tm) t'
  Ag.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ r' / "dummy" ]tm) ≡ᶠ op r' (s' [ π ]tm [ r' / "dummy" ]tm) x) (tm-weaken-subst-trivial t' r') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ r' / "dummy" ]tm ≡ᶠ op r' (s' [ π ]tm [ r' / "dummy" ]tm) (t' [ π ]tm [ r' / "dummy" ]tm)
  Ag.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ r' / "dummy" ]tm) ≡ᶠ x) (op-nat r' (var "dummy") (s' [ π ]tm) (t' [ π ]tm)) (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ r' / "dummy" ]tm ≡ᶠ (op (var "dummy") (s' [ π ]tm) (t' [ π ]tm)) [ r' / "dummy" ]tm
  subst (((op r s t) [ π ]tm) ≡ᶠ op (var "dummy") (s' [ π ]tm) (t' [ π ]tm)) er (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ r / "dummy" ]tm ≡ᶠ (op (var "dummy") (s' [ π ]tm) (t' [ π ]tm)) [ r / "dummy" ]tm
  Ag.subst (λ x → Ξ ⊢ x ≡ᶠ ((op (var "dummy") (s' [ π ]tm) (t' [ π ]tm)) [ r / "dummy" ]tm)) (Ag.sym (tm-weaken-subst-trivial (op r s t) r)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ (op (var "dummy") (s' [ π ]tm) (t' [ π ]tm)) [ r / "dummy" ]tm
  Ag.subst (λ x → Ξ ⊢ op r s t ≡ᶠ x) (Ag.sym (op-nat r (var "dummy") (s' [ π ]tm) (t' [ π ]tm))) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r (s' [ π ]tm [ r / "dummy" ]tm) (t' [ π ]tm [ r / "dummy" ]tm)
  Ag.subst (λ x → Ξ ⊢ op r s t ≡ᶠ op r x (t' [ π ]tm [ r / "dummy" ]tm)) (Ag.sym (tm-weaken-subst-trivial s' r)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r s' (t' [ π ]tm [ r / "dummy" ]tm)
  Ag.subst (λ x → Ξ ⊢ op r s t ≡ᶠ op r s' x) (Ag.sym (tm-weaken-subst-trivial t' r)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r s' t'
  Ag.subst (λ x → Ξ ⊢ x ≡ᶠ op r s' t') (tm-weaken-subst-trivial (op r s t) s') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ s' / "dummy" ]tm ≡ᶠ op r s' t'
  Ag.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ s' / "dummy" ]tm) ≡ᶠ op x s' t') (tm-weaken-subst-trivial r s') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ s' / "dummy" ]tm ≡ᶠ op (r [ π ]tm [ s' / "dummy" ]tm) s' t'
  Ag.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ s' / "dummy" ]tm) ≡ᶠ op (r [ π ]tm [ s' / "dummy" ]tm) s' x) (tm-weaken-subst-trivial t' s') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ s' / "dummy" ]tm ≡ᶠ op (r [ π ]tm [ s' / "dummy" ]tm) s' (t' [ π ]tm [ s' / "dummy" ]tm)
  Ag.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ s' / "dummy" ]tm) ≡ᶠ x) (op-nat s' (r [ π ]tm) (var "dummy") (t' [ π ]tm)) (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ s' / "dummy" ]tm ≡ᶠ (op (r [ π ]tm) (var "dummy") (t' [ π ]tm)) [ s' / "dummy" ]tm
  subst (((op r s t) [ π ]tm) ≡ᶠ op (r [ π ]tm) (var "dummy") (t' [ π ]tm)) es (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ s / "dummy" ]tm ≡ᶠ (op (r [ π ]tm) (var "dummy") (t' [ π ]tm)) [ s / "dummy" ]tm
  Ag.subst (λ x → Ξ ⊢ x ≡ᶠ ((op (r [ π ]tm) (var "dummy") (t' [ π ]tm)) [ s / "dummy" ]tm)) (Ag.sym (tm-weaken-subst-trivial (op r s t) s)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ (op (r [ π ]tm) (var "dummy") (t' [ π ]tm)) [ s / "dummy" ]tm
  Ag.subst (λ x → Ξ ⊢ op r s t ≡ᶠ x) (Ag.sym (op-nat s (r [ π ]tm) (var "dummy") (t' [ π ]tm))) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op (r [ π ]tm [ s / "dummy" ]tm) s (t' [ π ]tm [ s / "dummy" ]tm)
  Ag.subst (λ x → Ξ ⊢ op r s t ≡ᶠ op x s (t' [ π ]tm [ s / "dummy" ]tm)) (Ag.sym (tm-weaken-subst-trivial r s)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r s (t' [ π ]tm [ s / "dummy" ]tm)
  Ag.subst (λ x → Ξ ⊢ op r s t ≡ᶠ op r s x) (Ag.sym (tm-weaken-subst-trivial t' s)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r s t'
  Ag.subst (λ x → Ξ ⊢ x ≡ᶠ op r s t') (tm-weaken-subst-trivial (op r s t) t') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ t' / "dummy" ]tm ≡ᶠ op r s t'
  Ag.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ t' / "dummy" ]tm) ≡ᶠ op x s t') (tm-weaken-subst-trivial r t') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ t' / "dummy" ]tm ≡ᶠ op (r [ π ]tm [ t' / "dummy" ]tm) s t'
  Ag.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ t' / "dummy" ]tm) ≡ᶠ op (r [ π ]tm [ t' / "dummy" ]tm) x t') (tm-weaken-subst-trivial s t') (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ t' / "dummy" ]tm ≡ᶠ op (r [ π ]tm [ t' / "dummy" ]tm) (s [ π ]tm [ t' / "dummy" ]tm) t' 
  Ag.subst (λ x → Ξ ⊢ ((op r s t) [ π ]tm [ t' / "dummy" ]tm) ≡ᶠ x) (op-nat t' (r [ π ]tm) (s [ π ]tm) (var "dummy")) (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ t' / "dummy" ]tm ≡ᶠ (op (r [ π ]tm) (s [ π ]tm) (var "dummy")) [ t' / "dummy" ]tm
  subst (((op r s t) [ π ]tm) ≡ᶠ op (r [ π ]tm) (s [ π ]tm) (var "dummy")) et (
  -- goal : Ξ ⊢ (op r s t) [ π ]tm [ t / "dummy" ]tm ≡ᶠ (op (r [ π ]tm) (s [ π ]tm) (var "dummy")) [ t / "dummy" ]tm
  Ag.subst (λ x → Ξ ⊢ x ≡ᶠ ((op (r [ π ]tm) (s [ π ]tm) (var "dummy")) [ t / "dummy" ]tm)) (Ag.sym (tm-weaken-subst-trivial (op r s t) t)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ (op (r [ π ]tm) (s [ π ]tm) (var "dummy")) [ t / "dummy" ]tm
  Ag.subst (λ x → Ξ ⊢ op r s t ≡ᶠ x) (Ag.sym (op-nat t (r [ π ]tm) (s [ π ]tm) (var "dummy"))) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op (r [ π ]tm [ t / "dummy" ]tm) (s [ π ]tm [ t / "dummy" ]tm) t
  Ag.subst (λ x → Ξ ⊢ op r s t ≡ᶠ op x (s [ π ]tm [ t / "dummy" ]tm) t) (Ag.sym (tm-weaken-subst-trivial r t)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r (s [ π ]tm [ s / "dummy" ]tm) t
  Ag.subst (λ x → Ξ ⊢ op r s t ≡ᶠ op r x t) (Ag.sym (tm-weaken-subst-trivial s t)) (
  -- goal : Ξ ⊢ op r s t ≡ᶠ op r s t'
  refl)))))))))))))))))))))))))))

fst-cong : {p p' : TmExpr (to-ctx Ξ) (T ⊠ S)} →
           (Ξ ⊢ p ≡ᶠ p') →
           (Ξ ⊢ fst p ≡ᶠ fst p')
fst-cong = tm-constructor-cong₁ fst (λ _ _ → Ag.refl)

snd-cong : {p p' : TmExpr (to-ctx Ξ) (T ⊠ S)} →
           (Ξ ⊢ p ≡ᶠ p') →
           (Ξ ⊢ snd p ≡ᶠ snd p')
snd-cong = tm-constructor-cong₁ snd (λ _ _ → Ag.refl)

simultaneous-fun-cong : {f f' : TmExpr (to-ctx Ξ) (T ⇛ S)} {t t' : TmExpr (to-ctx Ξ) T} →
                        (Ξ ⊢ f ≡ᶠ f') →
                        (Ξ ⊢ t ≡ᶠ t') →
                        (Ξ ⊢ f ∙ t ≡ᶠ f' ∙ t')
simultaneous-fun-cong = tm-constructor-cong₂ _∙_ (λ _ _ _ → Ag.refl)

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
pair-cong = tm-constructor-cong₂ pair (λ _ _ _ → Ag.refl)

if-cong : {b b' : TmExpr (to-ctx Ξ) Bool'} {t t' f f' : TmExpr (to-ctx Ξ) T} →
          (Ξ ⊢ b ≡ᶠ b') →
          (Ξ ⊢ t ≡ᶠ t') →
          (Ξ ⊢ f ≡ᶠ f') →
          (Ξ ⊢ if b t f ≡ᶠ if b' t' f')
if-cong = tm-constructor-cong₃ if (λ _ _ _ _ → Ag.refl)


--------------------------------------------------
-- Soundness proof of the logical framework w.r.t. a trivial presheaf model

⟦_⟧pctx : ProofCtx → Ctx ★
to-ctx-subst : (Ξ : ProofCtx) → ⟦ Ξ ⟧pctx M.⇒ ⟦ to-ctx Ξ ⟧ctx

⟦ [] ⟧pctx = M.◇
⟦ Ξ ∷ᵛ _ ∈ T ⟧pctx = ⟦ Ξ ⟧pctx M.,,ₛ ⟦ T ⟧ty
⟦ Ξ ∷ᶠ _ ∈ φ ⟧pctx = ⟦ Ξ ⟧pctx M.,, (⟦ φ ⟧frm M.[ to-ctx-subst Ξ ])

to-ctx-subst [] = M.id-subst M.◇
to-ctx-subst (Ξ ∷ᵛ _ ∈ T) = to-ctx-subst Ξ M.s⊹
to-ctx-subst (Ξ ∷ᶠ _ ∈ φ) = to-ctx-subst Ξ M.⊚ M.π

interpret-assumption : (a : Assumption x Ξ) → Tm ⟦ Ξ ⟧pctx (⟦ lookup-assumption a ⟧frm M.[ to-ctx-subst Ξ ])
interpret-assumption azero = M.ι⁻¹[ M.ty-subst-comp _ _ _ ] M.ξ
interpret-assumption (asuc a) = M.ι⁻¹[ M.ty-subst-comp _ _ _ ] (interpret-assumption a M.[ M.π ]')
interpret-assumption (skip-var {Ξ = Ξ} {T = T} a) =
  M.ι⁻¹[ M.≅ᵗʸ-trans (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ lookup-assumption a ⟧frm subst-eq-proof)
                     (M.ty-subst-cong-ty _ (frm-subst-sound (lookup-assumption a) π))
       ]
  (interpret-assumption a M.[ M.π ]')
  where
    subst-eq-proof : _ M.≅ˢ _
    subst-eq-proof = M.≅ˢ-trans (M.≅ˢ-sym (M.,ₛ-β1 _ M.sξ)) (M.⊚-congʳ (M.≅ˢ-sym (M.⊚-id-substˡ _)))

⟦_⟧der : (Ξ ⊢ φ) → Tm ⟦ Ξ ⟧pctx (⟦ φ ⟧frm M.[ to-ctx-subst Ξ ])
⟦ withAlpha {Ξ = Ξ} {{ φ≈ψ }} d ⟧der = Ag.subst (λ x → Tm ⟦ Ξ ⟧pctx (⟦ x ⟧frm-nmls M.[ _ ])) φ≈ψ ⟦ d ⟧der
⟦ refl {Ξ = Ξ} {{t≈s}} ⟧der = Ag.subst (λ x → Tm ⟦ Ξ ⟧pctx ((M.Id _ ⟦ x ⟧tm-nmls) M.[ _ ])) t≈s (M.refl' _ M.[ _ ]')
⟦ sym d ⟧der = M.ι[ M.Id-natural _ ] M.sym' (M.ι⁻¹[ M.Id-natural _ ] ⟦ d ⟧der)
⟦ trans d1 d2 ⟧der = M.ι[ M.Id-natural _ ] M.trans' (M.ι⁻¹[ M.Id-natural _ ] ⟦ d1 ⟧der) (M.ι⁻¹[ M.Id-natural _ ] ⟦ d2 ⟧der)
⟦ subst {Ξ = Ξ} {x = x} φ {t1 = t1} {t2 = t2} e d ⟧der =
  M.ι[ M.≅ᵗʸ-trans (M.ty-subst-cong-ty _ (M.≅ᵗʸ-sym (frm-subst-sound φ (t2 / x))))
                   (ty-subst-seq-cong (_ ∷ˢ _ ◼) ((to-ctx-subst Ξ M.,ₛ (⟦ t2 ⟧tm M.[ to-ctx-subst Ξ ]s)) ◼) ⟦ φ ⟧frm
                                      (M.≅ˢ-trans (M.,ₛ-⊚ _ _ _) (M.,ₛ-cong1 (M.⊚-id-substˡ _) _)))
     ]
  M.ssubst' ⟦ φ ⟧frm (to-ctx-subst Ξ) ⟦ e ⟧der (
  M.ι⁻¹[ M.≅ᵗʸ-trans (M.ty-subst-cong-ty _ (M.≅ᵗʸ-sym (frm-subst-sound φ (t1 / x))))
                     (ty-subst-seq-cong (_ ∷ˢ _ ◼) ((to-ctx-subst Ξ M.,ₛ (⟦ t1 ⟧tm M.[ to-ctx-subst Ξ ]s)) ◼) ⟦ φ ⟧frm
                                        (M.≅ˢ-trans (M.,ₛ-⊚ _ _ _) (M.,ₛ-cong1 (M.⊚-id-substˡ _) _)))
     ]
  ⟦ d ⟧der)
⟦ assume[ _ ] d ⟧der = M.ι[ M.⇛-natural _ ] M.lam _ (M.ι[ M.ty-subst-comp _ _ _ ] ⟦ d ⟧der)
⟦ assumption' _ {a} ⟧der = interpret-assumption a
⟦ ∧-intro d1 d2 ⟧der = M.ι[ M.⊠-natural _ ] M.prim-pair ⟦ d1 ⟧der ⟦ d2 ⟧der
⟦ ∧-elimˡ d ⟧der = M.prim-fst (M.ι⁻¹[ M.⊠-natural _ ] ⟦ d ⟧der)
⟦ ∧-elimʳ d ⟧der = M.prim-snd (M.ι⁻¹[ M.⊠-natural _ ] ⟦ d ⟧der)
⟦ ∀-intro d ⟧der = M.ι[ M.sPi-natural _ ] (M.sdλ[ _ ] ⟦ d ⟧der)
⟦ ∀-elim {Ξ = Ξ} {x = x} {φ = φ} d t ⟧der =
  M.ι[ M.≅ᵗʸ-trans (M.≅ᵗʸ-sym (M.ty-subst-cong-ty _ (frm-subst-sound φ (t / x))))
                   (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm (subst-lemma (to-ctx Ξ) (to-ctx-subst Ξ) ⟦ t ⟧tm))
     ]
  (M.sdapp (M.ι⁻¹[ M.sPi-natural _ ] ⟦ d ⟧der) (⟦ t ⟧tm M.[ to-ctx-subst Ξ ]s))
⟦ fun-β {b = b} {t = t} ⟧der = (M.≅ᵗᵐ-to-Id (M.≅ᵗᵐ-trans (M.sfun-β _ _) (tm-subst-sound b (id-subst _ ∷ t / _)))) M.[ _ ]'
⟦ nat-elim-β-zero ⟧der = (M.≅ᵗᵐ-to-Id (M.snat-β-zero _ _)) M.[ _ ]'
⟦ nat-elim-β-suc ⟧der = (M.≅ᵗᵐ-to-Id (M.snat-β-suc _ _ _)) M.[ _ ]'
⟦ if-β-true ⟧der = (M.≅ᵗᵐ-to-Id (M.sif-β-true _ _)) M.[ _ ]'
⟦ if-β-false ⟧der = (M.≅ᵗᵐ-to-Id (M.sif-β-false _ _)) M.[ _ ]'
⟦ pair-β-fst ⟧der = (M.≅ᵗᵐ-to-Id (M.sprod-β-fst _ _)) M.[ _ ]'
⟦ pair-β-snd ⟧der = (M.≅ᵗᵐ-to-Id (M.sprod-β-snd _ _)) M.[ _ ]'
⟦ bool-induction {Ξ = Ξ} {x = x} {φ = φ} d1 d2 ⟧der =
  M.sbool-induction _ (M.ι[ M.≅ᵗʸ-trans (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm
                                                           (M.≅ˢ-trans (M.⊚-congˡ (M.,ₛ-cong2 _ (M.≅ᵗᵐ-sym (M.sdiscr-natural _))))
                                                                       (M.≅ˢ-sym (subst-lemma (to-ctx Ξ) (to-ctx-subst Ξ) M.strue))))
                                        (M.ty-subst-cong-ty _ (frm-subst-sound φ (true / x)))
                          ] ⟦ d1 ⟧der)
                      (M.ι[ M.≅ᵗʸ-trans (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm
                                                           (M.≅ˢ-trans (M.⊚-congˡ (M.,ₛ-cong2 _ (M.≅ᵗᵐ-sym (M.sdiscr-natural _))))
                                                                       (M.≅ˢ-sym (subst-lemma (to-ctx Ξ) (to-ctx-subst Ξ) M.sfalse))))
                                        (M.ty-subst-cong-ty _ (frm-subst-sound φ (false / x)))
                          ] ⟦ d2 ⟧der)
⟦ nat-induction {Ξ = Ξ} {x = n} {φ = φ} x d1 d2 ⟧der =
  M.snat-induction _ (M.ι[ M.≅ᵗʸ-trans (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm
                                                           (M.≅ˢ-trans (M.⊚-congˡ (M.,ₛ-cong2 _ (M.≅ᵗᵐ-sym (M.sdiscr-natural _))))
                                                                       (M.≅ˢ-sym (subst-lemma (to-ctx Ξ) (to-ctx-subst Ξ) M.szero))))
                                       (M.ty-subst-cong-ty _ (frm-subst-sound φ (zero / n)))
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
