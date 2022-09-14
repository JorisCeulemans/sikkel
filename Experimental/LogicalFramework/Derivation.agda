--------------------------------------------------
-- Definition of proof judgment, inference rules and proof of their soundness
--------------------------------------------------

module Experimental.LogicalFramework.Derivation where

open import Data.Empty
open import Data.Nat
open import Data.String as Str
import Relation.Binary.PropositionalEquality as Ag
-- We publicly export refl from Agda's propositional equality, because
-- we want it to be in scope so that the inference rules refl and
-- withAlpha can use it as instance argument when writing proofs.
open Ag public using (refl)
open import Relation.Nullary as Ag using (Dec; yes; no)
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
import Experimental.ClosedTypes.Discrete as M

open import Experimental.LogicalFramework.STT
open import Experimental.LogicalFramework.Formula
open import Experimental.LogicalFramework.Formula.Interpretation.Nameless using (⟦_⟧frm-nmls)
open import Experimental.LogicalFramework.STT.Interpretation.Nameless using (⟦_⟧tm-nmls)

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


-- In the same way as variables in STT, assumptions are internally
--  referred to using De Bruijn indices, but we keep track of their
--  names. The (proof-relevant) predicate Assumption x Ξ expresses
--  that an assumption with name x is present in proof context Ξ.
data Assumption : String → ProofCtx → Set where
  azero : Assumption x (Ξ ∷ᶠ x ∈ φ)
  asuc  : Assumption x Ξ → Assumption x (Ξ ∷ᶠ y ∈ ψ)
  skip-var : Assumption x Ξ → Assumption x (Ξ ∷ᵛ y ∈ T)

assump-vpred : Assumption x (Ξ ∷ᵛ y ∈ T) → Assumption x Ξ
assump-vpred (skip-var a) = a

assump-apred : Ag.¬ (x Ag.≡ y) → Assumption x (Ξ ∷ᶠ y ∈ φ) → Assumption x Ξ
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
  -- Making sure that derivability respects alpha equivalence. This is
  --  not ideal, we would like to bake this into assumption' below.
  --  However see comment on withTmAlpha below for problems with that.
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

  -- Introduction and elimination for logical combinators ⊤ᶠ, ⊥ᶠ, ⊃, ∧ and ∀.
  ⊤ᶠ-intro : Ξ ⊢ ⊤ᶠ
  ⊥ᶠ-elim : Ξ ⊢ ⊥ᶠ ⊃ φ
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

  -- Axioms specifying distinctness of booleans and natural numbers.
  true≠false : Ξ ⊢ ¬ (true ≡ᶠ false)
  suc-inj : Ξ ⊢ ∀[ "m" ∈ Nat' ] ∀[ "n" ∈ Nat' ] (suc ∙ (var "m") ≡ᶠ suc ∙ (var "n")) ⊃ (var "m" ≡ᶠ var "n")
  zero≠sucn : Ξ ⊢ ∀[ "n" ∈ Nat' ] ¬ (zero ≡ᶠ suc ∙ var "n")

  -- Induction schemata for Bool' and Nat'.
  bool-induction : (Ξ ⊢ φ [ true / x ]frm) →
                   (Ξ ⊢ φ [ false / x ]frm) →
                   (Ξ ∷ᵛ x ∈ Bool' ⊢ φ)
  nat-induction : (hyp : String) →
                  (Ξ ⊢ φ [ zero / x ]frm) →
                  (Ξ ∷ᵛ x ∈ Nat' ∷ᶠ hyp ∈ φ ⊢ φ [ π ∷ (suc ∙ var' x {vzero}) / x ]frm) →
                  (Ξ ∷ᵛ x ∈ Nat' ⊢ φ)

assumption : (x : String) {a : True (assumption? x Ξ)} → (Ξ ⊢ lookup-assumption (toWitness a))
assumption x {a} = assumption' x {toWitness a}


--------------------------------------------------
-- Some rules derivable from the basic ones

-- Not all of the above inference rules respect α-equivalence. Since
--  refl does respect α-equivalence, the following can be used for the
--  other rules. This situation is not ideal: the user does not want
--  to explicitly mention withAlpha. However, changing the types of
--  the inference rules that do not respect α equivalence so that they
--  look like the type of refl, does lead to the problem that Agda
--  cannot infer the intermediate formulas in a chain of equalities
--  (using trans) any more. We should investigate if reflection might
--  provide a solution.
withTmAlpha : {t s s' : TmExpr (to-ctx Ξ) T} →
              (Ξ ⊢ t ≡ᶠ s) →
              {{ s ≈α s' }} →
              (Ξ ⊢ t ≡ᶠ s')
withTmAlpha t=s = trans t=s refl

TmConstructor₁ : (Γ : CtxExpr) (T S : TyExpr) → Set
TmConstructor₁ Γ T S = ∀ {Δ} → SubstExpr Δ Γ → TmExpr Δ T → TmExpr Δ S

-- The naturality condition could be more strict (requiring the same
--  condition for all substitutions instead of restricting to those of
--  the form r / x), but this condition suffices to show that the
--  corresponding constructor is congruent and this condition will be
--  provable by reflexivity for most term constructors.
TmConstructorNatural₁ : TmConstructor₁ Γ T S → Set
TmConstructorNatural₁ {Γ} {T} op = ∀ {Δ R x σ} (r : TmExpr Δ R) (t : TmExpr (Δ ,, x ∈ R) T) → (op (σ ⊚π) t) [ r / x ]tm Ag.≡ op σ (t [ r / x ]tm)

tm-constructor-cong₁ : (op : TmConstructor₁ (to-ctx Ξ) T S) (op-nat : TmConstructorNatural₁ op) →
                       {t t' : TmExpr (to-ctx Ξ) T} →
                       (Ξ ⊢ t ≡ᶠ t') →
                       (Ξ ⊢ op (id-subst _) t ≡ᶠ op (id-subst _) t')
tm-constructor-cong₁ {Ξ = Ξ} op op-nat {t} {t'} et =
  -- goal : Ξ ⊢ op id t ≡ᶠ op id t'
  Ag.subst (λ x → Ξ ⊢ x ≡ᶠ op (id-subst _) t') (tm-weaken-subst-trivial (op (id-subst _) t) t') (
  -- goal : Ξ ⊢ (op id t) [ π ]tm [ t' / "dummy" ]tm ≡ᶠ op id t'
  Ag.subst (λ x → Ξ ⊢ ((op (id-subst _) t) [ π ]tm [ t' / "dummy" ]tm) ≡ᶠ x) (op-nat t' (var "dummy")) (
  -- goal : Ξ ⊢ (op id t) [ π ]tm [ t' / "dummy" ]tm ≡ᶠ (op (id ⊚π) (var "dummy")) [ t' / "dummy" ]tm
  subst (((op (id-subst _) t) [ π ]tm) ≡ᶠ op (id-subst _ ⊚π) (var "dummy")) et (
  -- goal : Ξ ⊢ (op id t) [ π ]tm [ t / "dummy" ]tm ≡ᶠ (op (id ⊚π) (var "dummy")) [ t / "dummy" ]tm
  Ag.subst (λ x → Ξ ⊢ x ≡ᶠ ((op (id-subst _ ⊚π) (var "dummy")) [ t / "dummy" ]tm)) (Ag.sym (tm-weaken-subst-trivial (op (id-subst _) t) t)) (
  -- goal : Ξ ⊢ op id t ≡ᶠ (op (id ⊚π) (var "dummy")) [ t / "dummy" ]tm
  Ag.subst (λ x → Ξ ⊢ op (id-subst _) t ≡ᶠ x) (Ag.sym (op-nat t (var "dummy")))
  -- goal : Ξ ⊢ op id t ≡ᶠ op id t
  refl))))

TmConstructor₂ : (Γ : CtxExpr) (T S R : TyExpr) → Set
TmConstructor₂ Γ T S R = ∀ {Δ} → SubstExpr Δ Γ → TmExpr Δ T → TmExpr Δ S → TmExpr Δ R

TmConstructorNatural₂ : TmConstructor₂ Γ T S R → Set
TmConstructorNatural₂ {Γ} {T} {S} op =
  ∀ {Δ W x σ} → (w : TmExpr Δ W) (t : TmExpr (Δ ,, x ∈ W) T) (s : TmExpr (Δ ,, x ∈ W) S) →
  (op (σ ⊚π) t s) [ w / x ]tm Ag.≡ op σ (t [ w / x ]tm) (s [ w / x ]tm)

apply-tmc₂ˡ : TmExpr Γ T → TmConstructor₂ Γ T S R → TmConstructor₁ Γ S R
apply-tmc₂ˡ t op = λ σ s → op σ (t [ σ ]tm) s

apply-tmc₂ˡ-natural : (t : TmExpr Γ T) (op : TmConstructor₂ Γ T S R) →
                      TmConstructorNatural₂ op → TmConstructorNatural₁ (apply-tmc₂ˡ t op)
apply-tmc₂ˡ-natural t op op-nat {σ = σ} = λ r s →
  Ag.trans (op-nat r (t [ σ ⊚π ]tm) s) (Ag.cong (λ x → op σ x _) (tm-weaken-subst-trivial (t [ σ ]tm) r))

apply-tmc₂ʳ : TmExpr Γ S → TmConstructor₂ Γ T S R → TmConstructor₁ Γ T R
apply-tmc₂ʳ s op = λ σ t → op σ t (s [ σ ]tm)

apply-tmc₂ʳ-natural : (s : TmExpr Γ S) (op : TmConstructor₂ Γ T S R) →
                      TmConstructorNatural₂ op → TmConstructorNatural₁ (apply-tmc₂ʳ s op)
apply-tmc₂ʳ-natural s op op-nat {σ = σ} = λ r t →
  Ag.trans (op-nat r t (s [ σ ⊚π ]tm)) (Ag.cong (op σ _) (tm-weaken-subst-trivial (s [ σ ]tm) r))

tm-constructor-cong₂ : (op : TmConstructor₂ (to-ctx Ξ) T S R) → TmConstructorNatural₂ op →
                       {t t' : TmExpr (to-ctx Ξ) T} {s s' : TmExpr (to-ctx Ξ) S} →
                       (Ξ ⊢ t ≡ᶠ t') →
                       (Ξ ⊢ s ≡ᶠ s') →
                       (Ξ ⊢ op (id-subst _) t s ≡ᶠ op (id-subst _) t' s')
tm-constructor-cong₂ {Ξ = Ξ} op op-nat {t} {t'} {s} {s'} et es = trans
  (tm-constructor-cong₁ (apply-tmc₂ʳ s op)  (apply-tmc₂ʳ-natural s op op-nat)  et)
  (tm-constructor-cong₁ (apply-tmc₂ˡ t' op) (apply-tmc₂ˡ-natural t' op op-nat) es)

TmConstructor₃ : (Γ : CtxExpr) (R S T U : TyExpr) → Set
TmConstructor₃ Γ R S T U = ∀ {Δ} → SubstExpr Δ Γ → TmExpr Δ R → TmExpr Δ S → TmExpr Δ T → TmExpr Δ U

TmConstructorNatural₃ : TmConstructor₃ Γ R S T U → Set
TmConstructorNatural₃ {Γ} {R} {S} {T} op =
  ∀ {Δ V x σ} → (v : TmExpr Δ V) (r : TmExpr (Δ ,, x ∈ V) R) (s : TmExpr (Δ ,, x ∈ V) S) (t : TmExpr (Δ ,, x ∈ V) T) →
  (op (σ ⊚π) r s t) [ v / x ]tm Ag.≡ op σ (r [ v / x ]tm) (s [ v / x ]tm) (t [ v / x ]tm)

apply-tmc₃ʳ : TmExpr Γ T → TmConstructor₃ Γ R S T U → TmConstructor₂ Γ R S U
apply-tmc₃ʳ t op = λ σ r s → op σ r s (t [ σ ]tm)

apply-tmc₃ʳ-natural : (t : TmExpr Γ T) (op : TmConstructor₃ Γ R S T U) →
                      TmConstructorNatural₃ op → TmConstructorNatural₂ (apply-tmc₃ʳ t op)
apply-tmc₃ʳ-natural t op op-nat {σ = σ} = λ w r s →
  Ag.trans (op-nat w r s (t [ σ ⊚π ]tm)) (Ag.cong (op σ _ _) (tm-weaken-subst-trivial (t [ σ ]tm) w))

apply-tmc₃ˡᶜ : TmExpr Γ R → TmExpr Γ S → TmConstructor₃ Γ R S T U → TmConstructor₁ Γ T U
apply-tmc₃ˡᶜ r s op = λ σ t → op σ (r [ σ ]tm) (s [ σ ]tm) t

apply-tmc₃ˡᶜ-natural : (r : TmExpr Γ R) (s : TmExpr Γ S) (op : TmConstructor₃ Γ R S T U) →
                       TmConstructorNatural₃ op → TmConstructorNatural₁ (apply-tmc₃ˡᶜ r s op)
apply-tmc₃ˡᶜ-natural r s op op-nat {σ = σ} = λ w t →
  Ag.trans (op-nat w (r [ σ ⊚π ]tm) (s [ σ ⊚π ]tm) t)
           (Ag.cong₂ (λ x y → op σ x y _) (tm-weaken-subst-trivial (r [ σ ]tm) w) (tm-weaken-subst-trivial (s [ σ ]tm) w))

tm-constructor-cong₃ : (op : TmConstructor₃ (to-ctx Ξ) R S T U) → TmConstructorNatural₃ op →
                       {r r' : TmExpr (to-ctx Ξ) R} {s s' : TmExpr (to-ctx Ξ) S} {t t' : TmExpr (to-ctx Ξ) T} →
                       (Ξ ⊢ r ≡ᶠ r') →
                       (Ξ ⊢ s ≡ᶠ s') →
                       (Ξ ⊢ t ≡ᶠ t') →
                       (Ξ ⊢ op (id-subst _) r s t ≡ᶠ op (id-subst _) r' s' t')
tm-constructor-cong₃ {Ξ = Ξ} op op-nat {r} {r'} {s} {s'} {t} {t'} er es et = trans
  (tm-constructor-cong₂ (apply-tmc₃ʳ t op) (apply-tmc₃ʳ-natural t op op-nat) er es)
  (tm-constructor-cong₁ (apply-tmc₃ˡᶜ r' s' op) (apply-tmc₃ˡᶜ-natural r' s' op op-nat) et)

fst-cong : {p p' : TmExpr (to-ctx Ξ) (T ⊠ S)} →
           (Ξ ⊢ p ≡ᶠ p') →
           (Ξ ⊢ fst p ≡ᶠ fst p')
fst-cong = tm-constructor-cong₁ (λ _ → fst) (λ _ _ → Ag.refl)

snd-cong : {p p' : TmExpr (to-ctx Ξ) (T ⊠ S)} →
           (Ξ ⊢ p ≡ᶠ p') →
           (Ξ ⊢ snd p ≡ᶠ snd p')
snd-cong = tm-constructor-cong₁ (λ _ → snd) (λ _ _ → Ag.refl)

app-constr : TmConstructor₂ Γ (T ⇛ S) T S
app-constr = λ _ → _∙_

app-constr-natural : ∀ {Γ T S} → TmConstructorNatural₂ (app-constr {Γ} {T} {S})
app-constr-natural = λ _ _ _ → Ag.refl

simultaneous-fun-cong : {f f' : TmExpr (to-ctx Ξ) (T ⇛ S)} {t t' : TmExpr (to-ctx Ξ) T} →
                        (Ξ ⊢ f ≡ᶠ f') →
                        (Ξ ⊢ t ≡ᶠ t') →
                        (Ξ ⊢ f ∙ t ≡ᶠ f' ∙ t')
simultaneous-fun-cong = tm-constructor-cong₂ app-constr (λ _ _ _ → Ag.refl)

cong : (f : TmExpr (to-ctx Ξ) (T ⇛ S)) {t1 t2 : TmExpr (to-ctx Ξ) T} →
       (Ξ ⊢ t1 ≡ᶠ t2) →
       (Ξ ⊢ f ∙ t1 ≡ᶠ f ∙ t2)
cong {Ξ = Ξ} f = tm-constructor-cong₁
  (apply-tmc₂ˡ f app-constr)
  (λ {_}{_}{_}{σ} → apply-tmc₂ˡ-natural f app-constr (λ {_}{_}{_}{τ} → app-constr-natural {σ = τ}) {σ = σ})

fun-cong : {f g : TmExpr (to-ctx Ξ) (T ⇛ S)} →
           (Ξ ⊢ f ≡ᶠ g) →
           (t : TmExpr (to-ctx Ξ) T) →
           (Ξ ⊢ f ∙ t ≡ᶠ g ∙ t)
fun-cong ef t = tm-constructor-cong₁
  (apply-tmc₂ʳ t app-constr)
  (λ {_}{_}{_}{σ} → apply-tmc₂ʳ-natural t app-constr (λ {_}{_}{_}{τ} → app-constr-natural {σ = τ}) {σ = σ})
  ef

pair-cong : {t t' : TmExpr (to-ctx Ξ) T} {s s' : TmExpr (to-ctx Ξ) S} →
            (Ξ ⊢ t ≡ᶠ t') →
            (Ξ ⊢ s ≡ᶠ s') →
            (Ξ ⊢ pair t s ≡ᶠ pair t' s')
pair-cong = tm-constructor-cong₂ (λ _ → pair) (λ _ _ _ → Ag.refl)

if-cong : {b b' : TmExpr (to-ctx Ξ) Bool'} {t t' f f' : TmExpr (to-ctx Ξ) T} →
          (Ξ ⊢ b ≡ᶠ b') →
          (Ξ ⊢ t ≡ᶠ t') →
          (Ξ ⊢ f ≡ᶠ f') →
          (Ξ ⊢ if b t f ≡ᶠ if b' t' f')
if-cong = tm-constructor-cong₃ (λ _ → if) (λ _ _ _ _ → Ag.refl)


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
⟦ ⊤ᶠ-intro ⟧der = M.tt' M.[ _ ]'
⟦ ⊥ᶠ-elim ⟧der = (M.empty-elim _) M.[ _ ]'
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
⟦ true≠false ⟧der = M.strue≠sfalse M.[ _ ]'
⟦ suc-inj ⟧der = M.ssuc-inj M.[ _ ]'
⟦ zero≠sucn ⟧der = M.szero≠ssucn M.[ _ ]'
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
