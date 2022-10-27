module Experimental.LogicalFramework.Proof.Checker where

open import Data.String as Str hiding (_≟_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality as Ag using (refl)

open import Experimental.LogicalFramework.MSTT
open import Experimental.LogicalFramework.Formula
open import Experimental.LogicalFramework.Proof.Definition
open import Experimental.LogicalFramework.Proof.CheckingMonad
open import Experimental.LogicalFramework.Proof.Equality

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  Γ Δ : Ctx m
  T S R U : Ty m
  φ ψ : Formula Γ
  x y : String



data IsEquation : Formula Γ → Set where
  is-eq : (t1 t2 : Tm Γ T) → IsEquation (t1 ≡ᶠ t2)

is-eq? : (φ : Formula Γ) → PCM (IsEquation φ)
is-eq? (t1 ≡ᶠ t2) = return (is-eq t1 t2)
is-eq? φ = throw-error "Formula is not an equation"

data IsForall : Formula Γ → Set where
  is-forall : {Γ : Ctx m} (μ : Modality n m) (x : String) (T : Ty n) (φ : Formula (Γ ,, μ ∣ x ∈ T)) →
              IsForall (∀[ μ ∣ x ∈ T ] φ)

is-forall? : (φ : Formula Γ) → PCM (IsForall φ)
is-forall? (∀[ μ ∣ x ∈ T ] φ) = return (is-forall μ x T φ)
is-forall? φ = throw-error "Formula is not of the form ∀ x ..."

data IsLam : Tm Γ T → Set where
  lam : (x : String) (b : Tm (Γ ,, 𝟙 ∣ x ∈ T) S) → IsLam (lam[ x ∈ T ] b)

is-lam? : (t : Tm Γ T) → PCM (IsLam t)
is-lam? (lam[ x ∈ T ] b) = return (lam x b)
is-lam? _ = throw-error "Lambda expected"

data IsApp : Tm Γ T → Set where
  app : (f : Tm Γ (T ⇛ S)) (t : Tm Γ T) → IsApp (f ∙ t)

is-app? : (t : Tm Γ T) → PCM (IsApp t)
is-app? (f ∙ t) = return (app f t)
is-app? _ = throw-error "Function application expected"

data IsNatElim : Tm Γ T → Set where
  nat-elim : ∀ {A} (z : Tm Γ A) (s : Tm Γ (A ⇛ A)) → IsNatElim (nat-elim z s)

is-nat-elim? : (t : Tm Γ T) → PCM (IsNatElim t)
is-nat-elim? (nat-elim z s) = return (nat-elim z s)
is-nat-elim? _ = throw-error "Natural number recursor expected"

data IsSucTm : Tm Γ T → Set where
  suc-tm : (t : Tm Γ Nat') → IsSucTm (suc ∙ t)

is-suc-tm? : (t : Tm Γ T) → PCM (IsSucTm t)
is-suc-tm? (suc ∙ t) = return (suc-tm t)
is-suc-tm? _ = throw-error "successor of natural number expected"


check-proof : (Ξ : ProofCtx m) → Proof Ξ → Formula (to-ctx Ξ) → PCM ⊤
check-proof Ξ refl φ = do
  is-eq t1 t2 ← is-eq? φ
  t1 =t? t2
  return tt
check-proof Ξ (sym p) φ = do
  is-eq t1 t2 ← is-eq? φ
  check-proof Ξ p (t2 ≡ᶠ t1)
check-proof Ξ (trans {T = T'} middle-tm p1 p2) φ = do
  is-eq {T = T} t s ← is-eq? φ
  refl ← T =T? T'
  check-proof Ξ p1 (t ≡ᶠ middle-tm) <|,|> check-proof Ξ p2 (middle-tm ≡ᶠ s)
  return tt
check-proof Ξ (assumption' x a α) φ = do
  φ =f? lookup-assumption a α
  return tt
check-proof Ξ (∀-intro[_∣_∈_]_ {n = n} μ x T p) φ = do
  is-forall {n = n'} κ y S φ' ← is-forall? φ
  refl ← n =m? n'
  refl ← μ =mod? κ
  refl ← from-dec (x Str.≟ y)
  refl ← T =T? S
  check-proof (Ξ ,,ᵛ μ ∣ x ∈ T) p φ'
check-proof Ξ (∀-elim {n = n} {T = T} μ ψ p t) φ = do
  check-proof Ξ p ψ
  is-forall {n = n'} κ y S ψ' ← is-forall? ψ
  refl ← n =m? n'
  refl ← μ =mod? κ
  refl ← T =T? S
  φ =f? (ψ' [ t / y ]frm)
  return tt
check-proof Ξ fun-β φ = do
  is-eq lhs rhs ← is-eq? φ
  app f t ← is-app? lhs
  lam x b ← is-lam? f
  rhs =t? (b [ lock𝟙-tm t / x ]tm)
  return tt
check-proof Ξ nat-elim-β-zero φ = do
  is-eq lhs rhs ← is-eq? φ
  app f t ← is-app? lhs
  nat-elim z s ← is-nat-elim? f
  t =t? zero
  rhs =t? z
  return tt
check-proof Ξ nat-elim-β-suc φ = do
  is-eq lhs rhs ← is-eq? φ
  app f t ← is-app? lhs
  nat-elim z s ← is-nat-elim? f
  suc-tm t' ← is-suc-tm? t
  rhs =t? s ∙ (nat-elim z s ∙ t')
  return tt
check-proof .(Ξ ,,ᵛ μ ∣ x ∈ Nat') (nat-induction {Ξ = Ξ} {μ = μ} {x = x} hyp ψ p0 ps) φ = do
  check-proof Ξ p0 (φ [ zero / x ]frm) <|,|>
    check-proof (Ξ ,,ᵛ μ ∣ x ∈ Nat' ,,ᶠ 𝟙 ∣ hyp ∈ lock𝟙-frm ψ)
                ps
                (φ [ π ∷ˢ suc ∙ var' x {skip-lock μ vzero} (Ag.subst (TwoCell μ) (Ag.sym mod-unitˡ) id-cell) / x ]frm)
  return tt
check-proof Ξ (fun-cong {T = T} p t) φ = do
  is-eq lhs rhs ← is-eq? φ
  app {T = T2} f s ← is-app? lhs
  app {T = T3} g s' ← is-app? rhs
  refl ← T =T? T2
  refl ← T =T? T3
  s =t? t
  s' =t? t
  check-proof Ξ p (f ≡ᶠ g)
check-proof Ξ (cong {T = T} {S = S} f p) φ = do
  is-eq {T = S'} lhs rhs ← is-eq? φ
  app {T = T2} g t ← is-app? lhs
  app {T = T3} g' s ← is-app? rhs
  refl ← S =T? S'
  refl ← T =T? T2
  refl ← T =T? T3
  g =t? f
  g' =t? f
  check-proof Ξ p (t ≡ᶠ s)
check-proof Ξ (hole id) φ = goal-fail (goal id Ξ φ)
