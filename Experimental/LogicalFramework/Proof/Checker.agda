module Experimental.LogicalFramework.Proof.Checker where

open import Data.String as Str hiding (_≟_)
open import Data.Unit
open import Function using (id)
open import Relation.Binary.PropositionalEquality as Ag using (refl)
open import Relation.Nullary

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
  Ξ : ProofCtx m



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

data EndsInVar : ProofCtx m → Set where
  ends-in-var : (Ξ : ProofCtx m) (μ : Modality n m) (x : String) (T : Ty n) → EndsInVar (Ξ ,,ᵛ μ ∣ x ∈ T)

ends-in-var? : (Ξ : ProofCtx m) → PCM (EndsInVar Ξ)
ends-in-var? (Ξ ,,ᵛ μ ∣ x ∈ T) = return (ends-in-var Ξ μ x T)
ends-in-var? _ = throw-error "Expected variable at head of proof context."


-- In the same way as variables in MSTT, assumptions are internally
--  referred to using De Bruijn indices, but we keep track of their
--  names. The (proof-relevant) predicate Assumption x μ κ Ξ expresses
--  that an assumption with name x is present in proof context Ξ under
--  modality μ and with κ the composition of all locks to the right of
--  x. Note that we do not keep track of the formula in the Assumption
--  type (in contrast to the type of variables in MSTT).
data Assumption (x : String) (μ : Modality n o) : Modality m o → ProofCtx m → Set where
  azero : Assumption x μ 𝟙 (Ξ ,,ᶠ μ ∣ x ∈ φ)
  asuc  : Assumption x μ κ Ξ → Assumption x μ κ (Ξ ,,ᶠ ρ ∣ y ∈ ψ)
  skip-var : Assumption x μ κ Ξ → Assumption x μ κ (Ξ ,,ᵛ ρ ∣ y ∈ T)
  skip-lock : (ρ : Modality m p) → Assumption x μ κ Ξ → Assumption x μ (κ ⓜ ρ) (Ξ ,lock⟨ ρ ⟩)

lookup-assumption' : Assumption x μ κ Ξ → (ρ : Modality _ _) →
                     TwoCell μ (κ ⓜ ρ) → Formula ((to-ctx Ξ) ,lock⟨ ρ ⟩)
lookup-assumption' (azero {φ = φ}) ρ α = φ [ key-sub (◇ ,lock⟨ ρ ⟩) (◇ ,lock⟨ _ ⟩) (Ag.subst (λ - → TwoCell - _) (Ag.sym mod-unitˡ) α) ]frm
lookup-assumption' (asuc a) ρ α = lookup-assumption' a ρ α
lookup-assumption' (skip-var a) ρ α = (lookup-assumption' a ρ α) [ π ,slock⟨ ρ ⟩ ]frm
lookup-assumption' (skip-lock {κ = κ} ρ' a) ρ α = unfuselocks-frm (lookup-assumption' a (ρ' ⓜ ρ) (Ag.subst (TwoCell _) (mod-assoc {μ = κ}) α))

lookup-assumption : Assumption x μ κ Ξ → TwoCell μ κ → Formula (to-ctx Ξ)
lookup-assumption a α = unlock𝟙-frm (lookup-assumption' a 𝟙 (Ag.subst (TwoCell _) (Ag.sym mod-unitʳ) α))

record ContainsAssumption (x : String) (μ : Modality n o) (Ξ : ProofCtx m) : Set where
  constructor contains-assumption
  field
    locks : Modality m o
    as : Assumption x μ locks Ξ

map-contains : {m m' : Mode} {x : String} {μ : Modality n o}
               {Ξ : ProofCtx m} {Ξ' : ProofCtx m'}
               (F : Modality m o → Modality m' o) →
               (∀ {κ} → Assumption x μ κ Ξ → Assumption x μ (F κ) Ξ') →
               ContainsAssumption x μ Ξ → ContainsAssumption x μ Ξ'
map-contains F G (contains-assumption locks as) = contains-assumption (F locks) (G as)

contains-assumption? : (x : String) (μ : Modality n o) (Ξ : ProofCtx m) →
                       PCM (ContainsAssumption x μ Ξ)
contains-assumption? x μ [] = throw-error "Assumption not found in context."
contains-assumption? x μ (Ξ ,,ᵛ ρ ∣ y ∈ T) = map-contains id skip-var <$> contains-assumption? x μ Ξ
contains-assumption? x μ (Ξ ,,ᶠ ρ ∣ y ∈ φ) with x Str.≟ y
contains-assumption? {n = n} {o} {m} x μ (_,,ᶠ_∣_∈_ {n = n'} Ξ ρ .x φ) | yes refl = do
  refl ← m =m? o
  refl ← n =m? n'
  refl ← μ =mod? ρ
  return (contains-assumption 𝟙 azero)
contains-assumption? x μ (Ξ ,,ᶠ ρ ∣ y ∈ φ) | no ¬x=y = map-contains id asuc <$> contains-assumption? x μ Ξ
contains-assumption? x μ (Ξ ,lock⟨ ρ ⟩) = map-contains (_ⓜ ρ) (skip-lock ρ) <$> contains-assumption? x μ Ξ


check-proof : (Ξ : ProofCtx m) → Proof (to-ctx Ξ) → Formula (to-ctx Ξ) → PCM ⊤
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
check-proof Ξ (assumption' x {μ = μ} {κ = κ} α) φ = do
  contains-assumption κ' a ← contains-assumption? x μ Ξ
  refl ← κ' =mod? κ
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
check-proof Ξ (nat-induction' hyp Δ=Γ,μ∣x∈T p0 ps) φ = do
  ends-in-var Ξ' μ x T ← ends-in-var? Ξ
  refl ← return Δ=Γ,μ∣x∈T -- Pattern matching on this proof only works since we already established that Ξ is of the form Ξ' ,,ᵛ μ ∣ x ∈ T.
                          -- Otherwise, unification would fail.
  check-proof Ξ' p0 (φ [ zero / x ]frm) <|,|>
    check-proof (Ξ' ,,ᵛ μ ∣ x ∈ Nat' ,,ᶠ 𝟙 ∣ hyp ∈ lock𝟙-frm φ)
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
