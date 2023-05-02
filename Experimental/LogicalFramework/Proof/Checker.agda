open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Interpretation.ModeTheory

module Experimental.LogicalFramework.Proof.Checker
  (ℳ : ModeTheory) (⟦ℳ⟧ : ModeTheoryInterpretation ℳ)
  where

open import Data.List
open import Data.String as Str hiding (_≟_; _++_)
open import Data.Product
open import Data.Unit
open import Function using (id)
open import Relation.Binary.PropositionalEquality as Ag using (refl)
open import Relation.Nullary

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
import Model.Modality as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.Function as M
import Model.Type.Constant as M
import Model.Type.Function as M hiding (lam)

open ModeTheory ℳ
open ModeTheoryInterpretation ⟦ℳ⟧

open import Experimental.LogicalFramework.MSTT ℳ ⟦ℳ⟧
open import Experimental.LogicalFramework.bProp ℳ ⟦ℳ⟧
open import Experimental.LogicalFramework.Proof.Definition ℳ
open import Experimental.LogicalFramework.Proof.CheckingMonad
open import Experimental.LogicalFramework.Proof.Equality ℳ
open import Experimental.LogicalFramework.Proof.Context ℳ ⟦ℳ⟧
open import Experimental.LogicalFramework.Postulates ℳ ⟦ℳ⟧

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  Γ Δ : Ctx m
  T S R U : Ty m
  φ ψ : bProp Γ
  x y : String
  Ξ : ProofCtx m



data IsEquation : bProp Γ → Set where
  is-eq : (t1 t2 : Tm Γ T) → IsEquation (t1 ≡ᵇ t2)

is-eq? : (φ : bProp Γ) → PCM (IsEquation φ)
is-eq? (t1 ≡ᵇ t2) = return (is-eq t1 t2)
is-eq? φ = throw-error "bProp is not an equation"

data IsForall : bProp Γ → Set where
  is-forall : {Γ : Ctx m} (μ : Modality n m) (x : String) (T : Ty n) (φ : bProp (Γ ,, μ ∣ x ∈ T)) →
              IsForall (∀[ μ ∣ x ∈ T ] φ)

is-forall? : (φ : bProp Γ) → PCM (IsForall φ)
is-forall? (∀[ μ ∣ x ∈ T ] φ) = return (is-forall μ x T φ)
is-forall? φ = throw-error "bProp is not of the form ∀ x ..."

data IsLam : Tm Γ T → Set where
  lam : (μ : Modality n m) (x : String) (b : Tm (Γ ,, μ ∣ x ∈ T) S) → IsLam (lam[ μ ∣ x ∈ T ] b)

is-lam? : (t : Tm Γ T) → PCM (IsLam t)
is-lam? (lam[ μ ∣ x ∈ T ] b) = return (lam μ x b)
is-lam? _ = throw-error "Lambda expected"

data IsApp : Tm Γ T → Set where
  app : {μ : Modality m n} (f : Tm Γ (⟨ μ ∣ T ⟩⇛ S)) (t : Tm (Γ ,lock⟨ μ ⟩) T) → IsApp (f ∙ t)

is-app? : (t : Tm Γ T) → PCM (IsApp t)
is-app? (f ∙ t) = return (app f t)
is-app? _ = throw-error "Function application expected"

data IsNatElim : Tm Γ T → Set where
  nat-elim : ∀ {A} (z : Tm Γ A) (s : Tm Γ (A ⇛ A)) (n : Tm Γ Nat') → IsNatElim (nat-elim z s n)

is-nat-elim? : (t : Tm Γ T) → PCM (IsNatElim t)
is-nat-elim? (nat-elim z s n) = return (nat-elim z s n)
is-nat-elim? _ = throw-error "Natural number recursor expected"

data IsSucTm : Tm Γ T → Set where
  suc-tm : (n : Tm Γ Nat') → IsSucTm (suc n)

is-suc-tm? : (t : Tm Γ T) → PCM (IsSucTm t)
is-suc-tm? (suc n) = return (suc-tm n)
is-suc-tm? _ = throw-error "successor of natural number expected"

data EndsInVar : ProofCtx m → Set where
  ends-in-var : (Ξ : ProofCtx m) (μ : Modality n m) (x : String) (T : Ty n) → EndsInVar (Ξ ,,ᵛ μ ∣ x ∈ T)

ends-in-var? : (Ξ : ProofCtx m) → PCM (EndsInVar Ξ)
ends-in-var? (Ξ ,,ᵛ μ ∣ x ∈ T) = return (ends-in-var Ξ μ x T)
ends-in-var? _ = throw-error "Expected variable at head of proof context."


-- If a proof is incomplete (i.e. it contains one or more holes), the
-- proof checker should output the remaining goals to solve (i.e. the
-- goal proposition to prove and the proof context at that point).
record Goal : Set where
  constructor goal
  field
    gl-identifier : String
    {gl-mode} : Mode
    gl-ctx    : ProofCtx gl-mode
    gl-prop   : bProp (to-ctx gl-ctx)
open Goal

SemGoals : List Goal → Set
SemGoals [] = ⊤
SemGoals (goal _ Ξ φ ∷ gls) = SemTm ⟦ Ξ ⟧pctx (⟦ φ ⟧bprop M.[ to-ctx-subst Ξ ]) × SemGoals gls

split-sem-goals : (gls1 gls2 : List Goal) → SemGoals (gls1 ++ gls2) → SemGoals gls1 × SemGoals gls2
split-sem-goals []          gls2 sgls         = tt , sgls
split-sem-goals (gl ∷ gls1) gls2 (sgl , sgls) = let (sgls1 , sgls2) = split-sem-goals gls1 gls2 sgls in (sgl , sgls1) , sgls2

record PCResult (Ξ : ProofCtx m) (φ : bProp (to-ctx Ξ)) : Set where
  constructor ⟅_,_⟆
  field
    goals : List Goal
    denotation : SemGoals goals → SemTm ⟦ Ξ ⟧pctx (⟦ φ ⟧bprop M.[ to-ctx-subst Ξ ])

pc-result : (goals : List Goal) →
            (SemGoals goals → SemTm ⟦ Ξ ⟧pctx (⟦ φ ⟧bprop M.[ to-ctx-subst Ξ ])) →
            PCResult Ξ φ
pc-result = ⟅_,_⟆

syntax pc-result goals (λ sgoals → b) = ⟅ goals , sgoals ↦ b ⟆

check-proof : (Ξ : ProofCtx m) → Proof (to-ctx Ξ) → (φ : bProp (to-ctx Ξ)) → PCM (PCResult Ξ φ)
check-proof Ξ refl φ = do
  is-eq t1 t2 ← is-eq? φ
  refl ← t1 =t? t2
  return ⟅ [] , _ ↦ M.refl' _ M.[ _ ]' ⟆
check-proof Ξ (sym p) φ = do
  is-eq t1 t2 ← is-eq? φ
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof Ξ p (t2 ≡ᵇ t1)
  return ⟅ goals , sgoals ↦ M.ι[ M.Id-natural _ ] M.sym' (M.ι⁻¹[ M.Id-natural _ ] ⟦p⟧ sgoals) ⟆
check-proof Ξ (trans {T = T'} middle-tm p1 p2) φ = do
  is-eq {T = T} t s ← is-eq? φ
  refl ← T =T? T'
  ⟅ goals1 , ⟦p1⟧ ⟆ ← check-proof Ξ p1 (t ≡ᵇ middle-tm)
  ⟅ goals2 , ⟦p2⟧ ⟆ ← check-proof Ξ p2 (middle-tm ≡ᵇ s)
  return ⟅ goals1 ++ goals2
         , sgoals ↦ (let sgoals1 , sgoals2 = split-sem-goals goals1 goals2 sgoals
                      in M.ι[ M.Id-natural _ ] M.trans' (M.ι⁻¹[ M.Id-natural _ ] ⟦p1⟧ sgoals1) (M.ι⁻¹[ M.Id-natural _ ] ⟦p2⟧ sgoals2))
         ⟆
check-proof Ξ (assumption' x {μ = μ} {κ = κ} α) φ = do
  contains-assumption κ' a ← contains-assumption? x μ Ξ
  refl ← κ' =mod? κ
  refl ← φ =b? lookup-assumption a α
  return ⟅ [] , _ ↦ ⟦ a , α ⟧assumption ⟆
check-proof Ξ (∀-intro[_∣_∈_]_ {n = n} μ x T p) φ = do
  is-forall {n = n'} κ y S φ' ← is-forall? φ
  refl ← n =m? n'
  refl ← μ =mod? κ
  refl ← from-dec "Alpha equivalence is currently not supported" (x Str.≟ y)
  refl ← T =T? S
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof (Ξ ,,ᵛ μ ∣ x ∈ T) p φ'
  return ⟅ goals , sgoals ↦ M.ι[ M.Pi-natural-closed-dom (ty-closed-natural ⟨ μ ∣ T ⟩) _ ]
                               M.lam ⟦ ⟨ μ ∣ T ⟩ ⟧ty (⟦p⟧ sgoals) ⟆
check-proof Ξ (∀-elim {n = n} {T = T} μ ψ p t) φ = do
  is-forall {n = n'} κ y S ψ' ← is-forall? ψ
  refl ← n =m? n'
  refl ← μ =mod? κ
  refl ← T =T? S
  refl ← φ =b? (ψ' [ t / y ]bprop)
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof Ξ p ψ
  return ⟅ goals , sgoals ↦ M.ι⁻¹[ M.ty-subst-cong-ty _ (M.transᵗʸ (M.ty-subst-cong-subst (M.symˢ (/-sound t y)) ⟦ ψ' ⟧bprop) (bprop-sub-sound ψ' (t / y))) ]
         (M.ι[ M.ty-subst-cong-subst-2-2 _ (M./-⊚ (ty-closed-natural ⟨ μ ∣ T ⟩) _ _) ]
         (M.ι[ M.ty-subst-cong-subst (M.,cl-cong-tm (ty-closed-natural ⟨ μ ∣ T ⟩) (M.mod-intro-cl-natural ⟦ μ ⟧mod (ty-closed-natural T) ⟦ t ⟧tm)) _ ]
         (M.cl-app (ty-closed-natural ⟨ μ ∣ T ⟩) (M.ι⁻¹[ M.Pi-natural-closed-dom (ty-closed-natural ⟨ μ ∣ T ⟩) _ ] (⟦p⟧ sgoals))
                                                 (M.mod-intro ⟦ μ ⟧mod (⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.lock-fmap ⟦ μ ⟧mod (to-ctx-subst Ξ) ]cl))))) ⟆
check-proof Ξ fun-β φ = do
  is-eq lhs rhs ← is-eq? φ
  app f t ← is-app? lhs
  lam {T = A} {S = B} μ x b ← is-lam? f
  refl ← rhs =t? (b [ t / x ]tm)
  return ⟅ [] , _ ↦ M.≅ᵗᵐ-to-Id (
         M.transᵗᵐ (M.⇛-cl-β (ty-closed-natural ⟨ μ ∣ A ⟩) (ty-closed-natural B) _ _) (
         M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural B) (M.symˢ (/-sound t x))) (
         tm-sub-sound b (t / x))))
         M.[ _ ]' ⟆
check-proof Ξ nat-elim-β-zero φ = do
  is-eq lhs rhs ← is-eq? φ
  nat-elim z s n ← is-nat-elim? lhs
  refl ← n =t? zero
  refl ← rhs =t? z
  return ⟅ [] , _ ↦ (M.≅ᵗᵐ-to-Id (M.β-nat-zero _ _)) M.[ _ ]' ⟆
check-proof Ξ nat-elim-β-suc φ = do
  is-eq lhs rhs ← is-eq? φ
  nat-elim z s n ← is-nat-elim? lhs
  suc-tm n' ← is-suc-tm? n
  refl ← rhs =t? s ∙¹ (nat-elim z s n')
  return ⟅ [] , _ ↦ M.≅ᵗᵐ-to-Id (M.transᵗᵐ (M.β-nat-suc _ _ _) (M.symᵗᵐ (∙¹-sound s (nat-elim z s n')))) M.[ _ ]' ⟆
check-proof Ξ (nat-induction' hyp Δ=Γ,μ∣x∈T p0 ps) φ = do
  ends-in-var Ξ' μ x T ← ends-in-var? Ξ
  refl ← return Δ=Γ,μ∣x∈T -- Pattern matching on this proof only works since we already established that Ξ is of the form Ξ' ,,ᵛ μ ∣ x ∈ T.
                          -- Otherwise, unification would fail.
  ⟅ goals1 , ⟦p0⟧ ⟆ ← check-proof Ξ' p0 (φ [ zero / x ]bprop)
  ⟅ goals2 , ⟦ps⟧ ⟆ ← check-proof (Ξ' ,,ᵛ μ ∣ x ∈ Nat' ,,ᵇ 𝟙 ∣ hyp ∈ lock𝟙-bprop φ)
                                  ps
                                  (φ [ π ∷ˢ suc (var' x {skip-lock μ vzero} id-cell) / x ]bprop)
  return ⟅ goals1 ++ goals2 , sgoals ↦ {!!} ⟆
check-proof Ξ (fun-cong {μ = μ} {T = T} p t) φ = do
  is-eq lhs rhs ← is-eq? φ
  app {T = T2} {μ = ρ}  f s  ← is-app? lhs
  app {T = T3} {μ = ρ'} g s' ← is-app? rhs
  refl ← mod-dom μ =m? mod-dom ρ
  refl ← μ =mod? ρ
  refl ← mod-dom μ =m? mod-dom ρ'
  refl ← μ =mod? ρ'
  refl ← T =T? T2
  refl ← T =T? T3
  refl ← s =t? t
  refl ← s' =t? t
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof Ξ p (f ≡ᵇ g)
  return ⟅ goals , sgoals ↦ {!!} ⟆
check-proof Ξ (cong {μ = μ} {T = T} {S = S} f p) φ = do
  is-eq {T = S'} lhs rhs ← is-eq? φ
  app {T = T2} {μ = ρ}  g  t ← is-app? lhs
  app {T = T3} {μ = ρ'} g' s ← is-app? rhs
  refl ← mod-dom μ =m? mod-dom ρ
  refl ← μ =mod? ρ
  refl ← mod-dom μ =m? mod-dom ρ'
  refl ← μ =mod? ρ'
  refl ← S =T? S'
  refl ← T =T? T2
  refl ← T =T? T3
  refl ← g =t? f
  refl ← g' =t? f
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof (Ξ ,lock⟨ μ ⟩) p (t ≡ᵇ s)
  return ⟅ goals , sgoals ↦ {!!} ⟆
check-proof Ξ (hole name) φ = return ⟅ [ goal name Ξ φ ] , (sgl , _) ↦ sgl ⟆
