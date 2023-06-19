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
open import Relation.Nullary hiding (¬_)

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
import Model.Modality as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.IdentityType.Modal as M
import Experimental.DependentTypes.Model.Constant as M
import Experimental.DependentTypes.Model.Function as M renaming (lam to dlam)
import Model.Type.Constant as M
import Model.Type.Function as M
import Model.Type.Product as M

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

data IsImplication : bProp Γ → Set where
  is-implication : {Γ : Ctx m} (μ : Modality n m) (φ : bProp (Γ ,lock⟨ μ ⟩)) (ψ : bProp Γ) →
                   IsImplication (⟨ μ ∣ φ ⟩⊃ ψ)

is-implication? : (φ : bProp Γ) → PCM (IsImplication φ)
is-implication? (⟨ μ ∣ φ ⟩⊃ ψ) = return (is-implication μ φ ψ)
is-implication? φ = throw-error "bProp is not of the form ⟨ μ ∣ φ ⟩⊃ ψ."

data IsConjunction : bProp Γ → Set where
  is-conjunction : {Γ : Ctx m} (φ ψ : bProp Γ) → IsConjunction (φ ∧ ψ)

is-conjunction? : (φ : bProp Γ) → PCM (IsConjunction φ)
is-conjunction? (φ ∧ ψ) = return (is-conjunction φ ψ)
is-conjunction? _ = throw-error "bProp is not of the form φ ∧ ψ."

data IsModalProp : bProp Γ → Set where
  is-modal : {Γ : Ctx m} (μ : Modality n m) (φ : bProp (Γ ,lock⟨ μ ⟩)) →
             IsModalProp ⟨ μ ∣ φ ⟩

is-modal? : (φ : bProp Γ) → PCM (IsModalProp φ)
is-modal? ⟨ μ ∣ φ ⟩ = return (is-modal μ φ)
is-modal? _ = throw-error "bProp is not of the form ⟨ μ ∣ φ ⟩."


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

data IsNatRec : Tm Γ T → Set where
  nat-rec : ∀ {A} (z : Tm Γ A) (s : Tm Γ (A ⇛ A)) (n : Tm Γ Nat') → IsNatRec (nat-rec z s n)

is-nat-rec? : (t : Tm Γ T) → PCM (IsNatRec t)
is-nat-rec? (nat-rec z s n) = return (nat-rec z s n)
is-nat-rec? _ = throw-error "Natural number recursor expected"

data IsSucTm : Tm Γ T → Set where
  suc-tm : (n : Tm Γ Nat') → IsSucTm (suc n)

is-suc-tm? : (t : Tm Γ T) → PCM (IsSucTm t)
is-suc-tm? (suc n) = return (suc-tm n)
is-suc-tm? _ = throw-error "successor of natural number expected"


data IsFunTy : Ty m → Set where
  is-fun-ty : (μ : Modality n m) (T : Ty n) (S : Ty m) → IsFunTy (⟨ μ ∣ T ⟩⇛ S)

is-fun-ty? : (T : Ty m) → PCM (IsFunTy T)
is-fun-ty? (⟨ μ ∣ T ⟩⇛ S) = return (is-fun-ty μ T S)
is-fun-ty? _  = throw-error "Function type expected"

data IsProdTy : Ty m → Set where
  is-prod-ty : (T S : Ty m) → IsProdTy (T ⊠ S)

is-prod-ty? : (T : Ty m) → PCM (IsProdTy T)
is-prod-ty? (T ⊠ S) = return (is-prod-ty T S)
is-prod-ty? _  = throw-error "Product type expected"


data EndsInProgVar : ProofCtx m → Set where
  ends-in-prog-var : (Ξ : ProofCtx m) (μ : Modality n m) (x : String) (T : Ty n) → EndsInProgVar (Ξ ,,ᵛ μ ∣ x ∈ T)

ends-in-prog-var? : (Ξ : ProofCtx m) → PCM (EndsInProgVar Ξ)
ends-in-prog-var? (Ξ ,,ᵛ μ ∣ x ∈ T) = return (ends-in-prog-var Ξ μ x T)
ends-in-prog-var? _ = throw-error "Expected variable at head of proof context."


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

-- A useful lemma
sub-to-ctx-sub : (Ξ : ProofCtx m) (φ : bProp (to-ctx (Ξ ,,ᵛ μ ∣ x ∈ T))) (t : Tm (to-ctx (Ξ ,lock⟨ μ ⟩)) T) →
                 ⟦ φ [ t / x ]bprop ⟧bprop M.[ to-ctx-subst Ξ ]
                   M.≅ᵗʸ
                 (⟦ φ ⟧bprop M.[ to-ctx-subst (Ξ ,,ᵛ μ ∣ x ∈ T) ]) M.[
                    M.mod-intro ⟦ μ ⟧mod (⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.lock-fmap ⟦ μ ⟧mod (to-ctx-subst Ξ) ]cl) M./cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ ]
sub-to-ctx-sub {μ = μ} {x} {T} Ξ φ t =
  M.transᵗʸ (M.symᵗʸ (M.ty-subst-cong-ty _ (M.transᵗʸ (M.ty-subst-cong-subst (M.symˢ (/cl-sound t x)) ⟦ φ ⟧bprop) (bprop-sub-sound φ (t / x))))) (
  M.transᵗʸ (M.ty-subst-cong-subst-2-2 _ (M./cl-⊚ (ty-closed-natural ⟨ μ ∣ T ⟩) _ _)) (
  M.ty-subst-cong-subst (M.,cl-cong-tm (ty-closed-natural ⟨ μ ∣ T ⟩) (M.mod-intro-cl-natural ⟦ μ ⟧mod (ty-closed-natural T) ⟦ t ⟧tm)) _))

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
check-proof Ξ (subst {μ = μ} {x = x} {T = T} φ t1 t2 pe p1) ψ = do
  ⟅ goalse , ⟦pe⟧ ⟆ ← check-proof (Ξ ,lock⟨ μ ⟩) pe (t1 ≡ᵇ t2)
  ⟅ goals1 , ⟦p1⟧ ⟆ ← check-proof Ξ p1 (φ [ t1 / x ]bprop)
  refl ← ψ =b? φ [ t2 / x ]bprop
  return ⟅ goalse ++ goals1 , sgoals ↦ (let sgoalse , sgoals1 = split-sem-goals goalse goals1 sgoals in
    M.ι[ sub-to-ctx-sub Ξ φ t2 ]
    M.ι[ M.ty-subst-cong-subst (M./cl-cong (ty-closed-natural ⟨ μ ∣ T ⟩) (M.mod-intro-cong ⟦ μ ⟧mod (M.symᵗᵐ (
           M.eq-reflect (M.ι⁻¹[ M.Id-cl-natural (ty-closed-natural T) _ ] ⟦pe⟧ sgoalse))))) _ ]
    M.ι⁻¹[ sub-to-ctx-sub Ξ φ t1 ] ⟦p1⟧ sgoals1) ⟆
check-proof Ξ ⊤ᵇ-intro φ = do
  refl ← φ =b? ⊤ᵇ
  return ⟅ [] , _ ↦ M.tt' M.[ _ ]' ⟆
check-proof Ξ ⊥ᵇ-elim φ = do
  is-implication μ domφ codφ ← is-implication? φ
  refl ← mod-dom μ =m? mod-cod μ
  refl ← μ =mod? 𝟙
  refl ← domφ =b? ⊥ᵇ
  return ⟅ [] , _ ↦ M.empty-elim _ M.[ _ ]' ⟆
check-proof Ξ (⊃-intro x p) φ = do
  is-implication μ domφ codφ ← is-implication? φ
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof (Ξ ,,ᵇ μ ∣ x ∈ domφ) p codφ
  return ⟅ goals , sgoals ↦ M.ι[ M.⇛-natural _ ] M.lam _ (M.ι[ M.ty-subst-comp _ _ _ ] ⟦p⟧ sgoals) ⟆
check-proof Ξ (⊃-elim μ φ p1 p2) ψ = do
  ⟅ goals1 , ⟦p1⟧ ⟆ ← check-proof Ξ p1 (⟨ μ ∣ φ ⟩⊃ ψ)
  ⟅ goals2 , ⟦p2⟧ ⟆ ← check-proof (Ξ ,lock⟨ μ ⟩) p2 φ
  return ⟅ goals1 ++ goals2 , sgoals ↦ (let sgoals1 , sgoals2 = split-sem-goals goals1 goals2 sgoals in
    M.app (M.ι⁻¹[ M.⇛-natural _ ] ⟦p1⟧ sgoals1) (M.ι[ M.mod-natural ⟦ μ ⟧mod _ ] M.mod-intro ⟦ μ ⟧mod (⟦p2⟧ sgoals2))) ⟆
check-proof Ξ (∧-intro p1 p2) φ = do
  is-conjunction φ1 φ2 ← is-conjunction? φ
  ⟅ goals1 , ⟦p1⟧ ⟆ ← check-proof Ξ p1 φ1
  ⟅ goals2 , ⟦p2⟧ ⟆ ← check-proof Ξ p2 φ2
  return ⟅ goals1 ++ goals2 , sgoals ↦ (let sgoals1 , sgoals2 = split-sem-goals goals1 goals2 sgoals in
    M.ι[ M.⊠-natural _ ] M.pair (⟦p1⟧ sgoals1) (⟦p2⟧ sgoals2)) ⟆
check-proof Ξ (∧-elimˡ ψ p) φ = do
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof Ξ p (φ ∧ ψ)
  return ⟅ goals , sgoals ↦ M.fst (M.ι⁻¹[ M.⊠-natural _ ] ⟦p⟧ sgoals) ⟆
check-proof Ξ (∧-elimʳ ψ p) φ = do
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof Ξ p (ψ ∧ φ)
  return ⟅ goals , sgoals ↦ M.snd (M.ι⁻¹[ M.⊠-natural _ ] ⟦p⟧ sgoals) ⟆
check-proof Ξ (mod⟨ μ ⟩ p) φ = do
  is-modal κ ψ ← is-modal? φ
  refl ← mod-dom μ =m? mod-dom κ
  refl ← μ =mod? κ
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof (Ξ ,lock⟨ μ ⟩) p ψ
  return ⟅ goals , sgoals ↦ M.ι[ M.mod-natural ⟦ μ ⟧mod _ ] M.mod-intro ⟦ μ ⟧mod (⟦p⟧ sgoals) ⟆
check-proof Ξ (mod-elim ρ μ x φ p1 p2) ψ = do
  ⟅ goals1 , ⟦p1⟧ ⟆ ← check-proof (Ξ ,lock⟨ ρ ⟩) p1 ⟨ μ ∣ φ ⟩
  ⟅ goals2 , ⟦p2⟧ ⟆ ← check-proof (Ξ ,,ᵇ ρ ⓜ μ ∣ x ∈ fuselocks-bprop φ) p2 ψ
  return ⟅ goals1 ++ goals2 , sgoals ↦ (let sgoals1 , sgoals2 = split-sem-goals goals1 goals2 sgoals in
    M.ι⁻¹[ M.ty-subst-cong-subst-2-1 _ (M.transˢ M.⊚-assoc (M.transˢ (M.⊚-congʳ (M.ctx-ext-subst-β₁ _ _)) (M.id-subst-unitʳ _))) ] (
    ⟦p2⟧ sgoals2
      M.[ (M.ι[ M.ty-subst-cong-ty _ (M.transᵗʸ (M.eq-mod-tyʳ (⟦ⓜ⟧-sound ρ μ) _) (M.mod-cong ⟦ ρ ⟧mod (M.mod-cong ⟦ μ ⟧mod (fuselocks-bprop-sound φ)))) ]
          (M.ι[ M.mod-natural ⟦ ρ ⟧mod _ ]
          M.mod-intro ⟦ ρ ⟧mod (⟦p1⟧ sgoals1)))
        M./v ]')) ⟆
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
                               M.dlam ⟦ ⟨ μ ∣ T ⟩ ⟧ty (⟦p⟧ sgoals) ⟆
check-proof Ξ (∀-elim {n = n} {T = T} μ ψ p t) φ = do
  is-forall {n = n'} κ y S ψ' ← is-forall? ψ
  refl ← n =m? n'
  refl ← μ =mod? κ
  refl ← T =T? S
  refl ← φ =b? (ψ' [ t / y ]bprop)
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof Ξ p ψ
  return ⟅ goals , sgoals ↦ M.ι[ sub-to-ctx-sub Ξ ψ' t ]
         (M.cl-app (ty-closed-natural ⟨ μ ∣ T ⟩) (M.ι⁻¹[ M.Pi-natural-closed-dom (ty-closed-natural ⟨ μ ∣ T ⟩) _ ] (⟦p⟧ sgoals))
                                                 (M.mod-intro ⟦ μ ⟧mod (⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.lock-fmap ⟦ μ ⟧mod (to-ctx-subst Ξ) ]cl))) ⟆
check-proof Ξ fun-β φ = do
  is-eq lhs rhs ← is-eq? φ
  app f t ← is-app? lhs
  lam {T = A} {S = B} μ x b ← is-lam? f
  refl ← rhs =t? (b [ t / x ]tm)
  return ⟅ [] , _ ↦ M.≅ᵗᵐ-to-Id (
         M.transᵗᵐ (M.⇛-cl-β (ty-closed-natural ⟨ μ ∣ A ⟩) (ty-closed-natural B) _ _) (
         M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural B) (M.symˢ (/cl-sound t x))) (
         tm-sub-sound b (t / x))))
         M.[ _ ]' ⟆
check-proof Ξ nat-rec-β-zero φ = do
  is-eq lhs rhs ← is-eq? φ
  nat-rec z s n ← is-nat-rec? lhs
  refl ← n =t? zero
  refl ← rhs =t? z
  return ⟅ [] , _ ↦ (M.≅ᵗᵐ-to-Id (M.β-nat-zero _ _)) M.[ _ ]' ⟆
check-proof Ξ nat-rec-β-suc φ = do
  is-eq lhs rhs ← is-eq? φ
  nat-rec z s n ← is-nat-rec? lhs
  suc-tm n' ← is-suc-tm? n
  refl ← rhs =t? s ∙¹ (nat-rec z s n')
  return ⟅ [] , _ ↦ M.≅ᵗᵐ-to-Id (M.transᵗᵐ (M.β-nat-suc _ _ _) (M.symᵗᵐ (∙¹-sound s (nat-rec z s n')))) M.[ _ ]' ⟆
check-proof Ξ (fun-η x) φ = do
  is-eq {T = T} lhs rhs ← is-eq? φ
  is-fun-ty μ dom cod ← is-fun-ty? T
  refl ← rhs =t? (lam[ μ ∣ x ∈ dom ] (weaken-tm lhs ∙ v0))
  return ⟅ [] , _ ↦
    M.≅ᵗᵐ-to-Id (M.transᵗᵐ
      (M.⇛-cl-η (ty-closed-natural ⟨ μ ∣ dom ⟩) (ty-closed-natural cod) _)
      (M.lamcl-cong (ty-closed-natural cod) (M.app-cong (M.symᵗᵐ (weaken-tm-sound (to-ctx Ξ) x μ dom lhs))
                                                        (M.symᵗᵐ (M.transᵗᵐ (M.mod-intro-cong ⟦ μ ⟧mod (v0-sound (to-ctx Ξ) μ x dom))
                                                                            (M.mod-η ⟦ μ ⟧mod _))))))
      M.[ _ ]' ⟆
check-proof Ξ ⊠-η φ = do
  is-eq {T = P} lhs rhs ← is-eq? φ
  is-prod-ty T S ← is-prod-ty? P
  refl ← rhs =t? (pair (fst lhs) (snd lhs))
  return ⟅ [] , _ ↦ M.≅ᵗᵐ-to-Id (M.η-⊠ ⟦ lhs ⟧tm) M.[ _ ]' ⟆
check-proof Ξ true≠false φ = do
  refl ← φ =b? ¬⟨ 𝟙 ⟩ (true ≡ᵇ false)
  return ⟅ [] , _ ↦ M.true≠false M.[ _ ]' ⟆
check-proof Ξ (suc-inj m n) φ = do
  refl ← φ =b? (∀[ 𝟙 ∣ m ∈ Nat' ] (∀[ 𝟙 ∣ n ∈ Nat' ] ⟨ 𝟙 ∣ suc v1 ≡ᵇ suc v0 ⟩⊃ (v1-𝟙 ≡ᵇ v0-𝟙)))
  return ⟅ [] , _ ↦
    (M.ι[ M.Pi-cong-cod (M.Pi-cong-cod (
      M.⇛-cong (M.Id-cong' (M.suc'-cong (v1-sound-𝟙 (to-ctx Ξ) m Nat' 𝟙 n Nat')) (M.suc'-cong (v0-sound-𝟙 (to-ctx Ξ ,, 𝟙 ∣ m ∈ Nat') n Nat')))
               (M.Id-cong' (v1-𝟙-sound (to-ctx Ξ) m Nat' 𝟙 n Nat') (v0-𝟙-sound (to-ctx Ξ ,, 𝟙 ∣ m ∈ Nat') n Nat')))) ]
      M.suc-inj) M.[ _ ]' ⟆
check-proof Ξ (zero≠sucn m) φ = do
  refl ← φ =b? (∀[ 𝟙 ∣ m ∈ Nat' ] ¬⟨ 𝟙 ⟩ (zero ≡ᵇ suc v0))
  return ⟅ [] , _ ↦
    (M.ι[ M.Pi-cong-cod (M.⇛-cong (M.Id-cong' M.reflᵗᵐ (M.suc'-cong (v0-sound-𝟙 (to-ctx Ξ) m Nat')))
                                  M.reflᵗʸ) ]
    M.zero≠sucn) M.[ _ ]' ⟆
check-proof Ξ (bool-induction' Δ=Γ,x∈Bool pt pf) φ = do
  ends-in-prog-var Ξ' μ x T ← ends-in-prog-var? Ξ
  refl ← mod-dom μ =m? mod-cod μ
  refl ← μ =mod? 𝟙
  refl ← T =T? Bool'
  refl ← return Δ=Γ,x∈Bool
  ⟅ goalst , ⟦pt⟧ ⟆ ← check-proof Ξ' pt (φ [ true / x ]bprop)
  ⟅ goalsf , ⟦pf⟧ ⟆ ← check-proof Ξ' pf (φ [ false / x ]bprop)
  return ⟅ goalst ++ goalsf , sgoals ↦ (let sgoalst , sgoalsf = split-sem-goals goalst goalsf sgoals in
    M.bool-ind _
               (M.ι⁻¹[ M.transᵗʸ (M.ty-subst-cong-subst-2-2 ⟦ φ ⟧bprop (M./cl-⊚ (ty-closed-natural ⟨ 𝟙 ∣ Bool' ⟩) (to-ctx-subst Ξ') M.true'))
                                 (M.ty-subst-cong-subst (M.transˢ (M./cl-cong-cl (M.𝟙-preserves-cl M.const-closed))
                                                                  (M./cl-cong M.const-closed (M.transᵗᵐ (M.cl-tm-subst-cong-cl (M.𝟙-preserves-cl M.const-closed))
                                                                                                        (M.const-cl-natural (to-ctx-subst Ξ'))))) _) ]
                 (M.ι[ M.ty-subst-cong-ty _ (M.transᵗʸ (M.ty-subst-cong-subst (M.symˢ (/cl-sound {Γ = to-ctx Ξ'} {μ = 𝟙} true x)) _)
                                                       (bprop-sub-sound φ _)) ]
                 ⟦pt⟧ sgoalst))
               (M.ι⁻¹[ M.transᵗʸ (M.ty-subst-cong-subst-2-2 ⟦ φ ⟧bprop (M./cl-⊚ (ty-closed-natural ⟨ 𝟙 ∣ Bool' ⟩) (to-ctx-subst Ξ') M.false'))
                                 (M.ty-subst-cong-subst (M.transˢ (M./cl-cong-cl (M.𝟙-preserves-cl M.const-closed))
                                                                  (M./cl-cong M.const-closed (M.transᵗᵐ (M.cl-tm-subst-cong-cl (M.𝟙-preserves-cl M.const-closed))
                                                                                                        (M.const-cl-natural (to-ctx-subst Ξ'))))) _) ]
                 (M.ι[ M.ty-subst-cong-ty _ (M.transᵗʸ (M.ty-subst-cong-subst (M.symˢ (/cl-sound {Γ = to-ctx Ξ'} {μ = 𝟙} false x)) _)
                                                       (bprop-sub-sound φ _)) ]
                 ⟦pf⟧ sgoalsf))) ⟆
check-proof Ξ (nat-induction' hyp Δ=Γ,x∈Nat p0 ps) φ = do
  ends-in-prog-var Ξ' μ x T ← ends-in-prog-var? Ξ
  refl ← mod-dom μ =m? mod-cod μ
  refl ← μ =mod? 𝟙
  refl ← return Δ=Γ,x∈Nat
    -- ^ Before this step, ps is a proof in Δ = to-ctx Ξ' ,,ᵛ μ ∣ x ∈ T and p0 is a proof in Γ.
    -- By pattern matching on Δ=Γ,x∈Nat : Δ ≡ Γ ,, x ∈ Nat', Γ gets unified with to-ctx Ξ', μ with 𝟙 and T with Nat'.
    -- Pattern matching on this proof only works since we already established that Ξ is of the form Ξ' ,,ᵛ μ ∣ x ∈ T.
    -- Otherwise, unification would fail.
  ⟅ goals1 , ⟦p0⟧ ⟆ ← check-proof Ξ' p0 (φ [ zero / x ]bprop)
  ⟅ goals2 , ⟦ps⟧ ⟆ ← check-proof (Ξ' ,,ᵛ 𝟙 ∣ x ∈ Nat' ,,ᵇ 𝟙 ∣ hyp ∈ lock𝟙-bprop φ)
                                  ps
                                  (φ [ π ∷ˢ suc v0 / x ]bprop)
  return ⟅ goals1 ++ goals2 , sgoals ↦
    (let sgoals1 , sgoals2 = split-sem-goals goals1 goals2 sgoals
     in M.nat-ind _ (M.ι[ M.transᵗʸ (M.ty-subst-cong-subst (M.transˢ (M./v-cong (M.symᵗᵐ (M.transᵗᵐ (M.cl-tm-subst-cong-cl (M.𝟙-preserves-cl M.const-closed))
                                                                                                                           (M.const-cl-natural _))))
                                                                     (M./v-/cl (ty-closed-natural ⟨ 𝟙 ∣ Nat' ⟩) _))
                                                           _)
                                    (M.ty-subst-cong-subst-2-2 _ (M.symˢ (M./cl-⊚ (ty-closed-natural ⟨ 𝟙 ∣ Nat' ⟩) _ M.zero'))) ]
                      (M.ι[ M.ty-subst-cong-ty _ (M.transᵗʸ (M.ty-subst-cong-subst (M.symˢ (/cl-sound {Γ = to-ctx Ξ'} {μ = 𝟙} zero x)) _) (bprop-sub-sound φ (zero / x))) ]
                      (⟦p0⟧ sgoals1)))
                    (M.ι⁻¹[ M.ty-subst-cong-subst-2-1 _ (M.transˢ M.⊚-assoc (M.⊚-congʳ (M.,,-map-π _))) ]
                      (M.ιc⁻¹[ M.,,-cong (M.ty-subst-cong-ty _ (lock𝟙-bprop-sound φ)) ]'
                      (M.ι⁻¹[ M.ty-subst-cong-subst (M.⊚-congˡ (
                              M.transˢ (M.,cl-cong-cl (M.𝟙-preserves-cl M.const-closed))
                                       (M.,cl-cong-tm M.const-closed (M.transᵗᵐ (M.cl-tm-subst-cong-cl (M.𝟙-preserves-cl M.const-closed))
                                                                     (M.transᵗᵐ (M.suc'-cl-natural _)
                                                                     (M.transᵗᵐ (M.const-map-cong _ (M.symᵗᵐ (M.cl-tm-subst-cong-cl (M.𝟙-preserves-cl M.const-closed))))
                                                                     (M.const-map-cong _ (M.transᵗᵐ (M.lift-cl-ξcl (ty-closed-natural ⟨ 𝟙 ∣ Nat' ⟩) {σ = to-ctx-subst Ξ'})
                                                                                                    (M.ξcl-cong-cl (M.𝟙-preserves-cl M.const-closed)))))))))) _ ]
                      (M.ι[ M.ty-subst-cong-subst-2-2 _ (M.transˢ (M.symˢ M.⊚-assoc)
                                                        (M.transˢ (M.⊚-congˡ (M.lift-cl-,cl (ty-closed-natural ⟨ 𝟙 ∣ Nat' ⟩) (ty-closed-natural ⟨ 𝟙 ∣ Nat' ⟩) _ _))
                                                        M.⊚-assoc)) ]
                      (M.ι[ M.ty-subst-cong-ty _ (
                              M.transᵗʸ (M.ty-subst-cong-subst (M.symˢ
                                          (M.transˢ (∷ˢ-sound {Δ = to-ctx Ξ'} π (suc (v0 {μ = 𝟙} {x = x})) x)
                                                    (M.,cl-cong (ty-closed-natural ⟨ 𝟙 ∣ Nat' ⟩)
                                                                (sub-π-sound (to-ctx Ξ') x 𝟙 Nat')
                                                                (M.const-map-cong _ (v0-sound (to-ctx Ξ') 𝟙 x Nat')))))
                                          _)
                                        (bprop-sub-sound φ _)) ]
                      ⟦ps⟧ sgoals2)))))) ⟆
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
  return ⟅ goals , sgoals ↦
    M.ι[ M.Id-natural _ ] M.ι[ M.Id-cong' (M.app-natural _ _ _) (M.app-natural _ _ _) ]
    M.fun-cong' (M.ι⁻¹[ M.Id-cong (M.⇛-natural _) (M.symᵗᵐ M.ι-symʳ) (M.symᵗᵐ M.ι-symʳ) ] (M.ι⁻¹[ M.Id-natural _ ] ⟦p⟧ sgoals))
                _ ⟆
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
  return ⟅ goals , sgoals ↦
    M.ι[ M.Id-natural _ ] M.ι[ M.Id-cong' (M.app-natural _ _ _) (M.app-natural _ _ _) ]
    M.cong' _ (M.ι[ M.Id-cong (M.mod-natural ⟦ μ ⟧mod _) (M.mod-intro-natural ⟦ μ ⟧mod _ _) (M.mod-intro-natural ⟦ μ ⟧mod _ _) ]
              M.id-mod-intro-cong ⟦ μ ⟧mod (M.ι⁻¹[ M.Id-natural _ ] ⟦p⟧ sgoals)) ⟆
check-proof Ξ (hole name) φ = return ⟅ [ goal name Ξ φ ] , (sgl , _) ↦ sgl ⟆
