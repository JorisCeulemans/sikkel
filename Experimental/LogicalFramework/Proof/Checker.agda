open import Experimental.LogicalFramework.Parameter

module Experimental.LogicalFramework.Proof.Checker
  (ℬ : BiSikkelParameter)
  where

open import Data.List
open import Data.String as Str hiding (_≟_; _++_)
open import Data.Product
import Relation.Binary.PropositionalEquality as Ag

open BiSikkelParameter ℬ
open import Experimental.LogicalFramework.Parameter.ProofExtension 𝒫 𝒷 ⟦𝒷⟧
open ProofExt 𝓅
open import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯 String

open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.bProp 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Proof.Definition ℬ
open import Experimental.LogicalFramework.Proof.CheckingMonad
open import Experimental.LogicalFramework.Proof.Equality 𝒫 𝒷
open import Experimental.LogicalFramework.Proof.Context 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Postulates 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Proof.Checker.ResultType 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Proof.Checker.SyntaxViews 𝒫 𝒷 ⟦𝒷⟧

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  Γ Δ : Ctx m
  T S R U : Ty m
  φ ψ : bProp Γ
  x y : String
  Ξ : ProofCtx m

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.DRA as DRA hiding (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; TwoCell; id-cell)
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.IdentityType.Modal as M
import Experimental.DependentTypes.Model.Constant as M
import Experimental.DependentTypes.Model.Function as M renaming (lam to dlam)
import Model.Type.Constant as M
import Model.Type.Function as M
import Model.Type.Product as M
open import Experimental.LogicalFramework.Proof.Checker.Soundness ℬ



check-proof : (Ξ : ProofCtx m) → Proof (to-ctx Ξ) → (φ : bProp (to-ctx Ξ)) → PCM (PCResult Ξ φ)
check-proof-explicit-constraint : (Ξ : ProofCtx m) {Γ : Ctx m} → to-ctx Ξ Ag.≡ Γ →
                                  Proof Γ → (φ : bProp (to-ctx Ξ)) →
                                  PCM (PCResult Ξ φ)
check-proof-ext : {infos : List (ArgInfo m)} →
                  (Ξ : ProofCtx m) (φ : bProp (to-ctx Ξ)) →
                  ExtPfArgs infos (to-ctx Ξ) →
                  ProofCheckExt infos Ξ φ →
                  PCM (PCResult Ξ φ)

check-proof Ξ refl φ = do
  is-eq t1 t2 ← is-eq? φ
  refl ← t1 ≟tm t2
  return ⟅ [] , _ ↦ M.refl' _ M.[ _ ]' ⟆
check-proof Ξ (sym p) φ = do
  is-eq t1 t2 ← is-eq? φ
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof Ξ p (t2 ≡ᵇ t1)
  return ⟅ goals , sgoals ↦ M.ι[ M.Id-natural _ ] M.sym' (M.ι⁻¹[ M.Id-natural _ ] ⟦p⟧ sgoals) ⟆
check-proof Ξ (trans {T = T'} middle-tm p1 p2) φ = do
  is-eq {T = T} t s ← is-eq? φ
  refl ← T ≟ty T'
  ⟅ goals1 , ⟦p1⟧ ⟆ ← check-proof Ξ p1 (t ≡ᵇ middle-tm)
  ⟅ goals2 , ⟦p2⟧ ⟆ ← check-proof Ξ p2 (middle-tm ≡ᵇ s)
  return ⟅ goals1 ++ goals2
         , sgoals ↦ (let sgoals1 , sgoals2 = split-sem-goals goals1 goals2 sgoals
                      in M.ι[ M.Id-natural _ ] M.trans' (M.ι⁻¹[ M.Id-natural _ ] ⟦p1⟧ sgoals1) (M.ι⁻¹[ M.Id-natural _ ] ⟦p2⟧ sgoals2))
         ⟆
check-proof Ξ (subst {μ = μ} {x = x} {T = T} φ t1 t2 pe p1) ψ = do
  ⟅ goalse , ⟦pe⟧ ⟆ ← check-proof (Ξ ,lock⟨ μ ⟩) pe (t1 ≡ᵇ t2)
  ⟅ goals1 , ⟦p1⟧ ⟆ ← check-proof Ξ p1 (φ [ t1 / x ]bprop)
  refl ← ψ ≟bprop φ [ t2 / x ]bprop
  return ⟅ goalse ++ goals1 , sgoals ↦ (let sgoalse , sgoals1 = split-sem-goals goalse goals1 sgoals in
    M.ι[ to-ctx-/-commute Ξ φ t2 ]
    M.ι[ M.ty-subst-cong-subst (M./cl-cong (ty-closed-natural ⟨ μ ∣ T ⟩) (dra-intro-cong ⟦ μ ⟧mod (M.symᵗᵐ (
           M.eq-reflect (M.ι⁻¹[ M.Id-cl-natural (ty-closed-natural T) _ ] ⟦pe⟧ sgoalse))))) _ ]
    M.ι⁻¹[ to-ctx-/-commute Ξ φ t1 ] ⟦p1⟧ sgoals1) ⟆
check-proof Ξ ⊤ᵇ-intro φ = do
  refl ← φ ≟bprop ⊤ᵇ
  return ⟅ [] , _ ↦ M.tt' M.[ _ ]' ⟆
check-proof Ξ (⊥ᵇ-elim p) φ = do
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof Ξ p ⊥ᵇ
  return ⟅ goals , sgoals ↦ M.app (M.ι⁻¹[ M.⇛-natural _ ] (M.empty-elim _ M.[ _ ]')) (⟦p⟧ sgoals) ⟆
check-proof Ξ (⊃-intro x p) φ = do
  is-implication μ domφ codφ ← is-implication? φ
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof (Ξ ,,ᵇ μ ∣ x ∈ domφ) p codφ
  return ⟅ goals , sgoals ↦ M.ι[ M.⇛-natural _ ] M.lam _ (M.ι[ M.ty-subst-comp _ _ _ ] ⟦p⟧ sgoals) ⟆
check-proof Ξ (⊃-elim μ φ p1 p2) ψ = do
  ⟅ goals1 , ⟦p1⟧ ⟆ ← check-proof Ξ p1 (⟨ μ ∣ φ ⟩⊃ ψ)
  ⟅ goals2 , ⟦p2⟧ ⟆ ← check-proof (Ξ ,lock⟨ μ ⟩) p2 φ
  return ⟅ goals1 ++ goals2 , sgoals ↦ (let sgoals1 , sgoals2 = split-sem-goals goals1 goals2 sgoals in
    M.app (M.ι⁻¹[ M.⇛-natural _ ] ⟦p1⟧ sgoals1) (M.ι[ dra-natural ⟦ μ ⟧mod _ ] dra-intro ⟦ μ ⟧mod (⟦p2⟧ sgoals2))) ⟆
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
  refl ← mod-dom μ ≟mode mod-dom κ
  refl ← μ ≟mod κ
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof (Ξ ,lock⟨ μ ⟩) p ψ
  return ⟅ goals , sgoals ↦ M.ι[ dra-natural ⟦ μ ⟧mod _ ] dra-intro ⟦ μ ⟧mod (⟦p⟧ sgoals) ⟆
check-proof Ξ (mod-elim ρ μ x φ p1 p2) ψ = do
  ⟅ goals1 , ⟦p1⟧ ⟆ ← check-proof (Ξ ,lock⟨ ρ ⟩) p1 ⟨ μ ∣ φ ⟩
  ⟅ goals2 , ⟦p2⟧ ⟆ ← check-proof (Ξ ,,ᵇ ρ ⓜ μ ∣ x ∈ fuselocks-bprop φ) p2 ψ
  return ⟅ goals1 ++ goals2 , sgoals ↦ (let sgoals1 , sgoals2 = split-sem-goals goals1 goals2 sgoals in
    M.ι⁻¹[ M.ty-subst-cong-subst-2-1 _ (M.transˢ M.⊚-assoc (M.transˢ (M.⊚-congʳ (M.ctx-ext-subst-β₁ _ _)) (M.id-subst-unitʳ _))) ] (
    ⟦p2⟧ sgoals2
      M.[ (M.ι[ M.ty-subst-cong-ty _ (M.transᵗʸ (eq-dra-tyʳ (⟦ⓜ⟧-sound ρ μ) _) (dra-cong ⟦ ρ ⟧mod (dra-cong ⟦ μ ⟧mod (fuselocks-bprop-sound φ)))) ]
          (M.ι[ dra-natural ⟦ ρ ⟧mod _ ]
          dra-intro ⟦ ρ ⟧mod (⟦p1⟧ sgoals1)))
        M./v ]')) ⟆
check-proof Ξ (assumption' x {μ = μ} {κ = κ} α) φ = do
  contains-assumption κ' a ← contains-assumption? x μ Ξ
  refl ← κ' ≟mod κ
  refl ← φ ≟bprop lookup-assumption a α
  return ⟅ [] , _ ↦ ⟦ a , α ⟧assumption ⟆
check-proof Ξ (∀-intro[_∣_∈_]_ {n = n} μ x T p) φ = do
  is-forall {n = n'} κ y S φ' ← is-forall? φ
  refl ← n ≟mode n'
  refl ← μ ≟mod κ
  refl ← from-dec "Alpha equivalence is currently not supported" (x Str.≟ y)
  refl ← T ≟ty S
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof (Ξ ,,ᵛ μ ∣ x ∈ T) p φ'
  return ⟅ goals , sgoals ↦ M.ι[ M.Pi-natural-closed-dom (ty-closed-natural ⟨ μ ∣ T ⟩) _ ]
                               M.dlam ⟦ ⟨ μ ∣ T ⟩ ⟧ty (⟦p⟧ sgoals) ⟆
check-proof Ξ (∀-elim {n = n} {T = T} μ ψ p t) φ = do
  is-forall {n = n'} κ y S ψ' ← is-forall? ψ
  refl ← n ≟mode n'
  refl ← μ ≟mod κ
  refl ← T ≟ty S
  refl ← φ ≟bprop (ψ' [ t / y ]bprop)
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof Ξ p ψ
  return ⟅ goals , sgoals ↦ M.ι[ to-ctx-/-commute Ξ ψ' t ]
         (M.cl-app (ty-closed-natural ⟨ μ ∣ T ⟩) (M.ι⁻¹[ M.Pi-natural-closed-dom (ty-closed-natural ⟨ μ ∣ T ⟩) _ ] (⟦p⟧ sgoals))
                                                 (dra-intro ⟦ μ ⟧mod (⟦ t ⟧tm M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ μ ⟧mod (to-ctx-subst Ξ) ]cl))) ⟆
check-proof Ξ fun-β φ = do
  is-eq lhs rhs ← is-eq? φ
  app f t ← is-app? lhs
  lam {T = A} {S = B} μ x b ← is-lam? f
  refl ← rhs ≟tm (b [ t / x ]tm)
  return ⟅ [] , _ ↦ M.≅ᵗᵐ-to-Id (
         M.transᵗᵐ (M.⇛-cl-β (ty-closed-natural ⟨ μ ∣ A ⟩) (ty-closed-natural B) _ _) (
         M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural B) (M.symˢ (/cl-sound t x))) (
         tm-sub-sound b (t / x))))
         M.[ _ ]' ⟆
check-proof Ξ nat-rec-β-zero φ = do
  is-eq lhs rhs ← is-eq? φ
  nat-rec z s n ← is-nat-rec? lhs
  refl ← n ≟tm zero
  refl ← rhs ≟tm z
  return ⟅ [] , _ ↦ (M.≅ᵗᵐ-to-Id (M.β-nat-zero _ _)) M.[ _ ]' ⟆
check-proof Ξ nat-rec-β-suc φ = do
  is-eq lhs rhs ← is-eq? φ
  nat-rec z s n ← is-nat-rec? lhs
  suc-tm n' ← is-suc-tm? n
  refl ← rhs ≟tm s ∙¹ (nat-rec z s n')
  return ⟅ [] , _ ↦ M.≅ᵗᵐ-to-Id (M.transᵗᵐ (M.β-nat-suc _ _ _) (M.symᵗᵐ (∙¹-sound s (nat-rec z s n')))) M.[ _ ]' ⟆
check-proof Ξ (fun-η x) φ = do
  is-eq {T = T} lhs rhs ← is-eq? φ
  is-fun-ty μ dom cod ← is-fun-ty? T
  refl ← rhs ≟tm (lam[ μ ∣ x ∈ dom ] (weaken-tm lhs ∙ v0))
  return ⟅ [] , _ ↦
    M.≅ᵗᵐ-to-Id (M.transᵗᵐ
      (M.⇛-cl-η (ty-closed-natural ⟨ μ ∣ dom ⟩) (ty-closed-natural cod) _)
      (M.lamcl-cong (ty-closed-natural cod) (M.app-cong (M.symᵗᵐ (weaken-tm-sound (to-ctx Ξ) x μ dom lhs))
                                                        (M.symᵗᵐ (M.transᵗᵐ (dra-intro-cong ⟦ μ ⟧mod (v0-sound (to-ctx Ξ) μ x dom))
                                                                            (dra-η ⟦ μ ⟧mod _))))))
      M.[ _ ]' ⟆
check-proof Ξ ⊠-η φ = do
  is-eq {T = P} lhs rhs ← is-eq? φ
  is-prod-ty T S ← is-prod-ty? P
  refl ← rhs ≟tm (pair (fst lhs) (snd lhs))
  return ⟅ [] , _ ↦ M.≅ᵗᵐ-to-Id (M.η-⊠ ⟦ lhs ⟧tm) M.[ _ ]' ⟆
check-proof Ξ true≠false φ = do
  refl ← φ ≟bprop ¬⟨ 𝟙 ⟩ (true ≡ᵇ false)
  return ⟅ [] , _ ↦ M.true≠false M.[ _ ]' ⟆
check-proof Ξ (suc-inj m n) φ = do
  refl ← φ ≟bprop (∀[ 𝟙 ∣ m ∈ Nat' ] (∀[ 𝟙 ∣ n ∈ Nat' ] ⟨ 𝟙 ∣ suc v1 ≡ᵇ suc v0 ⟩⊃ (v1-𝟙 ≡ᵇ v0-𝟙)))
  return ⟅ [] , _ ↦
    (M.ι[ M.Pi-cong-cod (M.Pi-cong-cod (
      M.⇛-cong (M.Id-cong' (M.suc'-cong (v1-sound-𝟙 (to-ctx Ξ) m Nat' 𝟙 n Nat')) (M.suc'-cong (v0-sound-𝟙 (to-ctx Ξ ,, 𝟙 ∣ m ∈ Nat') n Nat')))
               (M.Id-cong' (v1-𝟙-sound (to-ctx Ξ) m Nat' 𝟙 n Nat') (v0-𝟙-sound (to-ctx Ξ ,, 𝟙 ∣ m ∈ Nat') n Nat')))) ]
      M.suc-inj) M.[ _ ]' ⟆
check-proof Ξ (zero≠sucn m) φ = do
  refl ← φ ≟bprop (∀[ 𝟙 ∣ m ∈ Nat' ] ¬⟨ 𝟙 ⟩ (zero ≡ᵇ suc v0))
  return ⟅ [] , _ ↦
    (M.ι[ M.Pi-cong-cod (M.⇛-cong (M.Id-cong' M.reflᵗᵐ (M.suc'-cong (v0-sound-𝟙 (to-ctx Ξ) m Nat')))
                                  M.reflᵗʸ) ]
    M.zero≠sucn) M.[ _ ]' ⟆
check-proof Ξ (bool-induction' Δ=Γ,x∈Bool pt pf) φ = do
  ends-in-prog-var Ξ' μ x T ← ends-in-prog-var? Ξ
  refl ← return Δ=Γ,x∈Bool
  ⟅ goalst , ⟦pt⟧ ⟆ ← check-proof Ξ' pt (φ [ true  / x ]bprop)
  ⟅ goalsf , ⟦pf⟧ ⟆ ← check-proof Ξ' pf (φ [ false / x ]bprop)
  return ⟅ goalst ++ goalsf , sgoals ↦ (let sgoalst , sgoalsf = split-sem-goals goalst goalsf sgoals in
    M.bool-ind _
               (M.ι⁻¹[ M.ty-subst-cong-subst (M./cl-cong M.const-closed (M.const-cl-natural (to-ctx-subst Ξ'))) _ ] (
                 M.ι⁻¹[ to-ctx-/-commute-𝟙 Ξ' φ true ] ⟦pt⟧ sgoalst))
               (M.ι⁻¹[ M.ty-subst-cong-subst (M./cl-cong M.const-closed (M.const-cl-natural (to-ctx-subst Ξ'))) _ ] (
                 M.ι⁻¹[ to-ctx-/-commute-𝟙 Ξ' φ false ] ⟦pf⟧ sgoalsf))) ⟆
check-proof Ξ (nat-induction' hyp Δ=Γ,x∈Nat p0 ps) φ = do
  ends-in-prog-var Ξ' μ x T ← ends-in-prog-var? Ξ
  refl ← return Δ=Γ,x∈Nat
    -- ^ Before this step, ps is a proof in Δ = to-ctx Ξ' ,,ᵛ μ ∣ x ∈ T and p0 is a proof in Γ.
    -- By pattern matching on Δ=Γ,x∈Nat : Δ ≡ Γ ,, x ∈ Nat', Γ gets unified with to-ctx Ξ', μ with 𝟙 and T with Nat'.
    -- Pattern matching on this proof only works since we already established that Ξ is of the form Ξ' ,,ᵛ μ ∣ x ∈ T.
    -- Otherwise, unification would fail.
  ⟅ goals1 , ⟦p0⟧ ⟆ ← check-proof Ξ' p0 (φ [ zero / x ]bprop)
  ⟅ goals2 , ⟦ps⟧ ⟆ ← check-proof (Ξ' ,,ᵛ 𝟙 ∣ x ∈ Nat' ,,ᵇ 𝟙 ∣ hyp ∈ lock𝟙-bprop φ)
                                  ps
                                  (φ [ suc v0 // x ]bprop)
  return ⟅ goals1 ++ goals2 , sgoals ↦
    (let sgoals1 , sgoals2 = split-sem-goals goals1 goals2 sgoals
     in M.nat-ind _ (M.ι⁻¹[ M.ty-subst-cong-subst (M./cl-cong M.const-closed (M.const-cl-natural (to-ctx-subst Ξ'))) _ ]
                      (M.ι⁻¹[ to-ctx-/-commute-𝟙 Ξ' φ zero ] ⟦p0⟧ sgoals1))
                    (M.ι⁻¹[ M.ty-subst-cong-subst-2-1 _ (M.transˢ M.⊚-assoc (M.⊚-congʳ (M.,,-map-π _))) ]
                      (M.ιc⁻¹[ M.,,-cong (M.ty-subst-cong-ty _ (lock𝟙-bprop-sound φ)) ]'
                      (M.ι⁻¹[ M.ty-subst-cong-subst (M.⊚-congˡ (
                              M.transˢ (M.,cl-cong-cl (𝟙-preserves-cl M.const-closed))
                                       (M.,cl-cong-tm M.const-closed (M.transᵗᵐ (M.cl-tm-subst-cong-cl (𝟙-preserves-cl M.const-closed))
                                                                     (M.transᵗᵐ (M.suc'-cl-natural _)
                                                                     (M.transᵗᵐ (M.const-map-cong _ (M.symᵗᵐ (M.cl-tm-subst-cong-cl (𝟙-preserves-cl M.const-closed))))
                                                                     (M.const-map-cong _ (M.transᵗᵐ (M.lift-cl-ξcl (ty-closed-natural ⟨ 𝟙 ∣ Nat' ⟩) {σ = to-ctx-subst Ξ'})
                                                                                                    (M.ξcl-cong-cl (𝟙-preserves-cl M.const-closed)))))))))) _ ]
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
check-proof Ξ (mod-induction' {T = T} κ μ x ctx-eq p) φ = do
  ends-in-prog-var Ξ' μ' y _ ← ends-in-prog-var? Ξ
  refl ← return ctx-eq
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof (Ξ' ,,ᵛ μ ⓜ κ ∣ x ∈ T) p (φ [ mod⟨ κ ⟩ (var' x {skip-lock κ (skip-lock μ vzero)} id-cell) // y ]bprop)
  return ⟅ goals , sgoals ↦
    M.ι⁻¹[ M.transᵗʸ (M.ty-subst-cong-subst-2-2 _ (M.symˢ (M.lift-cl-,,-cong-commute (M.symᶜᵗʸ (eq-dra-closed (⟦ⓜ⟧-sound μ κ) (ty-closed-natural T))) (to-ctx-subst Ξ')))) (
           M.transᵗʸ (M.ty-subst-cong-subst (M.lift-cl-subst-cong-cl (ⓓ-preserves-cl ⟦ μ ⟧mod ⟦ κ ⟧mod (ty-closed-natural T))) _) (
           M.ty-subst-cong-ty _ (M.ty-subst-cong-subst-2-0 ⟦ φ ⟧bprop (
             M.transˢ (M.,cl-⊚ (ty-closed-natural ⟨ μ ∣ ⟨ κ ∣ T ⟩ ⟩) _ _ _) (
             M.transˢ (M.,cl-cong (ty-closed-natural ⟨ μ ∣ ⟨ κ ∣ T ⟩ ⟩) (M.transˢ (M.,,-map-π _) (M.symˢ (M.id-subst-unitʳ M.π))) (
               M.transᵗᵐ (M.cl-tm-subst-cong-tm (ty-closed-natural ⟨ μ ∣ ⟨ κ ∣ T ⟩ ⟩) (M.transᵗᵐ (dra-intro-cong ⟦ μ ⟧mod (dra-η ⟦ κ ⟧mod _)) (dra-η ⟦ μ ⟧mod _))) (
               M.transᵗᵐ (M.cl-tm-subst-cong-tm (ty-closed-natural ⟨ μ ∣ ⟨ κ ∣ T ⟩ ⟩) (M.symᵗᵐ (M.ξcl-,,-cong (eq-dra-closed (⟦ⓜ⟧-sound μ κ) (ty-closed-natural T))))) (
               M.transᵗᵐ (M.cl-tm-subst-cong-tm (ty-closed-natural ⟨ μ ∣ ⟨ κ ∣ T ⟩ ⟩) (
                 M.transᵗᵐ (M.cl-tm-subst-cong-cl (ⓓ-preserves-cl ⟦ μ ⟧mod ⟦ κ ⟧mod (ty-closed-natural T)))
                           (M.cl-tm-subst-cong-tm (ty-closed-natural ⟨ μ ∣ ⟨ κ ∣ T ⟩ ⟩) (M.ξcl-cong-cl (ⓓ-preserves-cl ⟦ μ ⟧mod ⟦ κ ⟧mod (ty-closed-natural T))))))
                         (M.cl-tm-subst-cong-subst-2-1 (ty-closed-natural ⟨ μ ∣ ⟨ κ ∣ T ⟩ ⟩)
                                                       {Δ' = ⟦ to-ctx Ξ' ⟧ctx M.,, DRA.⟨ ⟦ μ ⟧mod ∣ DRA.⟨ ⟦ κ ⟧mod ∣ ⟦ T ⟧ty ⟩ ⟩}
                                                       (M.isoʳ (M.,,-cong (eq-dra-ty-closed (⟦ⓜ⟧-sound μ κ) (ty-closed-natural T))))))))) (
             M.symˢ (M.,cl-η (ty-closed-natural ⟨ μ ∣ ⟨ κ ∣ T ⟩ ⟩) _))))))) ]
    M.ι[ M.ty-subst-cong-ty _ (M.ty-subst-cong-ty _ (
         M.transᵗʸ (M.ty-subst-cong-subst (M.symˢ (
           M.transˢ (∷ˢ-sound (π {Γ = to-ctx Ξ'} {T = T}) (mod⟨ κ ⟩ var' x {skip-lock κ (skip-lock μ vzero)} id-cell) y)
                    (M.,cl-cong (ty-closed-natural ⟨ μ ∣ ⟨ κ ∣ T ⟩ ⟩)
                                (sub-π-sound (to-ctx Ξ') y (μ ⓜ κ) T)
                                (dra-intro-cong ⟦ μ ⟧mod (dra-intro-cong ⟦ κ ⟧mod (v0-2lock-sound μ κ x (to-ctx Ξ') T))))))
                    ⟦ φ ⟧bprop) (
         bprop-sub-sound φ _))) ] (
    M.ιc⁻¹[ M.,,-cong (DRA.eq-dra-ty-closed (⟦ⓜ⟧-sound μ κ) (ty-closed-natural T)) ]'
    ⟦p⟧ sgoals) ⟆
check-proof Ξ (fun-cong {μ = μ} {T = T} p t) φ = do
  is-eq lhs rhs ← is-eq? φ
  app {T = T2} {μ = ρ}  f s  ← is-app? lhs
  app {T = T3} {μ = ρ'} g s' ← is-app? rhs
  refl ← mod-dom μ ≟mode mod-dom ρ
  refl ← μ ≟mod ρ
  refl ← mod-dom μ ≟mode mod-dom ρ'
  refl ← μ ≟mod ρ'
  refl ← T ≟ty T2
  refl ← T ≟ty T3
  refl ← s ≟tm t
  refl ← s' ≟tm t
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof Ξ p (f ≡ᵇ g)
  return ⟅ goals , sgoals ↦
    M.ι[ M.Id-natural _ ] M.ι[ M.Id-cong' (M.app-natural _ _ _) (M.app-natural _ _ _) ]
    M.fun-cong' (M.ι⁻¹[ M.Id-cong (M.⇛-natural _) (M.symᵗᵐ M.ι-symʳ) (M.symᵗᵐ M.ι-symʳ) ] (M.ι⁻¹[ M.Id-natural _ ] ⟦p⟧ sgoals))
                _ ⟆
check-proof Ξ (cong {μ = μ} {T = T} {S = S} f p) φ = do
  is-eq {T = S'} lhs rhs ← is-eq? φ
  app {T = T2} {μ = ρ}  g  t ← is-app? lhs
  app {T = T3} {μ = ρ'} g' s ← is-app? rhs
  refl ← mod-dom μ ≟mode mod-dom ρ
  refl ← μ ≟mod ρ
  refl ← mod-dom μ ≟mode mod-dom ρ'
  refl ← μ ≟mod ρ'
  refl ← S ≟ty S'
  refl ← T ≟ty T2
  refl ← T ≟ty T3
  refl ← g ≟tm f
  refl ← g' ≟tm f
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof (Ξ ,lock⟨ μ ⟩) p (t ≡ᵇ s)
  return ⟅ goals , sgoals ↦
    M.ι[ M.Id-natural _ ] M.ι[ M.Id-cong' (M.app-natural _ _ _) (M.app-natural _ _ _) ]
    M.cong' _ (M.ι[ M.Id-cong (dra-natural ⟦ μ ⟧mod _) (dra-intro-natural ⟦ μ ⟧mod _ _) (dra-intro-natural ⟦ μ ⟧mod _ _) ]
              M.id-dra-intro-cong ⟦ μ ⟧mod (M.ι⁻¹[ M.Id-natural _ ] ⟦p⟧ sgoals)) ⟆
check-proof Ξ (hole name) φ = return ⟅ [ goal name Ξ φ ] , (sgl , _) ↦ sgl ⟆
check-proof Ξ (ext c tmargs bpargs pfargs) φ = check-proof-ext Ξ φ pfargs (pf-code-check c Ξ φ tmargs bpargs)

check-proof-explicit-constraint Ξ Ag.refl pf φ = check-proof Ξ pf φ

check-proof-ext {infos = []}    Ξ φ _                f = f
check-proof-ext {infos = _ ∷ _} Ξ φ (pfarg , pfargs) f =
  check-proof-ext Ξ φ pfargs (f (λ Ξ' ψ e → check-proof-explicit-constraint Ξ' e pfarg ψ))
