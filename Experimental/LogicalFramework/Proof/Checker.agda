open import Experimental.LogicalFramework.Parameter

module Experimental.LogicalFramework.Proof.Checker
  (ℬ : BiSikkelParameter)
  where

open import Data.List
import Data.String as Str
open import Data.Product
import Relation.Binary.PropositionalEquality as Ag

open BiSikkelParameter ℬ
open import Experimental.LogicalFramework.Parameter.ProofExtension 𝒫 𝒷 ⟦𝒷⟧
open ProofExt 𝓅
open import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯

open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.bProp 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Proof.Definition ℬ
open import Experimental.LogicalFramework.Proof.CheckingMonad
open import Experimental.LogicalFramework.Proof.Equality 𝒫 𝒷
open import Experimental.LogicalFramework.Proof.Context 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Postulates 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Proof.Checker.ResultType 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Proof.Checker.SyntaxViews 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Proof.Checker.Soundness 𝒫 𝒷 ⟦𝒷⟧

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
import Model.Type.Constant as M

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  Γ Δ : Ctx m
  T S R U : Ty m
  φ ψ : bProp Γ
  x y : Name
  Ξ : ProofCtx m



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
  return ⟅ [] , _ ↦ refl-sound Ξ t1 ⟆
check-proof Ξ (sym p) φ = do
  is-eq t1 t2 ← is-eq? φ
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof Ξ p (t2 ≡ᵇ t1)
  return ⟅ goals , sgoals ↦ sym-sound Ξ t2 t1 (⟦p⟧ sgoals) ⟆
check-proof Ξ (trans {T = T'} middle-tm p1 p2) φ = do
  is-eq {T = T} t s ← is-eq? φ
  refl ← T ≟ty T'
  ⟅ goals1 , ⟦p1⟧ ⟆ ← check-proof Ξ p1 (t ≡ᵇ middle-tm)
  ⟅ goals2 , ⟦p2⟧ ⟆ ← check-proof Ξ p2 (middle-tm ≡ᵇ s)
  return ⟅ goals1 ++ goals2
         , sgoals ↦ (let sgoals1 , sgoals2 = split-sem-goals goals1 goals2 sgoals
                      in trans-sound Ξ t middle-tm s (⟦p1⟧ sgoals1) (⟦p2⟧ sgoals2))
         ⟆
check-proof Ξ (subst {μ = μ} {x = x} {T = T} φ t1 t2 pe p1) ψ = do
  ⟅ goalse , ⟦pe⟧ ⟆ ← check-proof (Ξ ,lock⟨ μ ⟩) pe (t1 ≡ᵇ t2)
  ⟅ goals1 , ⟦p1⟧ ⟆ ← check-proof Ξ p1 (φ [ t1 / x ]bpropˢ)
  refl ← ψ ≟bprop φ [ t2 / x ]bpropˢ
  return ⟅ goalse ++ goals1 , sgoals ↦
    (let sgoalse , sgoals1 = split-sem-goals goalse goals1 sgoals in
    subst-sound Ξ t1 t2 φ (⟦pe⟧ sgoalse) (⟦p1⟧ sgoals1)) ⟆
check-proof Ξ ⊤ᵇ-intro φ = do
  refl ← φ ≟bprop ⊤ᵇ
  return ⟅ [] , _ ↦ M.tt' M.[ _ ]' ⟆
check-proof Ξ (⊥ᵇ-elim p) φ = do
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof Ξ p ⊥ᵇ
  return ⟅ goals , sgoals ↦ ⊥ᵇ-elim-sound Ξ φ (⟦p⟧ sgoals) ⟆
check-proof Ξ (⊃-intro x p) φ = do
  is-implication μ domφ codφ ← is-implication? φ
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof (Ξ ,,ᵇ μ ∣ x ∈ domφ) p codφ
  return ⟅ goals , sgoals ↦ ⊃-intro-sound Ξ domφ codφ x (⟦p⟧ sgoals) ⟆
check-proof Ξ (⊃-elim μ φ p1 p2) ψ = do
  ⟅ goals1 , ⟦p1⟧ ⟆ ← check-proof Ξ p1 (⟨ μ ∣ φ ⟩⊃ ψ)
  ⟅ goals2 , ⟦p2⟧ ⟆ ← check-proof (Ξ ,lock⟨ μ ⟩) p2 φ
  return ⟅ goals1 ++ goals2 , sgoals ↦
    (let sgoals1 , sgoals2 = split-sem-goals goals1 goals2 sgoals in
    ⊃-elim-sound Ξ φ ψ (⟦p1⟧ sgoals1) (⟦p2⟧ sgoals2)) ⟆
check-proof Ξ (∧-intro p1 p2) φ = do
  is-conjunction φ1 φ2 ← is-conjunction? φ
  ⟅ goals1 , ⟦p1⟧ ⟆ ← check-proof Ξ p1 φ1
  ⟅ goals2 , ⟦p2⟧ ⟆ ← check-proof Ξ p2 φ2
  return ⟅ goals1 ++ goals2 , sgoals ↦ (let sgoals1 , sgoals2 = split-sem-goals goals1 goals2 sgoals in
    ∧-intro-sound Ξ φ1 φ2 (⟦p1⟧ sgoals1) (⟦p2⟧ sgoals2)) ⟆
check-proof Ξ (∧-elimˡ ψ p) φ = do
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof Ξ p (φ ∧ ψ)
  return ⟅ goals , sgoals ↦ ∧-elimˡ-sound Ξ φ ψ (⟦p⟧ sgoals) ⟆
check-proof Ξ (∧-elimʳ ψ p) φ = do
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof Ξ p (ψ ∧ φ)
  return ⟅ goals , sgoals ↦ ∧-elimʳ-sound Ξ ψ φ (⟦p⟧ sgoals) ⟆
check-proof Ξ (mod⟨ μ ⟩ p) φ = do
  is-modal κ ψ ← is-modal? φ
  refl ← mod-dom μ ≟mode mod-dom κ
  refl ← μ ≟mod κ
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof (Ξ ,lock⟨ μ ⟩) p ψ
  return ⟅ goals , sgoals ↦ mod-intro-sound Ξ ψ (⟦p⟧ sgoals) ⟆
check-proof Ξ (mod-elim ρ μ x φ p1 p2) ψ = do
  ⟅ goals1 , ⟦p1⟧ ⟆ ← check-proof (Ξ ,lock⟨ ρ ⟩) p1 ⟨ μ ∣ φ ⟩
  ⟅ goals2 , ⟦p2⟧ ⟆ ← check-proof (Ξ ,,ᵇ ρ ⓜ μ ∣ x ∈ fuselocks-bprop φ) p2 ψ
  return ⟅ goals1 ++ goals2 , sgoals ↦ (let sgoals1 , sgoals2 = split-sem-goals goals1 goals2 sgoals in
    mod-elim-sound Ξ φ ψ x (⟦p1⟧ sgoals1) (⟦p2⟧ sgoals2)) ⟆
check-proof Ξ (assumption' {m = m} {n = n} x {μ = μ} {κ = κ} α) φ = do
  a ← contains-assumption? x Ξ ◇
  refl ← n ≟mode as-cod-mode a
  refl ← μ ≟mod as-mod a
  refl ← κ ≟mod locksˡᵗ (as-lt a)
  refl ← φ ≟bprop lookup-assumption a α
  return ⟅ [] , _ ↦ ⟦ a , α ⟧assumption ⟆
check-proof Ξ (∀-intro[_∣_∈_]_ {n = n} μ x T p) φ = do
  is-forall {n = n'} κ y S φ' ← is-forall? φ
  refl ← n ≟mode n'
  refl ← μ ≟mod κ
  refl ← from-dec "Alpha equivalence is currently not supported" (x Str.≟ y)
  refl ← T ≟ty S
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof (Ξ ,,ᵛ μ ∣ x ∈ T) p φ'
  return ⟅ goals , sgoals ↦ ∀-intro-sound Ξ x T φ' (⟦p⟧ sgoals) ⟆
check-proof Ξ (∀-elim {n = n} {T = T} μ ψ p t) φ = do
  is-forall {n = n'} κ y S ψ' ← is-forall? ψ
  refl ← n ≟mode n'
  refl ← μ ≟mod κ
  refl ← T ≟ty S
  refl ← φ ≟bprop (ψ' [ t / y ]bpropˢ)
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof Ξ p ψ
  return ⟅ goals , sgoals ↦ ∀-elim-sound Ξ y T ψ' (⟦p⟧ sgoals) t ⟆
check-proof Ξ fun-β φ = do
  is-eq lhs rhs ← is-eq? φ
  app f t ← is-app? lhs
  lam {T = A} {S = B} μ x b ← is-lam? f
  refl ← rhs ≟tm (b [ t / x ]tmˢ)
  return ⟅ [] , _ ↦ fun-β-sound Ξ b t ⟆
check-proof Ξ nat-rec-β-zero φ = do
  is-eq lhs rhs ← is-eq? φ
  nat-rec z s n ← is-nat-rec? lhs
  refl ← n ≟tm zero
  refl ← rhs ≟tm z
  return ⟅ [] , _ ↦ nat-rec-β-zero-sound Ξ z s ⟆
check-proof Ξ nat-rec-β-suc φ = do
  is-eq lhs rhs ← is-eq? φ
  nat-rec z s n ← is-nat-rec? lhs
  suc-tm n' ← is-suc-tm? n
  refl ← rhs ≟tm s ∙¹ (nat-rec z s n')
  return ⟅ [] , _ ↦ nat-rec-β-suc-sound Ξ z s n' ⟆
check-proof Ξ (fun-η x) φ = do
  is-eq {T = T} lhs rhs ← is-eq? φ
  is-fun-ty μ dom cod ← is-fun-ty? T
  refl ← rhs ≟tm (lam[ μ ∣ x ∈ dom ] (weaken-tm lhs ∙ v0))
  return ⟅ [] , _ ↦ fun-η-sound Ξ lhs ⟆
check-proof Ξ ⊠-η φ = do
  is-eq {T = P} lhs rhs ← is-eq? φ
  is-prod-ty T S ← is-prod-ty? P
  refl ← rhs ≟tm (pair (fst lhs) (snd lhs))
  return ⟅ [] , _ ↦ ⊠-η-sound Ξ lhs ⟆
check-proof Ξ true≠false φ = do
  refl ← φ ≟bprop ¬⟨ 𝟙 ⟩ (true ≡ᵇ false)
  return ⟅ [] , _ ↦ true≠false-sound Ξ ⟆
check-proof Ξ (suc-inj m n) φ = do
  refl ← φ ≟bprop (∀[ 𝟙 ∣ m ∈ Nat' ] (∀[ 𝟙 ∣ n ∈ Nat' ] ⟨ 𝟙 ∣ suc v1 ≡ᵇ suc v0 ⟩⊃ (v1-nolock ≡ᵇ v0-nolock)))
  return ⟅ [] , _ ↦ suc-inj-sound Ξ m n ⟆
check-proof Ξ (zero≠sucn m) φ = do
  refl ← φ ≟bprop (∀[ 𝟙 ∣ m ∈ Nat' ] ¬⟨ 𝟙 ⟩ (zero ≡ᵇ suc v0))
  return ⟅ [] , _ ↦ zero≠sucn-sound Ξ m ⟆
check-proof Ξ (bool-induction' Δ=Γ,x∈Bool pt pf) φ = do
  ends-in-prog-var Ξ' μ x T ← ends-in-prog-var? Ξ
  refl ← return Δ=Γ,x∈Bool
  ⟅ goalst , ⟦pt⟧ ⟆ ← check-proof Ξ' pt (φ [ true  / x ]bpropˢ)
  ⟅ goalsf , ⟦pf⟧ ⟆ ← check-proof Ξ' pf (φ [ false / x ]bpropˢ)
  return ⟅ goalst ++ goalsf , sgoals ↦ (let sgoalst , sgoalsf = split-sem-goals goalst goalsf sgoals in
    bool-induction-sound Ξ' φ (⟦pt⟧ sgoalst) (⟦pf⟧ sgoalsf)) ⟆
check-proof Ξ (nat-induction' hyp Δ=Γ,x∈Nat p0 ps) φ = do
  ends-in-prog-var Ξ' μ x T ← ends-in-prog-var? Ξ
  refl ← return Δ=Γ,x∈Nat
    -- ^ Before this step, ps is a proof in Δ = to-ctx Ξ' ,,ᵛ μ ∣ x ∈ T and p0 is a proof in Γ.
    -- By pattern matching on Δ=Γ,x∈Nat : Δ ≡ Γ ,, x ∈ Nat', Γ gets unified with to-ctx Ξ', μ with 𝟙 and T with Nat'.
    -- Pattern matching on this proof only works since we already established that Ξ is of the form Ξ' ,,ᵛ μ ∣ x ∈ T.
    -- Otherwise, unification would fail.
  ⟅ goals1 , ⟦p0⟧ ⟆ ← check-proof Ξ' p0 (φ [ zero / x ]bpropˢ)
  ⟅ goals2 , ⟦ps⟧ ⟆ ← check-proof (Ξ' ,,ᵛ 𝟙 ∣ x ∈ Nat' ,,ᵇ 𝟙 ∣ hyp ∈ lock𝟙-bprop φ)
                                  ps
                                  (φ [ suc v0 // x ]bpropˢ)
  return ⟅ goals1 ++ goals2 , sgoals ↦
    (let sgoals1 , sgoals2 = split-sem-goals goals1 goals2 sgoals
     in nat-induction-sound Ξ' φ hyp (⟦p0⟧ sgoals1) (⟦ps⟧ sgoals2)) ⟆
check-proof Ξ (mod-induction' {T = T} κ μ x ctx-eq p) φ = do
  ends-in-prog-var Ξ' μ' y _ ← ends-in-prog-var? Ξ
  refl ← return ctx-eq
  ⟅ goals , ⟦p⟧ ⟆ ← check-proof (Ξ' ,,ᵛ μ ⓜ κ ∣ x ∈ T) p (φ [ mod⟨ κ ⟩ (var' x {vlock (vlock (vzero id-cell))}) // y ]bpropˢ)
  return ⟅ goals , sgoals ↦ mod-induction-sound Ξ' μ κ φ (⟦p⟧ sgoals) ⟆
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
  return ⟅ goals , sgoals ↦ fun-cong-sound Ξ f g t (⟦p⟧ sgoals) ⟆
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
  return ⟅ goals , sgoals ↦ cong-sound Ξ f t s (⟦p⟧ sgoals) ⟆
check-proof Ξ (hole name) φ = return ⟅ [ goal name Ξ φ ] , (sgl , _) ↦ sgl ⟆
check-proof Ξ (ext c tmargs bpargs pfargs) φ = check-proof-ext Ξ φ pfargs (pf-code-check c Ξ φ tmargs bpargs)

check-proof-explicit-constraint Ξ Ag.refl pf φ = check-proof Ξ pf φ

check-proof-ext {infos = []}    Ξ φ _                f = f
check-proof-ext {infos = _ ∷ _} Ξ φ (pfarg , pfargs) f =
  check-proof-ext Ξ φ pfargs (f (λ Ξ' ψ e → check-proof-explicit-constraint Ξ' e pfarg ψ))
