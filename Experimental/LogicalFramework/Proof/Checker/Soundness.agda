open import Experimental.LogicalFramework.Parameter

module Experimental.LogicalFramework.Proof.Checker.Soundness
  (ℬ : BiSikkelParameter)
  where

open import Data.String

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.DRA as DRA hiding (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; TwoCell; id-cell)
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.IdentityType.Modal as M
import Experimental.DependentTypes.Model.Constant as M
import Experimental.DependentTypes.Model.Function as M renaming (lam to dlam)
import Model.Type.Constant as M
import Model.Type.Function as M
import Model.Type.Product as M

open BiSikkelParameter ℬ
-- open import Experimental.LogicalFramework.Parameter.ProofExtension 𝒫 𝒷 ⟦𝒷⟧
-- open ProofExt 𝓅
-- open import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯 String

open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.bProp 𝒫 𝒷 ⟦𝒷⟧
-- open import Experimental.LogicalFramework.Proof.Definition ℬ
-- open import Experimental.LogicalFramework.Proof.CheckingMonad
-- open import Experimental.LogicalFramework.Proof.Equality 𝒫 𝒷
open import Experimental.LogicalFramework.Proof.Context 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Postulates 𝒫 𝒷 ⟦𝒷⟧
-- open import Experimental.LogicalFramework.Proof.Checker.ResultType 𝒫 𝒷 ⟦𝒷⟧
-- open import Experimental.LogicalFramework.Proof.Checker.SyntaxViews 𝒫 𝒷 ⟦𝒷⟧

private variable
  m n o : Mode
  μ ρ : Modality m n
  x y : String
  T S : Ty m


-- A useful lemma
to-ctx-/-commute : (Ξ : ProofCtx m) (φ : bProp (to-ctx (Ξ ,,ᵛ μ ∣ x ∈ T))) (t : Tm (to-ctx (Ξ ,lock⟨ μ ⟩)) T) →
                   ⟦ φ [ t / x ]bprop ⟧bprop M.[ to-ctx-subst Ξ ]
                     M.≅ᵗʸ
                   (⟦ φ ⟧bprop M.[ to-ctx-subst (Ξ ,,ᵛ μ ∣ x ∈ T) ]) M.[
                    dra-intro ⟦ μ ⟧mod (⟦ t ⟧tm M.[ ty-closed-natural T ∣ to-ctx-subst (Ξ ,lock⟨ μ ⟩) ]cl) M./cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ ]
to-ctx-/-commute {μ = μ} {x} {T} Ξ φ t =
  M.transᵗʸ (M.symᵗʸ (M.ty-subst-cong-ty _ (M.transᵗʸ (M.ty-subst-cong-subst (M.symˢ (/cl-sound t x)) ⟦ φ ⟧bprop) (bprop-sub-sound φ (t / x))))) (
  M.transᵗʸ (M.ty-subst-cong-subst-2-2 _ (M./cl-⊚ (ty-closed-natural ⟨ μ ∣ T ⟩) _ _)) (
  M.ty-subst-cong-subst (M.,cl-cong-tm (ty-closed-natural ⟨ μ ∣ T ⟩) (dra-intro-cl-natural ⟦ μ ⟧mod (ty-closed-natural T) ⟦ t ⟧tm)) _))

-- Specialisation of the previous lemma to the case μ = 𝟙
to-ctx-/-commute-𝟙 : (Ξ : ProofCtx m) (φ : bProp (to-ctx (Ξ ,,ᵛ 𝟙 ∣ x ∈ T))) (t : Tm (to-ctx Ξ ,lock⟨ 𝟙 ⟩) T) →
                     ⟦ φ [ t / x ]bprop ⟧bprop M.[ to-ctx-subst Ξ ]
                       M.≅ᵗʸ
                     (⟦ φ ⟧bprop M.[ to-ctx-subst (Ξ ,,ᵛ 𝟙 ∣ x ∈ T) ]) M.[
                       (⟦ t ⟧tm M.[ ty-closed-natural T ∣ to-ctx-subst Ξ ]cl) M./cl⟨ ty-closed-natural T ⟩ ]
to-ctx-/-commute-𝟙 {T = T} Ξ φ t =
  M.transᵗʸ (to-ctx-/-commute Ξ φ t) (
  M.ty-subst-cong-subst (M./cl-cong-cl (𝟙-preserves-cl (ty-closed-natural T))) _)

-- Todo: the soundness proofs for nat-induction and mod-induction can
-- probably be simplified by using the following lemma
-- to-ctx-//-commute : (Ξ : ProofCtx m) (φ : bProp (to-ctx (Ξ ,,ᵛ ρ ∣ y ∈ S)))
--                     (s : Tm (to-ctx Ξ ,, μ ∣ x ∈ T ,lock⟨ ρ ⟩) S) →
--                     ⟦ φ [ s // y ]bprop ⟧bprop M.[ to-ctx-subst (Ξ ,,ᵛ μ ∣ x ∈ T) ]
--                       M.≅ᵗʸ
--                     (⟦ φ ⟧bprop M.[ to-ctx-subst (Ξ ,,ᵛ ρ ∣ y ∈ S) ])
--                       M.[ dra-intro ⟦ ρ ⟧mod (⟦ s ⟧tm M.[ ty-closed-natural S ∣ to-ctx-subst ((Ξ ,,ᵛ μ ∣ x ∈ T) ,lock⟨ ρ ⟩) ]cl)
--                           M.//cl⟨ ty-closed-natural ⟨ ρ ∣ S ⟩ ⟩ ]
-- to-ctx-//-commute Ξ φ s = {!!}

Evidence : (Ξ : ProofCtx m) (φ : bProp (to-ctx Ξ)) → Set
Evidence Ξ φ = SemTm ⟦ Ξ ⟧pctx (⟦ φ ⟧bprop M.[ to-ctx-subst Ξ ])

module _ (Ξ : ProofCtx m) where
  refl-sound : (t : Tm (to-ctx Ξ) T) → Evidence Ξ (t ≡ᵇ t)
  refl-sound t = (M.refl' ⟦ t ⟧tm) M.[ _ ]'

  sym-sound : (t1 t2 : Tm (to-ctx Ξ) T) →
              Evidence Ξ (t1 ≡ᵇ t2) →
              Evidence Ξ (t2 ≡ᵇ t1)
  sym-sound t1 t2 p = M.ι[ M.Id-natural _ ] M.sym' (M.ι⁻¹[ M.Id-natural _ ] p)

  trans-sound : (t1 t2 t3 : Tm (to-ctx Ξ) T) →
                Evidence Ξ (t1 ≡ᵇ t2) →
                Evidence Ξ (t2 ≡ᵇ t3) →
                Evidence Ξ (t1 ≡ᵇ t3)
  trans-sound t1 t2 t3 p12 p23 = M.ι[ M.Id-natural _ ] M.trans' (M.ι⁻¹[ M.Id-natural _ ] p12) (M.ι⁻¹[ M.Id-natural _ ] p23)

  subst-sound : (t1 t2 : Tm (to-ctx Ξ ,lock⟨ μ ⟩) T) (φ : bProp (to-ctx Ξ ,, μ ∣ x ∈ T)) →
                Evidence (Ξ ,lock⟨ μ ⟩) (t1 ≡ᵇ t2) →
                Evidence Ξ (φ [ t1 / x ]bprop) →
                Evidence Ξ (φ [ t2 / x ]bprop)
  subst-sound {μ = μ} {T} t1 t2 φ pe p1 =
    M.ι[ to-ctx-/-commute Ξ φ t2 ]
      M.ι[ M.ty-subst-cong-subst (M./cl-cong (ty-closed-natural ⟨ μ ∣ T ⟩) (dra-intro-cong ⟦ μ ⟧mod (M.symᵗᵐ (
           M.eq-reflect (M.ι⁻¹[ M.Id-cl-natural (ty-closed-natural T) _ ] pe))))) _ ]
      M.ι⁻¹[ to-ctx-/-commute Ξ φ t1 ] p1

  ⊥ᵇ-elim-sound : (φ : bProp (to-ctx Ξ)) →
                  Evidence Ξ ⊥ᵇ →
                  Evidence Ξ φ
  ⊥ᵇ-elim-sound φ p = M.app (M.ι⁻¹[ M.⇛-natural _ ] (M.empty-elim _ M.[ _ ]')) p

  ⊃-intro-sound : (φ : bProp (to-ctx Ξ ,lock⟨ μ ⟩)) (ψ : bProp (to-ctx Ξ)) (x : String) →
                  Evidence (Ξ ,,ᵇ μ ∣ x ∈ φ) ψ →
                  Evidence Ξ (⟨ μ ∣ φ ⟩⊃ ψ)
  ⊃-intro-sound φ ψ x p = M.ι[ M.⇛-natural _ ] M.lam _ (M.ι[ M.ty-subst-comp _ _ _ ] p)

  ⊃-elim-sound : (φ : bProp (to-ctx Ξ ,lock⟨ μ ⟩)) (ψ : bProp (to-ctx Ξ)) →
                 Evidence Ξ (⟨ μ ∣ φ ⟩⊃ ψ) →
                 Evidence (Ξ ,lock⟨ μ ⟩) φ →
                 Evidence Ξ ψ
  ⊃-elim-sound {μ = μ} φ ψ p1 p2 = M.app (M.ι⁻¹[ M.⇛-natural _ ] p1) (M.ι[ dra-natural ⟦ μ ⟧mod _ ] dra-intro ⟦ μ ⟧mod p2)

  ∧-intro-sound : (φ ψ : bProp (to-ctx Ξ)) →
                  Evidence Ξ φ →
                  Evidence Ξ ψ →
                  Evidence Ξ (φ ∧ ψ)
  ∧-intro-sound φ ψ p1 p2 = M.ι[ M.⊠-natural _ ] M.pair p1 p2

  ∧-elimˡ-sound : (φ ψ : bProp (to-ctx Ξ)) →
                  Evidence Ξ (φ ∧ ψ) →
                  Evidence Ξ φ
  ∧-elimˡ-sound φ ψ p = M.fst (M.ι⁻¹[ M.⊠-natural _ ] p)

  ∧-elimʳ-sound : (φ ψ : bProp (to-ctx Ξ)) →
                  Evidence Ξ (φ ∧ ψ) →
                  Evidence Ξ ψ
  ∧-elimʳ-sound φ ψ p = M.snd (M.ι⁻¹[ M.⊠-natural _ ] p)

  mod-intro-sound : (φ : bProp (to-ctx Ξ ,lock⟨ μ ⟩)) →
                    Evidence (Ξ ,lock⟨ μ ⟩) φ →
                    Evidence Ξ ⟨ μ ∣ φ ⟩
  mod-intro-sound {μ = μ} φ p = M.ι[ dra-natural ⟦ μ ⟧mod _ ] dra-intro ⟦ μ ⟧mod p

  mod-elim-sound : (φ : bProp (to-ctx Ξ ,lock⟨ ρ ⟩ ,lock⟨ μ ⟩))
                   (ψ : bProp (to-ctx Ξ))
                   (x : String) →
                   Evidence (Ξ ,lock⟨ ρ ⟩) ⟨ μ ∣ φ ⟩ →
                   Evidence (Ξ ,,ᵇ ρ ⓜ μ ∣ x ∈ fuselocks-bprop φ) ψ →
                   Evidence Ξ ψ
  mod-elim-sound {ρ = ρ} {μ = μ} φ ψ x p1 p2 =
    M.ι⁻¹[ M.ty-subst-cong-subst-2-1 _ (M.transˢ M.⊚-assoc (M.transˢ (M.⊚-congʳ (M.ctx-ext-subst-β₁ _ _)) (M.id-subst-unitʳ _))) ] (
      p2
      M.[ (M.ι[ M.ty-subst-cong-ty _ (M.transᵗʸ (eq-dra-tyʳ (⟦ⓜ⟧-sound ρ μ) _) (dra-cong ⟦ ρ ⟧mod (dra-cong ⟦ μ ⟧mod (fuselocks-bprop-sound φ)))) ]
          (M.ι[ dra-natural ⟦ ρ ⟧mod _ ]
          dra-intro ⟦ ρ ⟧mod p1))
        M./v ]')

  ∀-intro-sound : (x : String) (T : Ty n) (φ : bProp (to-ctx Ξ ,, μ ∣ x ∈ T)) →
                  Evidence (Ξ ,,ᵛ μ ∣ x ∈ T) φ →
                  Evidence Ξ (∀[ μ ∣ x ∈ T ] φ)
  ∀-intro-sound {μ = μ} x T φ p = M.ι[ M.Pi-natural-closed-dom (ty-closed-natural ⟨ μ ∣ T ⟩) _ ]
                                    M.dlam ⟦ ⟨ μ ∣ T ⟩ ⟧ty p

  ∀-elim-sound : (x : String) (T : Ty n) (φ : bProp (to-ctx Ξ ,, μ ∣ x ∈ T)) →
                 Evidence Ξ (∀[ μ ∣ x ∈ T ] φ) →
                 (t : Tm (to-ctx Ξ ,lock⟨ μ ⟩) T) →
                 Evidence Ξ (φ [ t / x ]bprop)
  ∀-elim-sound {μ = μ} x T φ p t =
    M.ι[ to-ctx-/-commute Ξ φ t ]
      (M.cl-app (ty-closed-natural ⟨ μ ∣ T ⟩) (M.ι⁻¹[ M.Pi-natural-closed-dom (ty-closed-natural ⟨ μ ∣ T ⟩) _ ] p)
                                              (dra-intro ⟦ μ ⟧mod (⟦ t ⟧tm M.[ ty-closed-natural T ∣ DRA.lock-fmap ⟦ μ ⟧mod (to-ctx-subst Ξ) ]cl)))

  fun-β-sound : (b : Tm (to-ctx Ξ ,, μ ∣ x ∈ T) S) (t : Tm (to-ctx Ξ ,lock⟨ μ ⟩) T) →
                Evidence Ξ ((lam[ μ ∣ x ∈ T ] b) ∙ t ≡ᵇ b [ t / x ]tm)
  fun-β-sound {μ = μ} {x = x} {T = T} {S = S} b t =
    M.≅ᵗᵐ-to-Id (
      M.transᵗᵐ (M.⇛-cl-β (ty-closed-natural ⟨ μ ∣ T ⟩) (ty-closed-natural S) _ _) (
      M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural S) (M.symˢ (/cl-sound t x))) (
      tm-sub-sound b (t / x))))
    M.[ _ ]'

  nat-rec-β-zero-sound : (z : Tm (to-ctx Ξ) T) (s : Tm (to-ctx Ξ) (T ⇛ T)) →
                         Evidence Ξ (nat-rec z s zero ≡ᵇ z)
  nat-rec-β-zero-sound z s = (M.≅ᵗᵐ-to-Id (M.β-nat-zero _ _)) M.[ _ ]'

  nat-rec-β-suc-sound : (z : Tm (to-ctx Ξ) T) (s : Tm (to-ctx Ξ) (T ⇛ T)) (n : Tm (to-ctx Ξ) Nat') →
                        Evidence Ξ (nat-rec z s (suc n) ≡ᵇ s ∙¹ nat-rec z s n)
  nat-rec-β-suc-sound z s n = M.≅ᵗᵐ-to-Id (M.transᵗᵐ (M.β-nat-suc _ _ _) (M.symᵗᵐ (∙¹-sound s (nat-rec z s n)))) M.[ _ ]'

  fun-η-sound : (f : Tm (to-ctx Ξ) (⟨ μ ∣ T ⟩⇛ S)) →
                Evidence Ξ (f ≡ᵇ lam[ μ ∣ x ∈ T ] (weaken-tm f ∙ v0))
  fun-η-sound {μ = μ} {T = T} {S = S} {x = x} f =
    M.≅ᵗᵐ-to-Id (M.transᵗᵐ
      (M.⇛-cl-η (ty-closed-natural ⟨ μ ∣ T ⟩) (ty-closed-natural S) _)
      (M.lamcl-cong (ty-closed-natural S) (M.app-cong (M.symᵗᵐ (weaken-tm-sound (to-ctx Ξ) x μ T f))
                                                      (M.symᵗᵐ (M.transᵗᵐ (dra-intro-cong ⟦ μ ⟧mod (v0-sound (to-ctx Ξ) μ x T))
                                                                          (dra-η ⟦ μ ⟧mod _))))))
    M.[ _ ]'

  ⊠-η-sound : (p : Tm (to-ctx Ξ) (T ⊠ S)) →
              Evidence Ξ (p ≡ᵇ pair (fst p) (snd p))
  ⊠-η-sound p = M.≅ᵗᵐ-to-Id (M.η-⊠ ⟦ p ⟧tm) M.[ _ ]'

  true≠false-sound : Evidence Ξ (¬ (true ≡ᵇ false))
  true≠false-sound = M.true≠false M.[ _ ]'

  suc-inj-sound : (m n : String) →
                  Evidence Ξ (∀[ 𝟙 ∣ m ∈ Nat' ] ∀[ 𝟙 ∣ n ∈ Nat' ] ⟨ 𝟙 ∣ suc v1 ≡ᵇ suc v0 ⟩⊃ (v1-𝟙 ≡ᵇ v0-𝟙))
  suc-inj-sound m n =
    (M.ι[ M.Pi-cong-cod (M.Pi-cong-cod (
      M.⇛-cong (M.Id-cong' (M.suc'-cong (v1-sound-𝟙 (to-ctx Ξ) m Nat' 𝟙 n Nat')) (M.suc'-cong (v0-sound-𝟙 (to-ctx Ξ ,, 𝟙 ∣ m ∈ Nat') n Nat')))
               (M.Id-cong' (v1-𝟙-sound (to-ctx Ξ) m Nat' 𝟙 n Nat') (v0-𝟙-sound (to-ctx Ξ ,, 𝟙 ∣ m ∈ Nat') n Nat')))) ]
      M.suc-inj)
    M.[ _ ]'

  zero≠sucn-sound : (n : String) →
                    Evidence Ξ (∀[ 𝟙 ∣ n ∈ Nat' ] ¬⟨ 𝟙 ⟩ (zero ≡ᵇ suc v0))
  zero≠sucn-sound n =
    (M.ι[ M.Pi-cong-cod (M.⇛-cong (M.Id-cong' M.reflᵗᵐ (M.suc'-cong (v0-sound-𝟙 (to-ctx Ξ) n Nat')))
                                  M.reflᵗʸ) ]
    M.zero≠sucn) M.[ _ ]'

  bool-induction-sound : (φ : bProp (to-ctx Ξ ,, 𝟙 ∣ x ∈ Bool')) →
                         Evidence Ξ (φ [ true  / x ]bprop) →
                         Evidence Ξ (φ [ false / x ]bprop) →
                         Evidence (Ξ ,,ᵛ 𝟙 ∣ x ∈ Bool') φ
  bool-induction-sound φ pt pf =
    M.bool-ind _
               (M.ι⁻¹[ M.ty-subst-cong-subst (M./cl-cong M.const-closed (M.const-cl-natural (to-ctx-subst Ξ))) _ ] (
                 M.ι⁻¹[ to-ctx-/-commute-𝟙 Ξ φ true ] pt))
               (M.ι⁻¹[ M.ty-subst-cong-subst (M./cl-cong M.const-closed (M.const-cl-natural (to-ctx-subst Ξ))) _ ] (
                 M.ι⁻¹[ to-ctx-/-commute-𝟙 Ξ φ false ] pf))

  nat-induction-sound : (φ : bProp (to-ctx Ξ ,, 𝟙 ∣ x ∈ Nat')) (y : String) →
                        Evidence Ξ (φ [ zero / x ]bprop) →
                        Evidence (Ξ ,,ᵛ 𝟙 ∣ x ∈ Nat' ,,ᵇ 𝟙 ∣ y ∈ lock𝟙-bprop φ) (φ [ suc v0 // x ]bprop) →
                        Evidence (Ξ ,,ᵛ 𝟙 ∣ x ∈ Nat') φ
  nat-induction-sound {x = x} φ y p0 ps =
    M.nat-ind _ (M.ι⁻¹[ M.ty-subst-cong-subst (M./cl-cong M.const-closed (M.const-cl-natural (to-ctx-subst Ξ))) _ ]
                  (M.ι⁻¹[ to-ctx-/-commute-𝟙 Ξ φ zero ] p0))
                (M.ι⁻¹[ M.ty-subst-cong-subst-2-1 _ (M.transˢ M.⊚-assoc (M.⊚-congʳ (M.,,-map-π _))) ]
                  (M.ιc⁻¹[ M.,,-cong (M.ty-subst-cong-ty _ (lock𝟙-bprop-sound φ)) ]'
                  (M.ι⁻¹[ M.ty-subst-cong-subst (M.⊚-congˡ (
                          M.transˢ (M.,cl-cong-cl (𝟙-preserves-cl M.const-closed))
                                   (M.,cl-cong-tm M.const-closed (M.transᵗᵐ (M.cl-tm-subst-cong-cl (𝟙-preserves-cl M.const-closed))
                                                                 (M.transᵗᵐ (M.suc'-cl-natural _)
                                                                 (M.transᵗᵐ (M.const-map-cong _ (M.symᵗᵐ (M.cl-tm-subst-cong-cl (𝟙-preserves-cl M.const-closed))))
                                                                 (M.const-map-cong _ (M.transᵗᵐ (M.lift-cl-ξcl (ty-closed-natural ⟨ 𝟙 ∣ Nat' ⟩) {σ = to-ctx-subst Ξ})
                                                                                                (M.ξcl-cong-cl (𝟙-preserves-cl M.const-closed)))))))))) _ ]
                  (M.ι[ M.ty-subst-cong-subst-2-2 _ (M.transˢ (M.symˢ M.⊚-assoc)
                                                    (M.transˢ (M.⊚-congˡ (M.lift-cl-,cl (ty-closed-natural ⟨ 𝟙 ∣ Nat' ⟩) (ty-closed-natural ⟨ 𝟙 ∣ Nat' ⟩) _ _))
                                                    M.⊚-assoc)) ]
                  (M.ι[ M.ty-subst-cong-ty _ (
                          M.transᵗʸ (M.ty-subst-cong-subst (M.symˢ
                                      (M.transˢ (∷ˢ-sound {Δ = to-ctx Ξ} π (suc (v0 {μ = 𝟙} {x = x})) x)
                                                (M.,cl-cong (ty-closed-natural ⟨ 𝟙 ∣ Nat' ⟩)
                                                            (sub-π-sound (to-ctx Ξ) x 𝟙 Nat')
                                                            (M.const-map-cong _ (v0-sound (to-ctx Ξ) 𝟙 x Nat')))))
                                      _)
                                    (bprop-sub-sound φ _)) ]
                  ps)))))

  mod-induction-sound : (ρ : Modality n m) (μ : Modality o n) (φ : bProp (to-ctx Ξ ,, ρ ∣ x ∈ ⟨ μ ∣ T ⟩)) →
                        Evidence (Ξ ,,ᵛ ρ ⓜ μ ∣ y ∈ T) (φ [ mod⟨ μ ⟩ (var' y {skip-lock μ (skip-lock ρ vzero)} id-cell) // x ]bprop) →
                        Evidence (Ξ ,,ᵛ ρ ∣ x ∈ ⟨ μ ∣ T ⟩) φ
  mod-induction-sound {x = x} {T = T} {y = y} ρ μ φ p =
    M.ι⁻¹[ M.transᵗʸ (M.ty-subst-cong-subst-2-2 _ (M.symˢ (M.lift-cl-,,-cong-commute (M.symᶜᵗʸ (eq-dra-closed (⟦ⓜ⟧-sound ρ μ) (ty-closed-natural T))) (to-ctx-subst Ξ)))) (
           M.transᵗʸ (M.ty-subst-cong-subst (M.lift-cl-subst-cong-cl (ⓓ-preserves-cl ⟦ ρ ⟧mod ⟦ μ ⟧mod (ty-closed-natural T))) _) (
           M.ty-subst-cong-ty _ (M.ty-subst-cong-subst-2-0 ⟦ φ ⟧bprop (
             M.transˢ (M.,cl-⊚ (ty-closed-natural ⟨ ρ ∣ ⟨ μ ∣ T ⟩ ⟩) _ _ _) (
             M.transˢ (M.,cl-cong (ty-closed-natural ⟨ ρ ∣ ⟨ μ ∣ T ⟩ ⟩) (M.transˢ (M.,,-map-π _) (M.symˢ (M.id-subst-unitʳ M.π))) (
               M.transᵗᵐ (M.cl-tm-subst-cong-tm (ty-closed-natural ⟨ ρ ∣ ⟨ μ ∣ T ⟩ ⟩) (M.transᵗᵐ (dra-intro-cong ⟦ ρ ⟧mod (dra-η ⟦ μ ⟧mod _)) (dra-η ⟦ ρ ⟧mod _))) (
               M.transᵗᵐ (M.cl-tm-subst-cong-tm (ty-closed-natural ⟨ ρ ∣ ⟨ μ ∣ T ⟩ ⟩) (M.symᵗᵐ (M.ξcl-,,-cong (eq-dra-closed (⟦ⓜ⟧-sound ρ μ) (ty-closed-natural T))))) (
               M.transᵗᵐ (M.cl-tm-subst-cong-tm (ty-closed-natural ⟨ ρ ∣ ⟨ μ ∣ T ⟩ ⟩) (
                 M.transᵗᵐ (M.cl-tm-subst-cong-cl (ⓓ-preserves-cl ⟦ ρ ⟧mod ⟦ μ ⟧mod (ty-closed-natural T)))
                           (M.cl-tm-subst-cong-tm (ty-closed-natural ⟨ ρ ∣ ⟨ μ ∣ T ⟩ ⟩) (M.ξcl-cong-cl (ⓓ-preserves-cl ⟦ ρ ⟧mod ⟦ μ ⟧mod (ty-closed-natural T))))))
                         (M.cl-tm-subst-cong-subst-2-1 (ty-closed-natural ⟨ ρ ∣ ⟨ μ ∣ T ⟩ ⟩)
                                                       {Δ' = ⟦ to-ctx Ξ ⟧ctx M.,, DRA.⟨ ⟦ ρ ⟧mod ∣ DRA.⟨ ⟦ μ ⟧mod ∣ ⟦ T ⟧ty ⟩ ⟩}
                                                       (M.isoʳ (M.,,-cong (eq-dra-ty-closed (⟦ⓜ⟧-sound ρ μ) (ty-closed-natural T))))))))) (
             M.symˢ (M.,cl-η (ty-closed-natural ⟨ ρ ∣ ⟨ μ ∣ T ⟩ ⟩) _))))))) ]
    M.ι[ M.ty-subst-cong-ty _ (M.ty-subst-cong-ty _ (
         M.transᵗʸ (M.ty-subst-cong-subst (M.symˢ (
           M.transˢ (∷ˢ-sound (π {Γ = to-ctx Ξ} {T = T}) (mod⟨ μ ⟩ var' x {skip-lock μ (skip-lock ρ vzero)} id-cell) y)
                    (M.,cl-cong (ty-closed-natural ⟨ ρ ∣ ⟨ μ ∣ T ⟩ ⟩)
                                (sub-π-sound (to-ctx Ξ) y (ρ ⓜ μ) T)
                                (dra-intro-cong ⟦ ρ ⟧mod (dra-intro-cong ⟦ μ ⟧mod (v0-2lock-sound ρ μ x (to-ctx Ξ) T))))))
                    ⟦ φ ⟧bprop) (
         bprop-sub-sound φ _))) ] (
    M.ιc⁻¹[ M.,,-cong (DRA.eq-dra-ty-closed (⟦ⓜ⟧-sound ρ μ) (ty-closed-natural T)) ]'
    p)

  fun-cong-sound : (f g : Tm (to-ctx Ξ) (⟨ μ ∣ T ⟩⇛ S)) (t : Tm (to-ctx Ξ ,lock⟨ μ ⟩) T) →
                   Evidence Ξ (f ≡ᵇ g) →
                   Evidence Ξ (f ∙ t ≡ᵇ g ∙ t)
  fun-cong-sound f g t p =
    M.ι[ M.Id-natural _ ] M.ι[ M.Id-cong' (M.app-natural _ _ _) (M.app-natural _ _ _) ]
    M.fun-cong' (M.ι⁻¹[ M.Id-cong (M.⇛-natural _) (M.symᵗᵐ M.ι-symʳ) (M.symᵗᵐ M.ι-symʳ) ] (M.ι⁻¹[ M.Id-natural _ ] p))
                _

  cong-sound : (f : Tm (to-ctx Ξ) (⟨ μ ∣ T ⟩⇛ S)) (t t' : Tm (to-ctx Ξ ,lock⟨ μ ⟩) T) →
               Evidence (Ξ ,lock⟨ μ ⟩) (t ≡ᵇ t') →
               Evidence Ξ (f ∙ t ≡ᵇ f ∙ t')
  cong-sound {μ = μ} f t t' p =
    M.ι[ M.Id-natural _ ] M.ι[ M.Id-cong' (M.app-natural _ _ _) (M.app-natural _ _ _) ]
    M.cong' _ (M.ι[ M.Id-cong (dra-natural ⟦ μ ⟧mod _) (dra-intro-natural ⟦ μ ⟧mod _ _) (dra-intro-natural ⟦ μ ⟧mod _ _) ]
              M.id-dra-intro-cong ⟦ μ ⟧mod (M.ι⁻¹[ M.Id-natural _ ] p))
