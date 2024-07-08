open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics using (bPropExtSem)
open import Data.String

module Experimental.LogicalFramework.Proof.AlphaEquivalence
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉) (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷)
  where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)

open import Preliminaries -- we need uip for term extension equivalence

open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯
open TmExt 𝓉
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics ℳ 𝒯
open TmExtSem ⟦𝓉⟧
open import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯
open Experimental.LogicalFramework.Parameter.bPropExtensionSemantics ℳ 𝒯 𝓉 hiding (bPropExtSem)
open bPropExt 𝒷
open bPropExtSem ⟦𝒷⟧

open import Experimental.LogicalFramework.MSTT.Syntax ℳ 𝒯 𝓉
open import Experimental.LogicalFramework.MSTT.Interpretation ℳ 𝒯 𝓉 ⟦𝓉⟧
open import Experimental.LogicalFramework.MSTT.Soundness.Variable ℳ 𝒯 𝓉 ⟦𝓉⟧
open import Experimental.LogicalFramework.bProp.Syntax 𝒫 𝒷
open import Experimental.LogicalFramework.bProp.Interpretation 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Proof.CheckingMonad

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.DRA as DRA hiding (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; TwoCell; id-cell)
import Model.Type.Function as M
import Model.Type.Constant as M
import Model.Type.Product as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.Function as M

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  Γ Δ Γ1 Γ2 : Ctx m
  T S R U : Ty m
  φ ψ : bProp Γ
  x y : String


-- Testing for α-equivalence

data AlphaEquivCtx : (Γ Δ : Ctx m) → Set where
  ◇ : ∀ {m} → AlphaEquivCtx (◇ {m}) ◇
  _,,_∣_ : {Γ Δ : Ctx n} → AlphaEquivCtx Γ Δ → (μ : Modality m n) {x y : Name} (T : Ty m) →
           AlphaEquivCtx (Γ ,, μ ∣ x ∈ T) (Δ ,, μ ∣ y ∈ T)
  _,lock⟨_⟩ : {Γ Δ : Ctx n} → AlphaEquivCtx Γ Δ → (μ : Modality m n) →
              AlphaEquivCtx (Γ ,lock⟨ μ ⟩) (Δ ,lock⟨ μ ⟩)

alpha-equiv-sub : AlphaEquivCtx Γ Δ → (⟦ Δ ⟧ctx M.⇒ ⟦ Γ ⟧ctx)
alpha-equiv-sub ◇ = M.id-subst _
alpha-equiv-sub (e ,, μ ∣ T) = M.lift-cl-subst (ty-closed-natural ⟨ μ ∣ T ⟩) (alpha-equiv-sub e)
alpha-equiv-sub (e ,lock⟨ μ ⟩) = lock-fmap ⟦ μ ⟧mod (alpha-equiv-sub e)

alpha-equiv-ctx-refl : {Γ : Ctx m} → AlphaEquivCtx Γ Γ
alpha-equiv-ctx-refl {Γ = ◇} = ◇
alpha-equiv-ctx-refl {Γ = Γ ,, μ ∣ x ∈ T} = alpha-equiv-ctx-refl ,, μ ∣ T
alpha-equiv-ctx-refl {Γ = Γ ,lock⟨ μ ⟩} = alpha-equiv-ctx-refl ,lock⟨ μ ⟩

alpha-equiv-sub-refl : (Γ : Ctx m) → alpha-equiv-sub (alpha-equiv-ctx-refl {Γ = Γ}) M.≅ˢ M.id-subst _
alpha-equiv-sub-refl ◇ = M.reflˢ
alpha-equiv-sub-refl (Γ ,, μ ∣ x ∈ T) =
  M.transˢ (M.lift-cl-subst-cong (ty-closed-natural ⟨ μ ∣ T ⟩) (alpha-equiv-sub-refl Γ))
           (M.lift-cl-subst-id (ty-closed-natural ⟨ μ ∣ T ⟩))
alpha-equiv-sub-refl (Γ ,lock⟨ μ ⟩) =
  M.transˢ (lock-fmap-cong ⟦ μ ⟧mod (alpha-equiv-sub-refl Γ))
           (lock-fmap-id ⟦ μ ⟧mod)

alpha-equiv-nltel : {Γ Δ : Ctx m} → AlphaEquivCtx Γ Δ →
                    (Θ : NamelessTele m n) {names1 names2 : Names Θ} →
                    AlphaEquivCtx (Γ ++tel add-names Θ names1) (Δ ++tel add-names Θ names2)
alpha-equiv-nltel eΓ ◇ = eΓ
alpha-equiv-nltel eΓ (Θ ,, μ ∣ T) = (alpha-equiv-nltel eΓ Θ) ,, μ ∣ T
alpha-equiv-nltel eΓ (Θ ,lock⟨ μ ⟩) = (alpha-equiv-nltel eΓ Θ) ,lock⟨ μ ⟩

alpha-equiv-nltel-sub : {Γ Δ : Ctx m} (eΓ : AlphaEquivCtx Γ Δ)
                        (Θ : NamelessTele m n) {names1 names2 : Names Θ} →
                        M.to (++tel-++⟦⟧nltel Γ Θ names1) M.⊚ apply-nltel-sub (alpha-equiv-sub eΓ) Θ
                          M.≅ˢ
                        alpha-equiv-sub (alpha-equiv-nltel eΓ Θ) M.⊚ M.to (++tel-++⟦⟧nltel Δ Θ names2)
alpha-equiv-nltel-sub eΓ ◇ = M.transˢ (M.id-subst-unitˡ _) (M.symˢ (M.id-subst-unitʳ _))
alpha-equiv-nltel-sub eΓ (Θ ,, μ ∣ T) = M.ctx-fmap-cong-2-2 (M.,,-functor (ty-closed-natural ⟨ μ ∣ T ⟩)) (alpha-equiv-nltel-sub eΓ Θ)
alpha-equiv-nltel-sub eΓ (Θ ,lock⟨ μ ⟩) = M.ctx-fmap-cong-2-2 (ctx-functor ⟦ μ ⟧mod) (alpha-equiv-nltel-sub eΓ Θ)


var-α-equiv : {Λ : LockTele m n} (v1 : Var x T Γ1 Λ) (v2 : Var y T Γ2 Λ) →
              (eΓ : AlphaEquivCtx Γ1 Γ2) →
              PCM (⟦ v1 ⟧var M.[ ty-closed-natural T ∣ lock-fmap ⟦ locksˡᵗ Λ ⟧mod (alpha-equiv-sub eΓ) ]cl M.≅ᵗᵐ ⟦ v2 ⟧var)
var-α-equiv {x = x} {y = y} {Λ = Λ} (vzero {Γ = Γ1} α1) (vzero {Γ = Γ2} α2) (eΓ ,, μ ∣ T) = do
  refl ← α1 ≟cell α2
  return (vzero-sem-lift-sub Γ2 Γ1 μ x y T Λ α1 (alpha-equiv-sub eΓ))
var-α-equiv {T = T} {Λ = Λ} (vsuc v1)  (vsuc v2)  (eΓ ,, ρ ∣ S) = do
  ev ← var-α-equiv v1 v2 eΓ
  return (M.transᵗᵐ (M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural T) (lock-fmap-cong-2-2 ⟦ locksˡᵗ Λ ⟧mod (M.lift-cl-subst-π-commute (ty-closed-natural ⟨ ρ ∣ S ⟩))))
                    (M.cl-tm-subst-cong-tm (ty-closed-natural T) ev))
var-α-equiv {T = T} {Λ = Λ} (vlock v1) (vlock v2) (eΓ ,lock⟨ ρ ⟩) = do
  ev ← var-α-equiv v1 v2 eΓ
  return (M.transᵗᵐ (M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural T) (key-subst-natural (from (⟦ⓜ⟧-sound ρ (locksˡᵗ Λ)))))
                    (M.cl-tm-subst-cong-tm (ty-closed-natural T) ev))
var-α-equiv _ _ _ = throw-error "Variables are not equal."


tm-msg : ErrorMsg
tm-msg = "Terms are not α-equivalent."

tm-α-equiv-helper : (t1 : Tm Γ1 T) (t2 : Tm Γ2 T) (eΓ : AlphaEquivCtx Γ1 Γ2) →
                    PCM (⟦ t1 ⟧tm M.[ ty-closed-natural T ∣ alpha-equiv-sub eΓ ]cl M.≅ᵗᵐ ⟦ t2 ⟧tm)
ext-tmargs-α-equiv-helper : ∀ {arginfos}
                            {names1 : TmArgBoundNames arginfos} (args1 : ExtTmArgs arginfos names1 Γ1)
                            {names2 : TmArgBoundNames arginfos} (args2 : ExtTmArgs arginfos names2 Γ2)
                            (eΓ : AlphaEquivCtx Γ1 Γ2) →
                            PCM (semtms-subst ⟦ args1 ⟧tmextargs (alpha-equiv-sub eΓ) ≅ᵗᵐˢ ⟦ args2 ⟧tmextargs)

tm-α-equiv-helper (var' _ {v1}) (var' _ {v2}) = var-α-equiv v1 v2
tm-α-equiv-helper {T = ⟨ .μ ∣ T ⟩} (mod⟨ μ ⟩ t1) (mod⟨ .μ ⟩ t2) eΓ = do
  et ← tm-α-equiv-helper t1 t2 (eΓ ,lock⟨ μ ⟩)
  return (M.transᵗᵐ (dra-intro-cl-natural ⟦ μ ⟧mod (ty-closed-natural T) ⟦ t1 ⟧tm)
                    (dra-intro-cong ⟦ μ ⟧mod et))
tm-α-equiv-helper (mod-elim {o = o1} {n = n1} {T = T1} {S = S} ρ1 μ1 _ t1 s1) (mod-elim {o = o2} {n = n2} {T = T2} ρ2 μ2 _ t2 s2) eΓ = do
  refl ← o1 ≟mode o2
  refl ← n1 ≟mode n2
  refl ← ρ1 ≟mod ρ2
  refl ← μ1 ≟mod μ2
  refl ← T1 ≟ty T2
  et ← tm-α-equiv-helper t1 t2 (eΓ ,lock⟨ ρ1 ⟩)
  es ← tm-α-equiv-helper s1 s2 (eΓ ,, ρ1 ⓜ μ1 ∣ T1)
  return (M.transᵗᵐ (dra-let-natural ⟦ ρ1 ⟧mod ⟦ μ1 ⟧mod (ty-closed-natural T1) (ty-closed-natural S) (alpha-equiv-sub eΓ))
                    (dra-let-cong ⟦ ρ1 ⟧mod ⟦ μ1 ⟧mod (ty-closed-natural T1) (ty-closed-natural S) et (
                      M.transᵗᵐ (M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural S) (
                        M.transˢ (M.symˢ (M.⊚-congʳ (M.lift-cl-subst-cong-cl (ⓓ-preserves-cl ⟦ ρ1 ⟧mod ⟦ μ1 ⟧mod (ty-closed-natural T1)))))
                                 (M.lift-cl-,,-cong-commute (M.symᶜᵗʸ (eq-dra-closed (⟦ⓜ⟧-sound ρ1 μ1) (ty-closed-natural T1))) (alpha-equiv-sub eΓ))))
                        (M.cl-tm-subst-cong-tm (ty-closed-natural S) es))))
tm-α-equiv-helper {T = ⟨ μ ∣ T ⟩⇛ S} (lam[ .μ ∣ _ ∈ .T ] t1) (lam[ .μ ∣ _ ∈ .T ] t2) eΓ = do
  et ← tm-α-equiv-helper t1 t2 (eΓ ,, μ ∣ T)
  return (M.transᵗᵐ (M.lamcl-natural (ty-closed-natural ⟨ μ ∣ T ⟩) (ty-closed-natural S))
                    (M.lamcl-cong (ty-closed-natural S) et))
tm-α-equiv-helper {T = S} (_∙_ {T = T1} {μ = μ1} f1 t1) (_∙_ {T = T2} {μ = μ2} f2 t2) eΓ = do
  refl ← mod-dom μ1 ≟mode mod-dom μ2
  refl ← μ1 ≟mod μ2
  refl ← T1 ≟ty T2
  ef ← tm-α-equiv-helper f1 f2 eΓ
  et ← tm-α-equiv-helper t1 t2 (eΓ ,lock⟨ μ1 ⟩)
  return (M.transᵗᵐ (M.app-cl-natural (ty-closed-natural ⟨ μ1 ∣ T1 ⟩) (ty-closed-natural S))
                    (M.app-cong ef (M.transᵗᵐ (dra-intro-cl-natural ⟦ μ1 ⟧mod (ty-closed-natural T1) ⟦ t1 ⟧tm) (dra-intro-cong ⟦ μ1 ⟧mod et))))
tm-α-equiv-helper zero zero eΓ = return (M.const-cl-natural _)
tm-α-equiv-helper (suc t1) (suc t2) eΓ = do
  et ← tm-α-equiv-helper t1 t2 eΓ
  return (M.transᵗᵐ (M.suc'-cl-natural _) (M.suc'-cong et))
tm-α-equiv-helper {T = T} (nat-rec z1 s1 t1) (nat-rec z2 s2 t2) eΓ = do
  ez ← tm-α-equiv-helper z1 z2 eΓ
  es ← tm-α-equiv-helper s1 s2 eΓ
  et ← tm-α-equiv-helper t1 t2 eΓ
  return (M.transᵗᵐ (M.nat-rec-cl-natural (ty-closed-natural T))
                    (M.nat-rec-cong ez
                                    (M.transᵗᵐ (M.cl-tm-subst-cong-cl (M.fun-closed-congᶜⁿ (M.symᶜⁿ (𝟙-preserves-cl (ty-closed-natural T))) (M.reflᶜⁿ (ty-closed-natural T))))
                                               es)
                                    et))
tm-α-equiv-helper true true eΓ = return (M.const-cl-natural _)
tm-α-equiv-helper false false eΓ = return (M.const-cl-natural _)
tm-α-equiv-helper {T = T} (if b1 t1 f1) (if b2 t2 f2) eΓ = do
  eb ← tm-α-equiv-helper b1 b2 eΓ
  et ← tm-α-equiv-helper t1 t2 eΓ
  ef ← tm-α-equiv-helper f1 f2 eΓ
  return (M.transᵗᵐ (M.if'-cl-natural (ty-closed-natural T)) (M.if'-cong eb et ef))
tm-α-equiv-helper {T = T ⊠ S} (pair t1 s1) (pair t2 s2) eΓ = do
  et ← tm-α-equiv-helper t1 t2 eΓ
  es ← tm-α-equiv-helper s1 s2 eΓ
  return (M.transᵗᵐ (M.pair-cl-natural (ty-closed-natural T) (ty-closed-natural S)) (M.pair-cong et es))
tm-α-equiv-helper {T = T} (fst {S = S1} p1) (fst {S = S2} p2) eΓ = do
  refl ← S1 ≟ty S2
  ep ← tm-α-equiv-helper p1 p2 eΓ
  return (M.transᵗᵐ (M.fst-cl-natural (ty-closed-natural T) (ty-closed-natural S1)) (M.fst-cong ep))
tm-α-equiv-helper {T = S} (snd {T = T1} p1) (snd {T = T2} p2) eΓ = do
  refl ← T1 ≟ty T2
  ep ← tm-α-equiv-helper p1 p2 eΓ
  return (M.transᵗᵐ (M.snd-cl-natural (ty-closed-natural T1) (ty-closed-natural S)) (M.snd-cong ep))
tm-α-equiv-helper (ext c1 names1 args1 ty-eq1) (ext c2 names2 args2 ty-eq2) eΓ = do
  refl ← c1 ≟tm-code c2
  refl ← return ty-eq1 -- we can only pattern match on ty-eq1 here because at this point we know c1 = c2
  refl ← return (uip ty-eq1 refl)
  refl ← return ty-eq2
  refl ← return (uip ty-eq2 refl)
  eargs ← ext-tmargs-α-equiv-helper args1 args2 eΓ
  return (M.transᵗᵐ (apply-sem-tm-constructor-natural ⟦ c1 ⟧tm-code (⟦⟧tm-code-natural c1) (alpha-equiv-sub eΓ) ⟦ args1 ⟧tmextargs)
                    (apply-sem-tm-constructor-cong ⟦ c1 ⟧tm-code (⟦⟧tm-code-cong c1) eargs))
tm-α-equiv-helper {T = T} (global-def _ {t1}) (global-def _ {t2}) eΓ = do
  et ← tm-α-equiv-helper t1 t2 ◇
  return (M.transᵗᵐ (M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural T) (M.◇-terminal _ _ _))
                    (M.cl-tm-subst-cong-tm (ty-closed-natural T) et))
tm-α-equiv-helper _ _ _ = throw-error tm-msg

ext-tmargs-α-equiv-helper {arginfos = []}                 _              _              eΓ = return _
ext-tmargs-α-equiv-helper {arginfos = arginfo ∷ arginfos} (arg1 , args1) (arg2 , args2) eΓ = do
  earg ← tm-α-equiv-helper arg1 arg2 (alpha-equiv-nltel eΓ (tmarg-tel arginfo))
  eargs ← ext-tmargs-α-equiv-helper args1 args2 eΓ
  return (M.transᵗᵐ (M.cl-tm-subst-cong-subst-2-2 (ty-closed-natural (tmarg-ty arginfo)) (alpha-equiv-nltel-sub eΓ (tmarg-tel arginfo)))
                    (M.cl-tm-subst-cong-tm (ty-closed-natural (tmarg-ty arginfo)) earg)
         , eargs)

infix 10 _≟tm_
_≟tm_ : (t1 t2 : Tm Γ T) → PCM (⟦ t1 ⟧tm M.≅ᵗᵐ ⟦ t2 ⟧tm)
_≟tm_ {Γ = Γ} {T = T} t1 t2 = do
  et ← tm-α-equiv-helper t1 t2 alpha-equiv-ctx-refl
  return (M.transᵗᵐ (M.symᵗᵐ (M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural T) (alpha-equiv-sub-refl Γ))
                                        (M.cl-tm-subst-id (ty-closed-natural T) _)))
                    et)


bprop-msg : ErrorMsg
bprop-msg = "Propositions are not equal."

bprop-α-equiv-helper : (φ1 : bProp Γ1) (φ2 : bProp Γ2) (eΓ : AlphaEquivCtx Γ1 Γ2) →
                       PCM (⟦ φ1 ⟧bprop M.[ alpha-equiv-sub eΓ ] M.≅ᵗʸ ⟦ φ2 ⟧bprop)
ext-bpargs-α-equiv-helper : ∀ {arginfos}
                            {names1 : ArgBoundNames arginfos} (args1 : ExtBPArgs arginfos names1 Γ1)
                            {names2 : ArgBoundNames arginfos} (args2 : ExtBPArgs arginfos names2 Γ2)
                            (eΓ : AlphaEquivCtx Γ1 Γ2) →
                            PCM (semprops-subst ⟦ args1 ⟧bpextargs (alpha-equiv-sub eΓ) ≅ᵇᵖˢ ⟦ args2 ⟧bpextargs)

bprop-α-equiv-helper ⊤ᵇ ⊤ᵇ eΓ = return (M.Const-natural _ _)
bprop-α-equiv-helper ⊥ᵇ ⊥ᵇ eΓ = return (M.Const-natural _ _)
bprop-α-equiv-helper (_≡ᵇ_ {T1} t1 s1) (_≡ᵇ_ {T2} t2 s2) eΓ = do
  refl ← T1 ≟ty T2
  et ← tm-α-equiv-helper t1 t2 eΓ
  es ← tm-α-equiv-helper s1 s2 eΓ
  return (M.transᵗʸ (M.Id-cl-natural (ty-closed-natural T1) (alpha-equiv-sub eΓ)) (M.Id-cong' et es))
bprop-α-equiv-helper (⟨ μ1 ∣ φ1 ⟩⊃ ψ1) (⟨ μ2 ∣ φ2 ⟩⊃ ψ2) eΓ = do
  refl ← mod-dom μ1 ≟mode mod-dom μ2
  refl ← μ1 ≟mod μ2
  eφ ← bprop-α-equiv-helper φ1 φ2 (eΓ ,lock⟨ μ1 ⟩)
  eψ ← bprop-α-equiv-helper ψ1 ψ2 eΓ
  return (M.transᵗʸ (M.⇛-natural (alpha-equiv-sub eΓ))
                    (M.⇛-cong (M.transᵗʸ (dra-natural ⟦ μ1 ⟧mod (alpha-equiv-sub eΓ)) (dra-cong ⟦ μ1 ⟧mod eφ)) eψ))
bprop-α-equiv-helper (φ1 ∧ ψ1) (φ2 ∧ ψ2) eΓ = do
  eφ ← bprop-α-equiv-helper φ1 φ2 eΓ
  eψ ← bprop-α-equiv-helper ψ1 ψ2 eΓ
  return (M.transᵗʸ (M.⊠-natural (alpha-equiv-sub eΓ)) (M.⊠-cong eφ eψ))
bprop-α-equiv-helper (∀[ μ1 ∣ x1 ∈ T1 ] φ1) (∀[ μ2 ∣ x2 ∈ T2 ] φ2) eΓ = do
  refl ← mod-dom μ1 ≟mode mod-dom μ2
  refl ← μ1 ≟mod μ2
  refl ← T1 ≟ty T2
  eφ ← bprop-α-equiv-helper φ1 φ2 (eΓ ,, μ1 ∣ T1)
  return (M.transᵗʸ (M.Pi-natural-closed-dom (ty-closed-natural ⟨ μ1 ∣ T1 ⟩) (alpha-equiv-sub eΓ)) (M.Pi-cong-cod eφ))
bprop-α-equiv-helper ⟨ μ1 ∣ φ1 ⟩ ⟨ μ2 ∣ φ2 ⟩ eΓ = do
  refl ← mod-dom μ1 ≟mode mod-dom μ2
  refl ← μ1 ≟mod μ2
  eφ ← bprop-α-equiv-helper φ1 φ2 (eΓ ,lock⟨ μ1 ⟩)
  return (M.transᵗʸ (dra-natural ⟦ μ1 ⟧mod (alpha-equiv-sub eΓ)) (dra-cong ⟦ μ1 ⟧mod eφ))
bprop-α-equiv-helper (ext c1 tmarg-names1 tmargs1 bparg-names1 bpargs1) (ext c2 tmarg-names2 tmargs2 bparg-names2 bpargs2) eΓ = do
  refl ← c1 ≟bp-code c2
  etmargs ← ext-tmargs-α-equiv-helper tmargs1 tmargs2 eΓ
  ebpargs ← ext-bpargs-α-equiv-helper bpargs1 bpargs2 eΓ
  return (M.transᵗʸ (apply-sem-prop-constructor-natural ⟦ c1 ⟧bp-code (alpha-equiv-sub eΓ) (⟦⟧bp-code-natural c1) ⟦ tmargs1 ⟧tmextargs ⟦ bpargs1 ⟧bpextargs)
                    (apply-sem-prop-constructor-cong ⟦ c1 ⟧bp-code (⟦⟧bp-code-cong c1) etmargs ebpargs))
bprop-α-equiv-helper _ _ _ = throw-error bprop-msg

ext-bpargs-α-equiv-helper {arginfos = []}          bps1         bps2         eΓ = return _
ext-bpargs-α-equiv-helper {arginfos = arginfo ∷ _} (bp1 , bps1) (bp2 , bps2) eΓ = do
  earg ← bprop-α-equiv-helper bp1 bp2 (alpha-equiv-nltel eΓ (arg-tel arginfo))
  eargs ← ext-bpargs-α-equiv-helper bps1 bps2 eΓ
  return (M.transᵗʸ (M.ty-subst-cong-subst-2-2 _ (alpha-equiv-nltel-sub eΓ (arg-tel arginfo)))
                    (M.ty-subst-cong-ty _ earg)
         , eargs)


infix 10 _≟bprop_
_≟bprop_ : (φ1 φ2 : bProp Γ) → PCM (⟦ φ1 ⟧bprop M.≅ᵗʸ ⟦ φ2 ⟧bprop)
_≟bprop_ {Γ = Γ} φ1 φ2 = do
  eφ ← bprop-α-equiv-helper φ1 φ2 alpha-equiv-ctx-refl
  return (M.transᵗʸ (M.symᵗʸ (M.transᵗʸ (M.ty-subst-cong-subst (alpha-equiv-sub-refl Γ) _) (M.ty-subst-id _))) eφ)
