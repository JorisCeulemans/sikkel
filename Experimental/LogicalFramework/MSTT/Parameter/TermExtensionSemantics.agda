open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension

module Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ)
  where

open import Data.List
open import Data.Product
open import Data.Unit

open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯
open TmExt
open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Interpretation.TypeContext ℳ 𝒯

open import Model.CwF-Structure as M
  renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm; ClosedTy to ClosedSemTy) using ()
import Model.DRA as DRA

open ModeTheory ℳ

private variable
  m n : Mode


-- A SemTmConstructorLocal refers to an MSTT context and not a
-- semantic context. This has the advantage that it corresponds to the
-- arguments of the contructor Tm.ext.
SemTmConstructorLocal : List (TmArgInfo m) → Ctx m → Ty m → Set
SemTmConstructorLocal []                   Γ T = SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty
SemTmConstructorLocal (arginfo ∷ arginfos) Γ T =
  SemTm (⟦ Γ ⟧ctx ++⟦ tmarg-tel arginfo ⟧nltel) ⟦ tmarg-ty arginfo ⟧ty → SemTmConstructorLocal arginfos Γ T

SemTmConstructor : List (TmArgInfo m) → Ty m → Set
SemTmConstructor {m = m} arginfos T = {Γ : Ctx m} → SemTmConstructorLocal arginfos Γ T


SemTmConstructorLocalNatural : {arginfos : List (TmArgInfo m)} {Γ Δ : Ctx m} {T : Ty m}
                               (fΔ : SemTmConstructorLocal arginfos Δ T) (fΓ : SemTmConstructorLocal arginfos Γ T)
                               (σ : ⟦ Γ ⟧ctx M.⇒ ⟦ Δ ⟧ctx) →
                               Set
SemTmConstructorLocalNatural {arginfos = []} {T = T} tΔ tΓ σ =
  tΔ M.[ ty-closed-natural T ∣ σ ]cl M.≅ᵗᵐ tΓ
SemTmConstructorLocalNatural {arginfos = arginfo ∷ arginfos} {Δ = Δ} fΔ fΓ σ =
  (t : SemTm (⟦ Δ ⟧ctx ++⟦ tmarg-tel arginfo ⟧nltel) ⟦ tmarg-ty arginfo ⟧ty) →
  SemTmConstructorLocalNatural (fΔ t) (fΓ (t M.[ ty-closed-natural (tmarg-ty arginfo) ∣ apply-nltel-sub σ (tmarg-tel arginfo) ]cl)) σ

SemTmConstructorNatural : {tmarg-infos : List (TmArgInfo m)} {T : Ty m} → SemTmConstructor tmarg-infos T → Set
SemTmConstructorNatural {m = m} f =
  {Γ Δ : Ctx m} (σ : ⟦ Γ ⟧ctx M.⇒ ⟦ Δ ⟧ctx) → SemTmConstructorLocalNatural (f {Δ}) (f {Γ}) σ


SemTmConstructorLocalEquiv : {arginfos : List (TmArgInfo m)} {Γ : Ctx m} {T : Ty m}
                             (f g : SemTmConstructorLocal arginfos Γ T) →
                             Set
SemTmConstructorLocalEquiv {arginfos = []} t s = t M.≅ᵗᵐ s
SemTmConstructorLocalEquiv {arginfos = arginfo ∷ arginfos} {Γ} f g =
  {t s : SemTm (⟦ Γ ⟧ctx ++⟦ tmarg-tel arginfo ⟧nltel) ⟦ tmarg-ty arginfo ⟧ty} →
  t M.≅ᵗᵐ s → SemTmConstructorLocalEquiv (f t) (g s)

SemTmConstructorLocalCong : {arginfos : List (TmArgInfo m)} {Γ : Ctx m} {T : Ty m} →
                            SemTmConstructorLocal arginfos Γ T →
                            Set
SemTmConstructorLocalCong f = SemTmConstructorLocalEquiv f f

SemTmConstructorCong : {arginfos : List (TmArgInfo m)} {T : Ty m} →
                       SemTmConstructor arginfos T →
                       Set
SemTmConstructorCong {m = m} f = {Γ : Ctx m} → SemTmConstructorLocalCong (f {Γ})


record TmExtSem (𝓉 : TmExt) : Set where
  no-eta-equality
  field
    ⟦_⟧tm-code : ∀ {m} → (c : TmExtCode 𝓉 m) → SemTmConstructor (tm-code-arginfos 𝓉 c) (tm-code-ty 𝓉 c)
    ⟦⟧tm-code-natural : ∀ {m} (c : TmExtCode 𝓉 m) → SemTmConstructorNatural ⟦ c ⟧tm-code
    ⟦⟧tm-code-cong : ∀ {m} (c : TmExtCode 𝓉 m) → SemTmConstructorCong ⟦ c ⟧tm-code


SemTms : List (TmArgInfo m) → Ctx m → Set
SemTms []                   Γ = ⊤
SemTms (arginfo ∷ arginfos) Γ = SemTm (⟦ Γ ⟧ctx ++⟦ tmarg-tel arginfo ⟧nltel) ⟦ tmarg-ty arginfo ⟧ty × SemTms arginfos Γ

apply-sem-tm-constructor : {arginfos : List (TmArgInfo m)} {Γ : Ctx m} {T : Ty m} →
                           SemTmConstructorLocal arginfos Γ T →
                           SemTms arginfos Γ →
                           SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty
apply-sem-tm-constructor {arginfos = []}    t tms        = t
apply-sem-tm-constructor {arginfos = _ ∷ _} f (tm , tms) = apply-sem-tm-constructor (f tm) tms

semtms-subst : {arginfos : List (TmArgInfo m)} {Γ Δ : Ctx m} →
               SemTms arginfos Δ →
               (⟦ Γ ⟧ctx M.⇒ ⟦ Δ ⟧ctx) →
               SemTms arginfos Γ
semtms-subst {arginfos = []} tms σ = tt
semtms-subst {arginfos = arginfo ∷ arginfos} (tm , tms) σ =
  tm M.[ ty-closed-natural (tmarg-ty arginfo) ∣ apply-nltel-sub σ (tmarg-tel arginfo) ]cl , semtms-subst tms σ

_≅ᵗᵐˢ_ : {arginfos : List (TmArgInfo m)} {Γ : Ctx m} (tms tms' : SemTms arginfos Γ) → Set
_≅ᵗᵐˢ_ {arginfos = []} tms tms' = ⊤
_≅ᵗᵐˢ_ {arginfos = _ ∷ _} (tm , tms) (tm' , tms') = (tm M.≅ᵗᵐ tm') × (tms ≅ᵗᵐˢ tms')

apply-sem-tm-constr-natural-local : {arginfos : List (TmArgInfo m)} {Γ Δ : Ctx m} {T : Ty m}
                                    (σ : ⟦ Γ ⟧ctx M.⇒ ⟦ Δ ⟧ctx)
                                    (f : SemTmConstructorLocal arginfos Δ T) (g : SemTmConstructorLocal arginfos Γ T) →
                                    SemTmConstructorLocalNatural f g σ →
                                    (tms : SemTms arginfos Δ) →
                                    (apply-sem-tm-constructor f tms) M.[ ty-closed-natural T ∣ σ ]cl
                                      M.≅ᵗᵐ
                                    apply-sem-tm-constructor g (semtms-subst tms σ)
apply-sem-tm-constr-natural-local {arginfos = []} σ t s nat _ = nat
apply-sem-tm-constr-natural-local {arginfos = arginfo ∷ arginfos} σ f g nat (tm , tms) =
  apply-sem-tm-constr-natural-local σ (f tm) (g _) (nat tm) tms

apply-sem-tm-constructor-natural : {arginfos : List (TmArgInfo m)} {Γ Δ : Ctx m} {T : Ty m}
                                   (f : SemTmConstructor arginfos T) → SemTmConstructorNatural f →
                                   (σ : ⟦ Γ ⟧ctx M.⇒ ⟦ Δ ⟧ctx)
                                   (tms : SemTms arginfos Δ) →
                                   (apply-sem-tm-constructor f tms) M.[ ty-closed-natural T ∣ σ ]cl
                                     M.≅ᵗᵐ
                                   apply-sem-tm-constructor (f {Γ}) (semtms-subst tms σ)
apply-sem-tm-constructor-natural f nat σ tms = apply-sem-tm-constr-natural-local σ f f (nat σ) tms

apply-sem-tm-constr-local-equiv : {arginfos : List (TmArgInfo m)} {Γ : Ctx m} {T : Ty m}
                                  (f g : SemTmConstructorLocal arginfos Γ T) → SemTmConstructorLocalEquiv f g →
                                  {tms tms' : SemTms arginfos Γ} → tms ≅ᵗᵐˢ tms' →
                                  apply-sem-tm-constructor f tms M.≅ᵗᵐ apply-sem-tm-constructor g tms'
apply-sem-tm-constr-local-equiv {arginfos = []} f g equiv _ = equiv
apply-sem-tm-constr-local-equiv {arginfos = arginfo ∷ arginfos} f g equiv (𝒆 , 𝒆s) =
  apply-sem-tm-constr-local-equiv (f _) (g _) (equiv 𝒆) 𝒆s

apply-sem-tm-constructor-cong : {arginfos : List (TmArgInfo m)} {Γ : Ctx m} {T : Ty m}
                                (f : SemTmConstructor arginfos T) → SemTmConstructorCong f →
                                {tms tms' : SemTms arginfos Γ} → tms ≅ᵗᵐˢ tms' →
                                apply-sem-tm-constructor f tms M.≅ᵗᵐ apply-sem-tm-constructor f tms'
apply-sem-tm-constructor-cong f fcong 𝒆 = apply-sem-tm-constr-local-equiv f f fcong 𝒆
