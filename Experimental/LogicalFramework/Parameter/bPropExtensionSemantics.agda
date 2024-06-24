open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension using (TmExt)

module Experimental.LogicalFramework.Parameter.bPropExtensionSemantics
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯)
  where

open import Data.List
open import Data.Product
open import Data.Unit.Polymorphic
import Data.Unit as l0

open import Model.CwF-Structure as M
  renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm; ClosedTy to ClosedSemTy) using ()


open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics ℳ 𝒯
open import Experimental.LogicalFramework.Parameter.bPropExtension ℳ 𝒯 𝓉
open bPropExt
open import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Interpretation.TypeContext ℳ 𝒯

open ModeTheory ℳ

private variable
  m n : Mode


SemPropConstructorLocal : ∀ {m} → List (TmArgInfo m) → List (ArgInfo m) → Ctx m → Set₁
SemPropConstructorLocal []                   []                   Γ = SemTy ⟦ Γ ⟧ctx
SemPropConstructorLocal []                   (bp-info ∷ bp-infos) Γ =
  SemTy (⟦ Γ ⟧ctx ++⟦ arg-tel bp-info ⟧nltel) → SemPropConstructorLocal [] bp-infos Γ
SemPropConstructorLocal (tm-info ∷ tm-infos) bp-infos             Γ =
  SemTm (⟦ Γ ⟧ctx ++⟦ tmarg-tel tm-info ⟧nltel) ⟦ tmarg-ty tm-info ⟧ty → SemPropConstructorLocal tm-infos bp-infos Γ

SemPropConstructor : ∀ {m} → List (TmArgInfo m) → List (ArgInfo m) → Set₁
SemPropConstructor {m} tm-infos bp-infos = {Γ : Ctx m} → SemPropConstructorLocal tm-infos bp-infos Γ

SemPropConstructorLocalNatural : {tmarginfos : List (TmArgInfo m)} {bparginfos : List (ArgInfo m)} {Γ Δ : Ctx m}
                                 (FΔ : SemPropConstructorLocal tmarginfos bparginfos Δ)
                                 (FΓ : SemPropConstructorLocal tmarginfos bparginfos Γ)
                                 (σ : ⟦ Γ ⟧ctx M.⇒ ⟦ Δ ⟧ctx) →
                                 Set₁
SemPropConstructorLocalNatural {tmarginfos = []}            {[]}                    TΔ TΓ σ =
  TΔ M.[ σ ] M.≅ᵗʸ TΓ
SemPropConstructorLocalNatural {tmarginfos = []}            {bparginfo ∷ _} {Δ = Δ} FΔ FΓ σ =
  (φ : SemTy (⟦ Δ ⟧ctx ++⟦ arg-tel bparginfo ⟧nltel)) →
  SemPropConstructorLocalNatural (FΔ φ) (FΓ (φ M.[ apply-nltel-sub σ (arg-tel bparginfo) ])) σ
SemPropConstructorLocalNatural {tmarginfos = tmarginfo ∷ _} {_}             {Δ = Δ} FΔ FΓ σ =
  (t : SemTm (⟦ Δ ⟧ctx ++⟦ tmarg-tel tmarginfo ⟧nltel) ⟦ tmarg-ty tmarginfo ⟧ty) →
  SemPropConstructorLocalNatural (FΔ t) (FΓ (t M.[ ty-closed-natural (tmarg-ty tmarginfo) ∣ apply-nltel-sub σ (tmarg-tel tmarginfo) ]cl)) σ

SemPropConstructorNatural : {tmarginfos : List (TmArgInfo m)} {bparginfos : List (ArgInfo m)} →
                            SemPropConstructor tmarginfos bparginfos → Set₁
SemPropConstructorNatural {m = m} F =
  {Γ Δ : Ctx m} (σ : ⟦ Γ ⟧ctx M.⇒ ⟦ Δ ⟧ctx) → SemPropConstructorLocalNatural (F {Δ}) (F {Γ}) σ


SemPropConstructorLocalEquiv : {tmarginfos : List (TmArgInfo m)} {bparginfos : List (ArgInfo m)} {Γ : Ctx m} →
                               (F G : SemPropConstructorLocal tmarginfos bparginfos Γ) →
                               Set₁
SemPropConstructorLocalEquiv {tmarginfos = []} {bparginfos = []} T S = T M.≅ᵗʸ S
SemPropConstructorLocalEquiv {tmarginfos = []} {bparginfos = bparginfo ∷ _} {Γ} F G =
  {T S : SemTy (⟦ Γ ⟧ctx ++⟦ arg-tel bparginfo ⟧nltel)} → T M.≅ᵗʸ S → SemPropConstructorLocalEquiv (F T) (G S)
SemPropConstructorLocalEquiv {tmarginfos = tmarginfo ∷ _} {bparginfos = _} {Γ} F G =
  {t s : SemTm (⟦ Γ ⟧ctx ++⟦ tmarg-tel tmarginfo ⟧nltel) ⟦ tmarg-ty tmarginfo ⟧ty} →
  t M.≅ᵗᵐ s → SemPropConstructorLocalEquiv (F t) (G s)

SemPropConstructorLocalCong : {tmarginfos : List (TmArgInfo m)} {bparginfos : List (ArgInfo m)} {Γ : Ctx m} →
                              SemPropConstructorLocal tmarginfos bparginfos Γ →
                              Set₁
SemPropConstructorLocalCong F = SemPropConstructorLocalEquiv F F

SemPropConstructorCong : {tmarginfos : List (TmArgInfo m)} {bparginfos : List (ArgInfo m)} →
                         SemPropConstructor tmarginfos bparginfos →
                         Set₁
SemPropConstructorCong {m = m} F = {Γ : Ctx m} → SemPropConstructorLocalCong (F {Γ})


record bPropExtSem (𝒷 : bPropExt) : Set₁ where
  no-eta-equality
  field
    ⟦_⟧bp-code : ∀ {m} → (c : bPropExtCode 𝒷 m) →
                 SemPropConstructor (bp-code-tmarg-infos 𝒷 c) (bp-code-bparg-infos 𝒷 c)
    ⟦⟧bp-code-natural : ∀ {m} (c : bPropExtCode 𝒷 m) → SemPropConstructorNatural ⟦ c ⟧bp-code
    ⟦⟧bp-code-cong : ∀ {m} (c : bPropExtCode 𝒷 m) → SemPropConstructorCong ⟦ c ⟧bp-code


SemProps : List (ArgInfo m) → Ctx m → Set₁
SemProps []                   Γ = ⊤
SemProps (arginfo ∷ arginfos) Γ = SemTy (⟦ Γ ⟧ctx ++⟦ arg-tel arginfo ⟧nltel) × SemProps arginfos Γ

apply-sem-prop-constructor : {tmarginfos : List (TmArgInfo m)} {bparginfos : List (ArgInfo m)} {Γ : Ctx m} →
                             SemPropConstructorLocal tmarginfos bparginfos Γ →
                             SemTms tmarginfos Γ →
                             SemProps bparginfos Γ →
                             SemTy ⟦ Γ ⟧ctx
apply-sem-prop-constructor {tmarginfos = []}            {bparginfos = []}            T _ _ = T
apply-sem-prop-constructor {tmarginfos = []}            {bparginfos = bparginfo ∷ _} F _ (prop , props) = apply-sem-prop-constructor (F prop) l0.tt props
apply-sem-prop-constructor {tmarginfos = tmarginfo ∷ _} {bparginfos = _}             F (tm , tms) props = apply-sem-prop-constructor (F tm) tms props

semprops-subst : {bparginfos : List (ArgInfo m)} {Γ Δ : Ctx m} →
                 SemProps bparginfos Δ →
                 (σ : ⟦ Γ ⟧ctx M.⇒ ⟦ Δ ⟧ctx) →
                 SemProps bparginfos Γ
semprops-subst {bparginfos = []} props σ = tt
semprops-subst {bparginfos = bparginfo ∷ bparginfos} (prop , props) σ =
  prop M.[ apply-nltel-sub σ (arg-tel bparginfo) ] , semprops-subst props σ

_≅ᵇᵖˢ_ : {bparginfos : List (ArgInfo m)} {Γ : Ctx m} (props props' : SemProps bparginfos Γ) → Set₁
_≅ᵇᵖˢ_ {bparginfos = []} props props' = ⊤
_≅ᵇᵖˢ_ {bparginfos = bparginfo ∷ _} (prop , props) (prop' , props') = (prop M.≅ᵗʸ prop') × (props ≅ᵇᵖˢ props')


apply-sem-prop-constructor-natural-local : {tmarginfos : List (TmArgInfo m)} {bparginfos : List (ArgInfo m)}
                                           {Γ Δ : Ctx m}
                                           (σ : ⟦ Γ ⟧ctx M.⇒ ⟦ Δ ⟧ctx)
                                           (F : SemPropConstructorLocal tmarginfos bparginfos Δ)
                                           (G : SemPropConstructorLocal tmarginfos bparginfos Γ) →
                                           SemPropConstructorLocalNatural F G σ →
                                           (tms : SemTms tmarginfos Δ) (props : SemProps bparginfos Δ)  →
                                           (apply-sem-prop-constructor F tms props) M.[ σ ]
                                             M.≅ᵗʸ
                                           apply-sem-prop-constructor G (semtms-subst tms σ) (semprops-subst props σ)
apply-sem-prop-constructor-natural-local {tmarginfos = []}    {[]}    σ F G nat _ _ = nat
apply-sem-prop-constructor-natural-local {tmarginfos = []}    {_ ∷ _} σ F G nat _ (prop , props) =
  apply-sem-prop-constructor-natural-local σ (F prop) (G _) (nat prop) l0.tt props
apply-sem-prop-constructor-natural-local {tmarginfos = _ ∷ _} {_}     σ F G nat (tm , tms) props =
  apply-sem-prop-constructor-natural-local σ (F tm) (G _) (nat tm) tms props

apply-sem-prop-constructor-natural : {tmarginfos : List (TmArgInfo m)} {bparginfos : List (ArgInfo m)}
                                     (F : SemPropConstructor tmarginfos bparginfos)
                                     {Γ Δ : Ctx m}
                                     (σ : ⟦ Γ ⟧ctx M.⇒ ⟦ Δ ⟧ctx) →
                                     SemPropConstructorNatural F →
                                     (tms : SemTms tmarginfos Δ) (props : SemProps bparginfos Δ) →
                                     (apply-sem-prop-constructor F tms props) M.[ σ ]
                                       M.≅ᵗʸ
                                     apply-sem-prop-constructor (F {Γ}) (semtms-subst tms σ) (semprops-subst props σ)
apply-sem-prop-constructor-natural F σ nat tms props = apply-sem-prop-constructor-natural-local σ F F (nat σ) tms props

apply-sem-prop-constr-local-equiv : {tmarginfos : List (TmArgInfo m)} {bparginfos : List (ArgInfo m)}
                                    {Γ : Ctx m}
                                    (F G : SemPropConstructorLocal tmarginfos bparginfos Γ) →
                                    SemPropConstructorLocalEquiv F G →
                                    {tms tms' : SemTms tmarginfos Γ} {props props' : SemProps bparginfos Γ} →
                                    tms ≅ᵗᵐˢ tms' →
                                    props ≅ᵇᵖˢ props' →
                                    apply-sem-prop-constructor F tms props M.≅ᵗʸ apply-sem-prop-constructor G tms' props'
apply-sem-prop-constr-local-equiv {tmarginfos = []}    {[]}    F G equiv _ _ = equiv
apply-sem-prop-constr-local-equiv {tmarginfos = []}    {_ ∷ _} F G equiv 𝒆 (e , es) =
  apply-sem-prop-constr-local-equiv (F _) (G _) (equiv e) l0.tt es
apply-sem-prop-constr-local-equiv {tmarginfos = _ ∷ _} {_}     F G equiv (𝒆 , 𝒆s) e =
  apply-sem-prop-constr-local-equiv (F _) (G _) (equiv 𝒆) 𝒆s e

apply-sem-prop-constructor-cong : {tmarginfos : List (TmArgInfo m)} {bparginfos : List (ArgInfo m)}
                                  {Γ : Ctx m}
                                  (F : SemPropConstructor tmarginfos bparginfos) →
                                  SemPropConstructorCong F →
                                  {tms tms' : SemTms tmarginfos Γ} {props props' : SemProps bparginfos Γ} →
                                  tms ≅ᵗᵐˢ tms' →
                                  props ≅ᵇᵖˢ props' →
                                  apply-sem-prop-constructor F tms props M.≅ᵗʸ apply-sem-prop-constructor F tms' props'
apply-sem-prop-constructor-cong F cong 𝒆 e = apply-sem-prop-constr-local-equiv F F cong 𝒆 e
