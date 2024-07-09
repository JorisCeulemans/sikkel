--------------------------------------------------
-- Extraction of MSTT contexts, types, programs to Agda types and
-- programs
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.MSTT.Extraction
  (𝒫 : MSTT-Parameter)
  where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Product renaming (_,_ to [_,_])
open import Data.Product.Function.NonDependent.Propositional using (_×-↔_)
open import Data.Unit
open import Function
open import Function.Consequences.Setoid
open import Function.Construct.Composition
open import Function.Construct.Identity
open import Function.Construct.Symmetry
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality

open MSTT-Parameter 𝒫
open import Experimental.LogicalFramework.MSTT.Syntax ℳ 𝒯 𝓉 hiding (refl)
open import Experimental.LogicalFramework.MSTT.Interpretation ℳ 𝒯 𝓉 ⟦𝓉⟧

open import Preliminaries
import Model.BaseCategory as M
open import Model.CwF-Structure as M
  renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm; tm-setoid to semtm-setoid) using ()
import Model.Type.Function as M
import Model.DRA as DRA

private variable
  x y : Name
  m n : Mode
  μ ρ : Modality m n
  Γ Δ : Ctx m
  T S : Ty m


--------------------------------------------------
-- Definition of extractability for MSTT contexts and types at the
-- trivial mode

-- To make an MSTT context extractable, we need to provide an Agda
-- type and an isomorphism between that type and the context's
-- denotation as a presheaf over the trivial base category.
record ExtractableCtx (Γ : Ctx ★) : Set₁ where
  no-eta-equality
  field
    AgdaCtx : Set
    extract-ctx-iso : (⟦ Γ ⟧ctx M.⟨ tt ⟩) ↔ AgdaCtx

open ExtractableCtx {{...}} public

extract-ctx : (Γ : Ctx ★) → {{ExtractableCtx Γ}} → Set
extract-ctx Γ {{exΓ}} = AgdaCtx


-- The definition of extractability for MSTT types is more or less the
-- same as for contexts.
record ExtractableTy (T : Ty ★) : Set₁ where
  no-eta-equality
  field
    AgdaTy : Set
    extract-ty-iso-◇ : ((⟦ T ⟧ty {M.◇}) M.⟨ tt , tt ⟩) ↔ AgdaTy

  extract-ty-iso : {sΓ : SemCtx M.★} {γ : sΓ M.⟨ tt ⟩} →
                   ((⟦ T ⟧ty {sΓ}) M.⟨ tt , γ ⟩) ↔ AgdaTy
  extract-ty-iso = extract-ty-iso-◇ ↔-∘ M.closed-ty-cell-iso-◇ (ty-closed-natural T) _ _

  extract-ty-iso-transport : {sΓ : SemCtx M.★} {γ γ' : sΓ M.⟨ tt ⟩} (eγ : γ ≡ γ') →
                             (t : (⟦ T ⟧ty {sΓ}) M.⟨ tt , γ ⟩) →
                             Inverse.from extract-ty-iso (Inverse.to extract-ty-iso t) ≡ ⟦ T ⟧ty M.⟪ tt , trans (M.ctx-id sΓ) eγ ⟫ t
  extract-ty-iso-transport {sΓ} eγ t =
    trans (cong (Inverse.from (M.closed-ty-cell-iso-◇ (ty-closed-natural T) _ _)) (Inverse.strictlyInverseʳ extract-ty-iso-◇ _)) (
    trans (sym (M.ty-id ⟦ T ⟧ty)) (
    trans (M.naturality (M.from (M.closed-natural (ty-closed-natural T) (M.!◇ sΓ)))) (
    trans (cong (Inverse.from (M.closed-ty-cell-iso-◇ (ty-closed-natural T) _ _))
                (trans (M.ty-cong ⟦ T ⟧ty refl) (M.naturality (M.to (M.closed-natural (ty-closed-natural T) (M.!◇ sΓ)))))) (
    M.eq (M.isoʳ (M.closed-natural (ty-closed-natural T) (M.!◇ sΓ))) _))))

open ExtractableTy {{...}} public

extract-ty : (T : Ty ★) → {{ExtractableTy T}} → Set
extract-ty T {{exT}} = AgdaTy


--------------------------------------------------
-- Given an extractable context Γ and extractable type T, there is an
-- Agda isomorphism between SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty and
-- (extract-ctx Γ → extract-ctx T). However, this does not always give
-- us definitionally the extracted Agda term we expect (e.g. function
-- application is not necessarily extracted to application of an Agda
-- function). We therefore define a term to be extractable if we can
-- construct a function of type (extract-ctx Γ → extract-ty T) which
-- is pointwise propositionally equal to the function obtained from
-- the isomorphisms for Γ and T.

module ExtractSemTm
  {Γ : Ctx ★} {{_ : ExtractableCtx Γ}}
  {T : Ty ★} {{_ : ExtractableTy T}}
  where

  tm-extraction-setoid : Setoid _ _
  tm-extraction-setoid = extract-ctx Γ →-setoid extract-ty T

  extract-semtm : SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty → extract-ctx Γ → extract-ty T
  extract-semtm t =
    Inverse.to extract-ty-iso
    ∘ t M.⟨ tt ,_⟩'
    ∘ Inverse.from extract-ctx-iso

  extract-semtm-cong : {t1 t2 : SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty} → t1 M.≅ᵗᵐ t2 →
                       (γ : extract-ctx Γ) →
                       extract-semtm t1 γ ≡ extract-semtm t2 γ
  extract-semtm-cong 𝒆 γ = cong (Inverse.to extract-ty-iso) (M.eq 𝒆 _)

  embed-semtm : (extract-ctx Γ → extract-ty T) → SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty
  embed-semtm f M.⟨ x , γ ⟩' = Inverse.from extract-ty-iso (f (Inverse.to extract-ctx-iso γ))
  M.naturality (embed-semtm f) tt eγ =
    trans (M.naturality (M.from (M.closed-natural (ty-closed-natural T) (M.!◇ ⟦ Γ ⟧ctx))))
          (cong (M.func (M.from (M.closed-natural (ty-closed-natural T) (M.!◇ ⟦ Γ ⟧ctx))))
                (trans (M.strong-ty-id ⟦ T ⟧ty)
                       (cong (Inverse.from extract-ty-iso-◇ ∘ f ∘ Inverse.to extract-ctx-iso) (trans (sym (M.ctx-id ⟦ Γ ⟧ctx)) eγ))))

  embed-semtm-cong : {f g : extract-ctx Γ → extract-ty T} → ((γ : extract-ctx Γ) → f γ ≡ g γ) →
                     embed-semtm f M.≅ᵗᵐ embed-semtm g
  M.eq (embed-semtm-cong e) γ = cong (Inverse.from extract-ty-iso) (e _)

  extract-embed-semtm : (f : extract-ctx Γ → extract-ty T) (γ : extract-ctx Γ) →
                        extract-semtm (embed-semtm f) γ ≡ f γ
  extract-embed-semtm f γ =
    trans (Inverse.strictlyInverseˡ extract-ty-iso _) (cong f (Inverse.strictlyInverseˡ (extract-ctx-iso) γ))

  embed-extract-semtm : (t : SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty) → embed-semtm (extract-semtm t) M.≅ᵗᵐ t
  M.eq (embed-extract-semtm t) γ =
    trans (extract-ty-iso-transport (Inverse.strictlyInverseʳ extract-ctx-iso _) _) (M.naturality t tt _)

  extract-semtm-iso : Inverse (semtm-setoid ⟦ Γ ⟧ctx ⟦ T ⟧ty) tm-extraction-setoid
  Inverse.to extract-semtm-iso = extract-semtm
  Inverse.from extract-semtm-iso = embed-semtm
  Inverse.to-cong extract-semtm-iso = extract-semtm-cong
  Inverse.from-cong extract-semtm-iso = embed-semtm-cong
  Inverse.inverse extract-semtm-iso =
    [ strictlyInverseˡ⇒inverseˡ (semtm-setoid ⟦ Γ ⟧ctx ⟦ T ⟧ty) tm-extraction-setoid {f⁻¹ = embed-semtm} extract-semtm-cong extract-embed-semtm
    , strictlyInverseʳ⇒inverseʳ (semtm-setoid ⟦ Γ ⟧ctx ⟦ T ⟧ty) tm-extraction-setoid embed-semtm-cong embed-extract-semtm
    ]


open ExtractSemTm public


record ExtractableTm {Γ : Ctx ★} {{_ : ExtractableCtx Γ}} {T : Ty ★} {{_ : ExtractableTy T}} (t : Tm Γ T) : Set where
  no-eta-equality
  field
    extracted-tm : extract-ctx Γ → extract-ty T
    extract-tm-semtm : (γ : extract-ctx Γ) → extracted-tm γ ≡ extract-semtm ⟦ t ⟧tm γ

open ExtractableTm {{...}} public

extract-tm : {Γ : Ctx ★} {{_ : ExtractableCtx Γ}}
             {T : Ty ★} {{_ : ExtractableTy T}}
             (t : Tm Γ T) → {{ExtractableTm t}} →
             extract-ctx Γ → extract-ty T
extract-tm t = extracted-tm


--------------------------------------------------
-- Instances of extractability for many of the MSTT type formers and
-- context constructors

instance
  ◇-extractable : ExtractableCtx ◇
  ExtractableCtx.AgdaCtx ◇-extractable = ⊤
  ExtractableCtx.extract-ctx-iso ◇-extractable =
    mk↔ₛ′ (λ _ → tt) (λ _ → tt) (λ _ → refl) (λ _ → refl)

  ,,-extractable : {Γ : Ctx ★} → {{ExtractableCtx Γ}} →
                   {T : Ty ★} → {{ExtractableTy T}} →
                   {x : Name} →
                   ExtractableCtx (Γ ,, 𝟙 ∣ x ∈ T)
  ExtractableCtx.AgdaCtx (,,-extractable {Γ} {T}) = extract-ctx Γ × extract-ty T
  ExtractableCtx.extract-ctx-iso (,,-extractable {Γ} {T}) = mk↔ₛ′
    (map (Inverse.to extract-ctx-iso) (Inverse.to extract-ty-iso))
    (map (Inverse.from extract-ctx-iso) (Inverse.from extract-ty-iso))
    (λ _ → cong₂ [_,_] (Inverse.strictlyInverseˡ (extract-ctx-iso {Γ}) _) (Inverse.strictlyInverseˡ extract-ty-iso _))
    (λ _ → M.to-Σ-ty-eq ⟦ T ⟧ty (Inverse.strictlyInverseʳ extract-ctx-iso _)
                                (trans (cong (⟦ T ⟧ty M.⟪ tt , _ ⟫_) (extract-ty-iso-transport (sym (Inverse.strictlyInverseʳ extract-ctx-iso _)) _))
                                       (trans (sym (M.ty-comp ⟦ T ⟧ty)) (M.strong-ty-id ⟦ T ⟧ty))))

  lock𝟙-extractable : {Γ : Ctx ★} → {{ExtractableCtx Γ}} →
                      ExtractableCtx (Γ ,lock⟨ 𝟙 ⟩)
  ExtractableCtx.AgdaCtx (lock𝟙-extractable {Γ}) = extract-ctx Γ
  ExtractableCtx.extract-ctx-iso (lock𝟙-extractable {Γ}) = extract-ctx-iso {Γ}

  Nat'-extractable : ExtractableTy Nat'
  ExtractableTy.AgdaTy Nat'-extractable = ℕ
  ExtractableTy.extract-ty-iso-◇ Nat'-extractable = ↔-id ℕ

  Bool'-extractable : ExtractableTy Bool'
  ExtractableTy.AgdaTy Bool'-extractable = Bool
  ExtractableTy.extract-ty-iso-◇ Bool'-extractable = ↔-id Bool

to-★-pshfun-◇ : {sT sS : SemTy {M.★} M.◇} →
                (sT M.⟨ tt , tt ⟩ → sS M.⟨ tt , tt ⟩) →
                M.PshFun sT sS tt tt
to-★-pshfun-◇ f M.$⟨ _ , _ ⟩ t = f t
M.naturality (to-★-pshfun-◇ {sT} {sS} f) = trans (cong f (M.strong-ty-id sT)) (sym (M.strong-ty-id sS))

instance
  ⇛-extractable : {T S : Ty ★} → {{ExtractableTy T}} → {{ExtractableTy S}} →
                  ExtractableTy (T ⇛ S)
  ExtractableTy.AgdaTy (⇛-extractable {T} {S}) = extract-ty T → extract-ty S
  ExtractableTy.extract-ty-iso-◇ (⇛-extractable {T} {S}) = mk↔ₛ′
    (λ psh-f t → Inverse.to (extract-ty-iso-◇ {S}) (psh-f M.$⟨ tt , refl ⟩ Inverse.from (extract-ty-iso-◇ {T}) t))
    (λ f → to-★-pshfun-◇ (Inverse.from (extract-ty-iso-◇ {S}) ∘ f ∘ Inverse.to (extract-ty-iso-◇ {T})))
    (λ f → funext λ _ → trans (Inverse.strictlyInverseˡ (extract-ty-iso-◇ {S}) _) (cong f (Inverse.strictlyInverseˡ (extract-ty-iso-◇ {T}) _)))
    (λ psh-f → M.to-pshfun-eq (λ { _ refl _ → trans (Inverse.strictlyInverseʳ (extract-ty-iso-◇ {S}) _)
                                                    (cong (psh-f M.$⟨ tt , refl ⟩_) (Inverse.strictlyInverseʳ (extract-ty-iso-◇ {T}) _)) }))

  ⊠-extractable : {T S : Ty ★} → {{ExtractableTy T}} → {{ExtractableTy S}} →
                 ExtractableTy (T ⊠ S)
  ExtractableTy.AgdaTy (⊠-extractable {T} {S}) = extract-ty T × extract-ty S
  ExtractableTy.extract-ty-iso-◇ (⊠-extractable {T} {S}) = extract-ty-iso-◇ {T} ×-↔ extract-ty-iso-◇ {S}

  mod𝟙-extractable : {T : Ty ★} → {{ExtractableTy T}} → ExtractableTy ⟨ 𝟙 ∣ T ⟩
  ExtractableTy.AgdaTy (mod𝟙-extractable {T}) = extract-ty T
  ExtractableTy.extract-ty-iso-◇ (mod𝟙-extractable {T}) = extract-ty-iso-◇ {T}


--------------------------------------------------
-- Instances for extraction of terms

-- Convenient function to extract terms that live in the empty context.
extract-tm-◇ : {T : Ty ★} → {{_ : ExtractableTy T}}
               (t : Tm ◇ T) → {{ExtractableTm t}} → extract-ty T
extract-tm-◇ t = extract-tm t tt


data Only𝟙 : LockTele ★ ★ → Set where
  instance
    ◇-only𝟙 : Only𝟙 ◇
    lock𝟙-only𝟙 : {Λ : LockTele ★ ★} → {{Only𝟙 Λ}} → Only𝟙 (lock⟨ 𝟙 ⟩, Λ)

unlock𝟙-only𝟙 : {Λ : LockTele ★ ★} → Only𝟙 (lock⟨ 𝟙 ⟩, Λ) → Only𝟙 Λ
unlock𝟙-only𝟙 (lock𝟙-only𝟙 {{ol𝟙}}) = ol𝟙

only𝟙-locks : {Λ : LockTele ★ ★} → Only𝟙 Λ → TwoCell 𝟙 (locksˡᵗ Λ)
only𝟙-locks ◇-only𝟙 = id-cell
only𝟙-locks (lock𝟙-only𝟙 {{ol𝟙}}) = id-cell {μ = 𝟙} ⓣ-hor only𝟙-locks ol𝟙

only𝟙-sem : {Λ : LockTele ★ ★} → Only𝟙 Λ →
            ⟦ locksˡᵗ Λ ⟧mod DRA.≅ᵈ DRA.𝟙
only𝟙-sem ◇-only𝟙 = DRA.reflᵈ
only𝟙-sem (lock𝟙-only𝟙 {Λ} {{ol𝟙}}) =
  DRA.transᵈ (⟦ⓜ⟧-sound 𝟙 (locksˡᵗ Λ)) (DRA.transᵈ (DRA.𝟙-unitˡ _) (only𝟙-sem ol𝟙))

only𝟙-sem-◇ : (ol𝟙 : Only𝟙 ◇) → DRA.from (only𝟙-sem ol𝟙) DRA.≅ᵗᶜ DRA.id-cell
only𝟙-sem-◇ ◇-only𝟙 = DRA.reflᵗᶜ

only𝟙-sem-unlock𝟙 : {Λ : LockTele ★ ★} (ol𝟙 : Only𝟙 (lock⟨ 𝟙 ⟩, Λ)) →
                    DRA.from (only𝟙-sem (unlock𝟙-only𝟙 ol𝟙))
                    DRA.ⓣ-vert DRA.from (DRA.𝟙-unitˡ _)
                    DRA.ⓣ-vert DRA.from (⟦ⓜ⟧-sound 𝟙 (locksˡᵗ Λ))
                      DRA.≅ᵗᶜ
                    DRA.from (only𝟙-sem ol𝟙)
only𝟙-sem-unlock𝟙 (lock𝟙-only𝟙 {{ol𝟙}}) = DRA.reflᵗᶜ

only𝟙-sem-only𝟙-locks : {Λ : LockTele ★ ★} (ol𝟙 : Only𝟙 Λ) →
                        DRA.from (only𝟙-sem ol𝟙) DRA.ⓣ-vert ⟦ only𝟙-locks ol𝟙 ⟧two-cell
                          DRA.≅ᵗᶜ
                        DRA.id-cell
only𝟙-sem-only𝟙-locks ◇-only𝟙 = DRA.transᵗᶜ DRA.ⓣ-vert-unitˡ ⟦id-cell⟧-sound
only𝟙-sem-only𝟙-locks (lock𝟙-only𝟙 {Λ} {{ol𝟙}}) =
  DRA.transᵗᶜ (DRA.transᵗᶜ DRA.ⓣ-vert-assoc (DRA.ⓣ-vert-congʳ (⟦ⓜ⟧-sound-natural id-cell (only𝟙-locks ol𝟙)))) (
  DRA.transᵗᶜ (DRA.transᵗᶜ (DRA.symᵗᶜ DRA.ⓣ-vert-assoc) (DRA.ⓣ-vert-congˡ DRA.ⓣ-vert-assoc)) (
  DRA.transᵗᶜ (DRA.ⓣ-vert-congˡ (DRA.ⓣ-vert-congʳ (DRA.transᵗᶜ (DRA.ⓣ-vert-congʳ (DRA.ⓣ-hor-congˡ ⟦id-cell⟧-sound)) (DRA.symᵗᶜ (DRA.𝟙-unitˡ-natural-from _))))) (
  DRA.transᵗᶜ (DRA.ⓣ-vert-congˡ (DRA.symᵗᶜ DRA.ⓣ-vert-assoc)) (DRA.transᵗᶜ (DRA.ⓣ-vert-congˡ (
    DRA.transᵗᶜ (DRA.ⓣ-vert-congˡ (only𝟙-sem-only𝟙-locks ol𝟙)) DRA.ⓣ-vert-unitˡ))
  (DRA.transᵗᶜ (DRA.ⓣ-vert-congˡ DRA.𝟙-unitˡ-unitʳ-from) (DRA.isoʳ (DRA.𝟙-unitʳ DRA.𝟙)))))))


data ExtractableVar {x : Name} {T : Ty ★} : {Γ : Ctx ★} {Λ : LockTele ★ ★} → Var x T Γ Λ → Set₁ where
  instance
    vzero-extr : {Γ : Ctx ★} {{_ : ExtractableCtx Γ}}
                 {Λ : LockTele ★ ★} {{ol𝟙 : Only𝟙 Λ}} →
                 ExtractableVar {Γ = Γ ,, 𝟙 ∣ x ∈ T} {Λ} (vzero (only𝟙-locks ol𝟙))
    vsuc-extr : {Γ : Ctx ★}
                {Λ : LockTele ★ ★} {y : Name}
                {S : Ty ★} {{_ : ExtractableTy S}}
                {v : Var x T Γ Λ} → {{ExtractableVar v}} →
                ExtractableVar {Γ = Γ ,, 𝟙 ∣ y ∈ S} (vsuc v)
    vlock-extr : {Γ : Ctx ★} {Λ : LockTele ★ ★} →
                 {v : Var x T Γ (lock⟨ 𝟙 ⟩, Λ)} → {{ExtractableVar v}} →
                 ExtractableVar (vlock v)

extractable-var-ctx : {x : Name} {T : Ty ★} {{_ : ExtractableTy T}}
                      {Γ : Ctx ★} {Λ : LockTele ★ ★}
                      {v : Var x T Γ Λ} → ExtractableVar v → ExtractableCtx Γ
extractable-var-ctx (vzero-extr {{exΓ}}) = ,,-extractable
extractable-var-ctx (vsuc-extr {v = v} {{exv}}) = ,,-extractable {{extractable-var-ctx {v = v} exv}}
extractable-var-ctx (vlock-extr {{exv}}) = lock𝟙-extractable {{extractable-var-ctx exv}}

extractable-var-only𝟙 : {x : Name} {T : Ty ★} {{_ : ExtractableTy T}}
                        {Γ : Ctx ★} {Λ : LockTele ★ ★}
                        {v : Var x T Γ Λ} → ExtractableVar v →
                        Only𝟙 Λ
extractable-var-only𝟙 (vzero-extr {{ol𝟙 = ol𝟙}}) = ol𝟙
extractable-var-only𝟙 (vsuc-extr {v = _} {{exv}}) = extractable-var-only𝟙 exv
extractable-var-only𝟙 (vlock-extr {v = _} {{exv}}) = unlock𝟙-only𝟙 (extractable-var-only𝟙 exv)

extract-var : {x : Name} {T : Ty ★} {{_ : ExtractableTy T}}
              {Γ : Ctx ★} {Λ : LockTele ★ ★}
              (v : Var x T Γ Λ) {{exv : ExtractableVar v}} →
              extract-ctx Γ {{extractable-var-ctx exv}} → extract-ty T
extract-var (vzero _) {{ vzero-extr }} γ = proj₂ γ
extract-var (vsuc v)  {{ vsuc-extr  }} γ = extract-var v (proj₁ γ)
extract-var (vlock v) {{ vlock-extr }} γ = extract-var v γ

extract-var-iso : {x : Name} {T : Ty ★} {{_ : ExtractableTy T}}
                  {Γ : Ctx ★} {Λ : LockTele ★ ★}
                  (v : Var x T Γ Λ) {{exv : ExtractableVar v}} →
                  (γ : extract-ctx Γ {{extractable-var-ctx exv}}) →
                  extract-var v γ
                    ≡
                  Inverse.to (extract-ty-iso {T}) (
                    ⟦ v ⟧var M.⟨ tt , M.func (DRA.key-subst (DRA.from (only𝟙-sem (extractable-var-only𝟙 exv)))) (
                                      Inverse.from (extract-ctx-iso {Γ} {{extractable-var-ctx exv}}) γ) ⟩')
extract-var-iso {T = T} {{exT}} {Λ = Λ} .(vzero _) {{ vzero-extr {Γ = Γ} {{ol𝟙 = ol𝟙}} }} [ γ , t ] = sym (
  trans (cong (Inverse.to (extract-ty-iso-◇ {T})) (
    trans (sym (M.eq (M.to-eq (M.closed-subst-eq (ty-closed-natural T) (M.◇-terminal _ _ (M.!◇ _ M.⊚ _ M.⊚ _)))) _)) (
    trans (cong (⟦ T ⟧ty M.⟪ _ , _ ⟫_) (
      trans (sym (M.eq (M.to-eq (M.closed-⊚ (ty-closed-natural T) _ _)) _)) (
      trans (cong (M.func (M.to (M.closed-natural (ty-closed-natural T) _))) (M.eq (M.isoˡ (M.closed-natural (ty-closed-natural T) _)) _)) (
      trans (sym (M.eq (M.to-eq (M.closed-⊚ (ty-closed-natural T) _ _)) _)) (
      cong (M.func (M.to (M.closed-natural (ty-closed-natural T) _))) (M.eq (M.isoˡ (M.closed-natural (ty-closed-natural T) _)) _)))))) (
    trans (cong (⟦ T ⟧ty M.⟪ _ , _ ⟫_) (cong (M.func (M.to (M.closed-natural (ty-closed-natural T) _))) (
      trans (sym (dcong {A = _} proj₂ (sym (M.eq (DRA.key-subst-eq (only𝟙-sem-only𝟙-locks ol𝟙))
                                           [ Inverse.from (extract-ctx-iso {Γ}) γ , Inverse.from (extract-ty-iso {T}) t ])))) (
      sym (M.ty-ctx-subst-prop-subst (⟦ T ⟧ty M.[ M.π {T = ⟦ T ⟧ty} ]) (sym (M.eq (DRA.key-subst-eq (only𝟙-sem-only𝟙-locks ol𝟙)) _))))))) (
    trans (cong (⟦ T ⟧ty M.⟪ tt , refl ⟫_) (sym (M.naturality (M.to (M.closed-natural (ty-closed-natural T) _))))) (
    trans (M.ty-cong-2-1 ⟦ T ⟧ty refl) (M.ty-id ⟦ T ⟧ty))))))) (
  Inverse.strictlyInverseˡ (extract-ty-iso {T} {⟦ Γ ⟧ctx} {Inverse.from (extract-ctx-iso {Γ}) γ}) t))
extract-var-iso {T = T} {{exT}} {Λ = Λ} .(vsuc v) {{ vsuc-extr {Γ = Γ} {S = S} {v = v} {{exv}} }} [ γ , s ] =
  trans (extract-var-iso v {{exv}} γ) (sym (
    trans (cong (λ z → Inverse.to (extract-ty-iso {T} {{exT}}) (
                         M.func (M.from (M.closed-natural (ty-closed-natural T) (DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (M.π {T = ⟦ S ⟧ty})))) z))
                (sym (M.naturality ⟦ v ⟧var tt (
                     trans (M.ctx-id (DRA.lock ⟦ locksˡᵗ Λ ⟧mod ⟦ Γ ⟧ctx))
                           (M.eq (DRA.key-subst-natural (DRA.from (only𝟙-sem (extractable-var-only𝟙 exv)))) _))))) (
    cong (Inverse.to (extract-ty-iso-◇ {T} {{exT}})) (
      trans (sym (M.eq (M.to-eq (M.closed-subst-eq (ty-closed-natural T) (M.◇-terminal _ _ _))) _)) (
      trans (cong (⟦ T ⟧ty M.⟪ tt , refl ⟫_) (
        trans (sym (M.eq (M.to-eq (M.closed-⊚ (ty-closed-natural T) _ _)) _)) (
        cong (M.func (M.to (M.closed-natural (ty-closed-natural T) _))) (M.eq (M.isoˡ (M.closed-natural (ty-closed-natural T) _)) _)))) (
      trans (cong (⟦ T ⟧ty M.⟪ _ , _ ⟫_) (sym (M.naturality (M.to (M.closed-natural (ty-closed-natural T) (M.!◇ _)))))) (
      trans (M.ty-cong-2-1 ⟦ T ⟧ty refl) (M.ty-id ⟦ T ⟧ty))))))))
extract-var-iso {T = T} {Γ} {Λ} .(vlock v) {{ vlock-extr {v = v} {{exv}} }} γ =
  trans (extract-var-iso v {{exv}} γ) (sym (cong (Inverse.to (extract-ty-iso-◇ {T})) (
    trans (sym (M.eq (M.to-eq (M.closed-subst-eq (ty-closed-natural T) (M.◇-terminal _ _ _))) _)) (
    trans (cong (⟦ T ⟧ty M.⟪ tt , refl ⟫_) (
      trans (sym (M.eq (M.to-eq (M.closed-⊚ (ty-closed-natural T) _ _)) _)) (
      cong (M.func (M.to (M.closed-natural (ty-closed-natural T) _))) (M.eq (M.isoˡ (M.closed-natural (ty-closed-natural T) _)) _)))) (
    trans (trans (M.ty-cong ⟦ T ⟧ty refl) (M.naturality (M.to (M.closed-natural (ty-closed-natural T) _)))) (
    cong (M.func (M.to (M.closed-natural (ty-closed-natural T) _))) (
      M.naturality ⟦ v ⟧var tt (trans (M.ctx-id (DRA.lock ⟦ Modality.𝟙 ⓜ locksˡᵗ Λ ⟧mod ⟦ Γ ⟧ctx))
                                      (M.eq (DRA.key-subst-eq (only𝟙-sem-unlock𝟙 (extractable-var-only𝟙 exv))) _)))))))))

instance
  var-extractable : {x : Name} {T : Ty ★} {{_ : ExtractableTy T}}
                    {Γ : Ctx ★} {v : Var x T Γ ◇} {{exv : ExtractableVar v}} →
                    ExtractableTm {{extractable-var-ctx exv}} (var' x {v})
  extracted-tm {{var-extractable {v = v}}} = extract-var v
  extract-tm-semtm {{var-extractable {T = T} {Γ = Γ} {v = v} {{exv}}}} γ =
    trans (extract-var-iso v γ) (
    trans (cong (Inverse.to (extract-ty-iso-◇ {T})) (
      trans (sym (M.strong-ty-id ⟦ T ⟧ty)) (
      M.naturality (M.to (M.closed-natural (ty-closed-natural T) _))))) (
    cong (Inverse.to (extract-ty-iso {T})) (M.naturality ⟦ v ⟧var tt (
      trans (M.ctx-id ⟦ Γ ⟧ctx) (M.eq (DRA.key-subst-eq (only𝟙-sem-◇ (extractable-var-only𝟙 exv))) _)))))

instance
  mod𝟙tm-extractable : {Γ : Ctx ★} {{_ : ExtractableCtx Γ}}
                       {T : Ty ★} {{_ : ExtractableTy T}}
                       {t : Tm (Γ ,lock⟨ 𝟙 ⟩) T} → {{ExtractableTm t}} →
                       ExtractableTm (mod⟨ 𝟙 ⟩ t)
  extracted-tm {{mod𝟙tm-extractable {t = t}}} = extract-tm t
  extract-tm-semtm {{mod𝟙tm-extractable {t = t}}} = extract-tm-semtm {t = t}

  ∙-extractable : {Γ : Ctx ★} {{_ : ExtractableCtx Γ}}
                  {T S : Ty ★} {{_ : ExtractableTy T}} {{_ : ExtractableTy S}}
                  {f : Tm Γ (T ⇛ S)} {{_ : ExtractableTm f}}
                  {t : Tm (Γ ,lock⟨ 𝟙 ⟩) T} {{_ : ExtractableTm t}} →
                  ExtractableTm (f ∙ t)
  extracted-tm {{∙-extractable {f = f} {t = t}}} γ = extract-tm f γ (extract-tm t γ)
  extract-tm-semtm {{∙-extractable {Γ} {T} {S} {f = f} {t = t}}} γ =
    trans (cong-app (extract-tm-semtm {t = f} γ) _) (
    trans (cong (extract-semtm {Γ = Γ} {T = T ⇛ S} ⟦ f ⟧tm γ) (extract-tm-semtm {t = t} γ)) (
      cong (Inverse.to (extract-ty-iso-◇ {T = S})) (
      trans (M.strong-ty-id ⟦ S ⟧ty) (
      trans (cong (M.func (M.to (M.closed-natural (ty-closed-natural S) _))) (
        trans (cong (λ x → (⟦ f ⟧tm M.⟨ tt , _ ⟩') M.$⟨ tt , _ ⟩ x) (
          trans (sym (M.naturality (M.from (M.closed-natural (ty-closed-natural T) (M.!◇ ⟦ Γ ⟧ctx))))) (
          cong (⟦ T ⟧ty M.⟪ tt , refl ⟫_) (Inverse.strictlyInverseʳ (extract-ty-iso {T = T}) _)))) (
        trans (M.$-cong (⟦ f ⟧tm M.⟨ tt , _ ⟩') refl) (
        M.naturality (⟦ f ⟧tm M.⟨ tt , _ ⟩'))))) (
      trans (sym (M.naturality (M.to (M.closed-natural (ty-closed-natural S) (M.!◇ ⟦ Γ ⟧ctx))))) (
      M.strong-ty-id ⟦ S ⟧ty))))))

global-extract : {Γ : Ctx ★} {{_ : ExtractableCtx Γ}}
                 {T : Ty ★} {{_ : ExtractableTy T}} (t : Tm ◇ T) →
                 extract-ctx Γ → extract-ty T
global-extract {T = T} t γ = extract-semtm {Γ = ◇} {T = T} ⟦ t ⟧tm tt

global-extract-proof : {Γ : Ctx ★} {{_ : ExtractableCtx Γ}}
                       {T : Ty ★} {{_ : ExtractableTy T}} (t : Tm ◇ T) →
                       (γ : extract-ctx Γ) (def-name : DefName) →
                       global-extract {Γ} t γ
                         ≡
                       extract-semtm {Γ = Γ} {T = T} ⟦ global-def {Γ = Γ} def-name {t} ⟧tm γ
global-extract-proof {Γ} {T = T} t γ def-name =
  cong (Inverse.to (extract-ty-iso-◇ {T})) (
    trans (sym (M.eq (M.to-eq (M.closed-subst-eq (ty-closed-natural T) (M.◇-terminal M.◇ (M.!◇ M.◇) (M.id-subst M.◇)))) _)) (
    trans (M.strong-ty-id ⟦ T ⟧ty) (
    trans (M.eq (M.to-eq (M.closed-id (ty-closed-natural T))) _) (
    sym (M.eq (M.isoˡ (M.closed-natural (ty-closed-natural T) (M.!◇ ⟦ Γ ⟧ctx))) _)))))



instance
  global-def-extractable : {Γ : Ctx ★} {{_ : ExtractableCtx Γ}}
                           {T : Ty ★} {{_ : ExtractableTy T}}
                           {def-name : DefName} {t : Tm ◇ T} →
                           ExtractableTm {Γ = Γ} (global-def def-name {t})
  extracted-tm {{global-def-extractable {Γ} {T = T} {t = t}}} γ = global-extract {Γ} t γ
  extract-tm-semtm {{global-def-extractable {Γ} {T = T} {def-name} {t}}} γ = global-extract-proof {Γ} t γ def-name
