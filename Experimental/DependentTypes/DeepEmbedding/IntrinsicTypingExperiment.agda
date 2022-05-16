module Experimental.DependentTypes.DeepEmbedding.IntrinsicTypingExperiment where

open import Relation.Binary.PropositionalEquality
open import Function.Nary.NonDependent

open import Model.CwF-Structure as M hiding (◇)
open import Model.BaseCategory
open import Model.Type.Discrete

import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M


-- Intrinsically-typed approach + interpretation in the model (trivial base category)
data CtxExpr : Set
data TyExpr : CtxExpr → Set
data TmExpr : (Γ : CtxExpr) → TyExpr Γ → Set

private variable
  Γ : CtxExpr

data CtxExpr where
  ◇ : CtxExpr
  _,_ : (Γ : CtxExpr) → TyExpr Γ → CtxExpr

data TyExpr where
  Bool : TyExpr Γ
  Id : {T : TyExpr Γ} → (t s : TmExpr Γ T) → TyExpr Γ

data TmExpr where
  true false : TmExpr Γ Bool
  if : {T : TyExpr Γ} → TmExpr Γ Bool → TmExpr Γ T → TmExpr Γ T → TmExpr Γ T
  refl : {T : TyExpr Γ} → (t : TmExpr Γ T) → TmExpr Γ (Id t t)

interp-ctx : CtxExpr → Ctx ★
interp-ty : (Γ : CtxExpr) → TyExpr Γ → Ty (interp-ctx Γ)
interp-tm : (Γ : CtxExpr) (T : TyExpr Γ) → TmExpr Γ T → Tm (interp-ctx Γ) (interp-ty Γ T)

interp-ctx ◇ = M.◇
interp-ctx (Γ , T) = interp-ctx Γ ,, interp-ty Γ T

interp-ty Γ Bool = Bool'
interp-ty Γ (Id t s) = M.Id (interp-tm Γ _ t) (interp-tm Γ _ s)

interp-tm Γ .Bool true = true'
interp-tm Γ .Bool false = false'
interp-tm Γ T (if c t f) = if' (interp-tm Γ Bool c) then' (interp-tm Γ T t) else' (interp-tm Γ T f)
interp-tm Γ .(Id t t) (refl t) = M.refl' (interp-tm Γ _ t)


-- Extrinsically-typed approach + translation to intrinsically-typed syntax
data CtxExpr' : Set
data TyExpr' : Set
data TmExpr' : Set

data CtxExpr' where
  ◇ : CtxExpr'
  _,_ : CtxExpr' → TyExpr' → CtxExpr'

data TyExpr' where
  Bool : TyExpr'
  Id : (T : TyExpr') → (t s : TmExpr') → TyExpr'

data TmExpr' where
  true false : TmExpr'
  if : TmExpr' → TmExpr' → TmExpr' → TmExpr'
  refl : (t : TmExpr') → TmExpr'


data ⊢ctx : CtxExpr' → Set
data _⊢ty_ : CtxExpr' → TyExpr' → Set
data _⊢_∈_ : CtxExpr' → TmExpr' → TyExpr' → Set

data ⊢ctx where
  d-◇ : ⊢ctx ◇
  d-, : ∀ {Γ T} → ⊢ctx Γ → Γ ⊢ty T → ⊢ctx (Γ , T)

data _⊢ty_ where
  d-Bool : ∀ {Γ} → ⊢ctx Γ → Γ ⊢ty Bool
  d-Id : ∀ {Γ T t s} → ⊢ctx Γ → Γ ⊢ty T → Γ ⊢ t ∈ T → Γ ⊢ s ∈ T → Γ ⊢ty Id T t s

data _⊢_∈_ where
  d-true : ∀ {Γ} → ⊢ctx Γ → Γ ⊢ true ∈ Bool
  d-false : ∀ {Γ} → ⊢ctx Γ → Γ ⊢ false ∈ Bool
  d-if : ∀ {Γ T c t f} → ⊢ctx Γ → Γ ⊢ty T → Γ ⊢ c ∈ Bool → Γ ⊢ t ∈ T → Γ ⊢ f ∈ T → Γ ⊢ if c t f ∈ T
  d-refl : ∀ {Γ T t} → ⊢ctx Γ → Γ ⊢ty T → Γ ⊢ t ∈ T → Γ ⊢ refl t ∈ Id T t t

ctx-deriv-irr : ∀ {Γ} (d1 d2 : ⊢ctx Γ) → d1 ≡ d2
ty-deriv-irr : ∀ {Γ T} (d1 d2 : Γ ⊢ty T) → d1 ≡ d2
tm-deriv-irr : ∀ {Γ T t} (d1 d2 : Γ ⊢ t ∈ T) → d1 ≡ d2

ctx-deriv-irr d-◇ d-◇ = refl
ctx-deriv-irr (d-, dΓ1 dT1) (d-, dΓ2 dT2) = cong₂ d-, (ctx-deriv-irr dΓ1 dΓ2) (ty-deriv-irr dT1 dT2)

ty-deriv-irr (d-Bool dΓ1) (d-Bool dΓ2) = cong d-Bool (ctx-deriv-irr dΓ1 dΓ2)
ty-deriv-irr (d-Id dΓ1 dT1 dt1 ds1) (d-Id dΓ2 dT2 dt2 ds2) = congₙ 4 d-Id (ctx-deriv-irr dΓ1 dΓ2)
                                                                          (ty-deriv-irr dT1 dT2)
                                                                          (tm-deriv-irr dt1 dt2)
                                                                          (tm-deriv-irr ds1 ds2)

tm-deriv-irr (d-true dΓ1) (d-true dΓ2) = cong d-true (ctx-deriv-irr dΓ1 dΓ2)
tm-deriv-irr (d-false dΓ1) (d-false dΓ2) = cong d-false (ctx-deriv-irr dΓ1 dΓ2)
tm-deriv-irr (d-if dΓ1 dT1 dc1 dt1 df1) (d-if dΓ2 dT2 dc2 dt2 df2) = congₙ 5 d-if (ctx-deriv-irr dΓ1 dΓ2)
                                                                                  (ty-deriv-irr dT1 dT2)
                                                                                  (tm-deriv-irr dc1 dc2)
                                                                                  (tm-deriv-irr dt1 dt2)
                                                                                  (tm-deriv-irr df1 df2)
tm-deriv-irr (d-refl dΓ1 dT1 dt1) (d-refl dΓ2 dT2 dt2) = congₙ 3 d-refl (ctx-deriv-irr dΓ1 dΓ2)
                                                                        (ty-deriv-irr dT1 dT2)
                                                                        (tm-deriv-irr dt1 dt2)

translate-ctx : {Γ : CtxExpr'} → ⊢ctx Γ → CtxExpr
translate-ty : {Γ : CtxExpr'} {T : TyExpr'} → (dΓ : ⊢ctx Γ) → Γ ⊢ty T → TyExpr (translate-ctx dΓ)
translate-tm : {Γ : CtxExpr'} {T : TyExpr'} {t : TmExpr'} →
               (dΓ : ⊢ctx Γ) (dT : Γ ⊢ty T) → Γ ⊢ t ∈ T →
               TmExpr (translate-ctx dΓ) (translate-ty dΓ dT)

translate-ctx d-◇ = ◇
translate-ctx (d-, dΓ dT) = translate-ctx dΓ , translate-ty dΓ dT

translate-ty dΓ (d-Bool _) = Bool
translate-ty dΓ (d-Id _ dT dt ds) = Id (translate-tm dΓ dT dt) (translate-tm dΓ dT ds)

translate-tm dΓ (d-Bool _) (d-true _) = true
translate-tm dΓ (d-Bool _) (d-false _) = false
translate-tm dΓ dT (d-if dΓ' _ dc dt df) = if (translate-tm dΓ (d-Bool dΓ') dc) (translate-tm dΓ dT dt) (translate-tm dΓ dT df)
translate-tm dΓ (d-Id _ dT dt1 dt2) (d-refl _ _ dt) = subst (λ - → TmExpr (translate-ctx dΓ) (Id (translate-tm dΓ dT dt1) (translate-tm dΓ dT -)))
                                                            (tm-deriv-irr dt1 dt2)
                                                            (refl (translate-tm dΓ dT dt1))


-- Direct interpretation of extrinsically-typed syntax in the model also seems to work.
--  -> Probably an indication that this example has been oversimplified (no interesting equality).
interp-ctx' : {Γ : CtxExpr'} → ⊢ctx Γ → Ctx ★
interp-ty' : {Γ : CtxExpr'} {T : TyExpr'} → (dΓ : ⊢ctx Γ) → Γ ⊢ty T → Ty (interp-ctx' dΓ)
interp-tm' : {Γ : CtxExpr'} {T : TyExpr'} {t : TmExpr'} →
             (dΓ : ⊢ctx Γ) (dT : Γ ⊢ty T) → Γ ⊢ t ∈ T →
             Tm (interp-ctx' dΓ) (interp-ty' dΓ dT)

interp-ctx' d-◇ = M.◇
interp-ctx' (d-, dΓ dT) = interp-ctx' dΓ ,, interp-ty' dΓ dT

interp-ty' dΓ (d-Bool _) = Bool'
interp-ty' dΓ (d-Id _ dT dt ds) = M.Id (interp-tm' dΓ dT dt) (interp-tm' dΓ dT ds)

interp-tm' dΓ (d-Bool _) (d-true _) = true'
interp-tm' dΓ (d-Bool _) (d-false _) = false'
interp-tm' dΓ dT (d-if dΓ' _ dc dt df) = if' (interp-tm' dΓ (d-Bool dΓ) dc) then' (interp-tm' dΓ dT dt) else' (interp-tm' dΓ dT df)
interp-tm' dΓ (d-Id _ dT dt1 dt2) (d-refl _ _ _) = subst (λ - → Tm (interp-ctx' dΓ) (M.Id (interp-tm' dΓ dT dt1) (interp-tm' dΓ dT -)))
                                                         (tm-deriv-irr dt1 dt2)
                                                         (M.refl' (interp-tm' dΓ dT dt1))
