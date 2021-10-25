module Experimental.DependentTypes.DeepEmbedding.AlternativeDelay where

open import Level
open import Data.String
open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory as M
open import Model.CwF-Structure as M hiding (_,,_)
open import Model.Type.Discrete as M
open import Model.Type.Function as M hiding (_⇛_)
open import Model.Type.Product as M hiding (_⊠_)

import Experimental.DependentTypes.Model.IdentityType
module M-id = Experimental.DependentTypes.Model.IdentityType.Alternative1
open M-id hiding (Id)

open import Experimental.DependentTypes.DeepEmbedding.Syntax
-- open import MSTT.TCMonad

private
  variable
    ℓ ℓ′ : Level
    A B : Set ℓ

data TCM (A : Set ℓ) : Set ℓ
record TCMThunk (A : Set ℓ) : Set ℓ where
  coinductive
  field force : TCM A

data TCM A where
  type-error : String → TCM A
  ok : A → TCM A
  delay : TCMThunk A → TCM A

return : {A : Set ℓ} → A → TCM A
return = ok


data HasRes {ℓ} {A : Set ℓ} : TCM A → A → Set ℓ where
  here : {v : A} {m : TCM A} → m ≡ ok v → HasRes m v
  next : {v : A} {m : TCMThunk A} → HasRes (TCMThunk.force m) v → HasRes (delay m) v

_t>>=p_ : (m : TCMThunk A) → (∀ v → HasRes (TCMThunk.force m) v → TCM B) → TCMThunk B
_>>=p_ : (m : TCM A) → (∀ v → HasRes m v → TCM B) → TCM B
type-error x >>=p k = type-error x
ok x >>=p k = k x (here refl)
delay x >>=p k = delay (x t>>=p λ v p → k v (next p))
TCMThunk.force (m t>>=p k) = TCMThunk.force m >>=p k

_t>>=_ : {A : Set ℓ} {B : Set ℓ′} → TCMThunk A → (A → TCM B) → TCMThunk B
_>>=_ : {A : Set ℓ} {B : Set ℓ′} → TCM A → (A → TCM B) → TCM B
m >>= k = m >>=p λ v _ → k v
m t>>= k = m t>>=p λ v _ → k v

interpret-ctx : CtxExpr → TCM (Ctx ★)
interpret-ty : TyExpr → (Γ : CtxExpr) (sΓ : Ctx ★) → HasRes (interpret-ctx Γ) sΓ → TCM (Ty sΓ)
ty-eq? : (T S : TyExpr) (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : HasRes (interpret-ctx Γ) sΓ)
         (sT sS : Ty sΓ) → HasRes (interpret-ty T Γ sΓ Γ-ok) sT → HasRes (interpret-ty S Γ sΓ Γ-ok) sS →
         TCM (sT ≅ᵗʸ sS)
record InferInterpretResult (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : HasRes (interpret-ctx Γ) sΓ) : Set₁
infer-interpret-tm : TmExpr → (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : HasRes (interpret-ctx Γ) sΓ) → TCM (InferInterpretResult Γ sΓ Γ-ok)

record InferInterpretResult Γ sΓ Γ-ok where
  inductive
  pattern
  constructor tm-result
  field
    T : TyExpr
    sT : Ty sΓ
    type-valid : HasRes (interpret-ty T Γ sΓ Γ-ok) sT
    interpretation : Tm sΓ sT

interpret-ctx ◇ = return M.◇
interpret-ctx (Γ ,, T) = interpret-ctx Γ >>=p
                         λ sΓ Γ-ok → interpret-ty T Γ sΓ Γ-ok >>=
                         λ sT → return (sΓ M.,, sT)

interpret-ty Nat Γ sΓ Γ-ok = return M.Nat'
interpret-ty Bool Γ sΓ Γ-ok = return M.Bool'
interpret-ty (T ⇛ S) Γ sΓ Γ-ok = do
  sT ← interpret-ty T Γ sΓ Γ-ok
  sS ← interpret-ty S Γ sΓ Γ-ok
  return (sT M.⇛ sS)
interpret-ty (T ⊠ S) Γ sΓ Γ-ok = do
  sT ← interpret-ty T Γ sΓ Γ-ok
  sS ← interpret-ty S Γ sΓ Γ-ok
  return (sT M.⊠ sS)
interpret-ty (Id t s) Γ sΓ Γ-ok = do
  tm-result T sT T-ok ⟦t⟧ ← infer-interpret-tm t Γ sΓ Γ-ok
  tm-result S sS S-ok ⟦s⟧ ← infer-interpret-tm s Γ sΓ Γ-ok
  sT=sS ← ty-eq? T S Γ sΓ Γ-ok sT sS T-ok S-ok
  return (M-id.Id ⟦t⟧ (ι[ {!!} ] ⟦s⟧))

-- ty-eq? Nat Nat Γ sΓ Γ-ok .Nat' .Nat' refl refl = return ≅ᵗʸ-refl
-- ty-eq? Bool Bool Γ sΓ Γ-ok .Bool' .Bool' refl refl = return ≅ᵗʸ-refl
-- ty-eq? (T1 ⇛ T2) (S1 ⇛ S2) Γ sΓ Γ-ok sT sS T-ok S-ok with interpret-ty T1 Γ sΓ Γ-ok in eqT1 | interpret-ty T2 Γ sΓ Γ-ok in eqT2 | interpret-ty S1 Γ sΓ Γ-ok in eqS1 | interpret-ty S2 Γ sΓ Γ-ok in eqS2
-- ty-eq? (T1 ⇛ T2) (S1 ⇛ S2) Γ sΓ Γ-ok .(sT1 M.⇛ sT2) .(sS1 M.⇛ sS2) refl refl | ok sT1 | ok sT2 | ok sS1 | ok sS2 = do
--   T1=S1 ← ty-eq? T1 S1 Γ sΓ Γ-ok sT1 sS1 eqT1 eqS1
--   T2=S2 ← ty-eq? T2 S2 Γ sΓ Γ-ok sT2 sS2 eqT2 eqS2
--   return (⇛-cong T1=S1 T2=S2)
-- ty-eq? (T1 ⊠ T2) (S1 ⊠ S2) Γ sΓ Γ-ok sT sS T-ok S-ok with interpret-ty T1 Γ sΓ Γ-ok in eqT1 | interpret-ty T2 Γ sΓ Γ-ok in eqT2 | interpret-ty S1 Γ sΓ Γ-ok in eqS1 | interpret-ty S2 Γ sΓ Γ-ok in eqS2
-- ty-eq? (T1 ⊠ T2) (S1 ⊠ S2) Γ sΓ Γ-ok .(sT1 M.⊠ sT2) .(sS1 M.⊠ sS2) refl refl | ok sT1 | ok sT2 | ok sS1 | ok sS2 = do
--   T1=S1 ← ty-eq? T1 S1 Γ sΓ Γ-ok sT1 sS1 eqT1 eqS1
--   T2=S2 ← ty-eq? T2 S2 Γ sΓ Γ-ok sT2 sS2 eqT2 eqS2
--   return (⊠-cong T1=S1 T2=S2)
-- ty-eq? (Id t1 t2) (Id s1 s2) Γ sΓ Γ-ok sT sS T-ok S-ok = type-error "123"
-- ty-eq? T S Γ sΓ Γ-ok sT sS T-ok S-ok = type-error ""

-- infer-interpret-tm (ann t ∈ x) Γ sΓ Γ-ok = {!!}
-- infer-interpret-tm (var x) Γ sΓ Γ-ok = {!!}
-- infer-interpret-tm (TmExpr.lam x t) Γ sΓ Γ-ok = {!!}
-- infer-interpret-tm (t ∙ t₁) Γ sΓ Γ-ok = {!!}
-- infer-interpret-tm (lit x) Γ sΓ Γ-ok = return (tm-result Nat M.Nat' refl (discr x))
-- infer-interpret-tm suc Γ sΓ Γ-ok = return (tm-result (Nat ⇛ Nat) (Nat' M.⇛ Nat') refl M.suc')
-- infer-interpret-tm plus Γ sΓ Γ-ok = return (tm-result (Nat ⇛ Nat ⇛ Nat) (Nat' M.⇛ Nat' M.⇛ Nat') refl M.nat-sum)
-- infer-interpret-tm true Γ sΓ Γ-ok = return (tm-result Bool M.Bool' refl M.true')
-- infer-interpret-tm false Γ sΓ Γ-ok = return (tm-result Bool M.Bool' refl M.false')
-- infer-interpret-tm (if t t₁ t₂) Γ sΓ Γ-ok = {!!}
-- infer-interpret-tm (TmExpr.pair t t₁) Γ sΓ Γ-ok = type-error "pairs not supported"
-- infer-interpret-tm (TmExpr.fst t) Γ sΓ Γ-ok = type-error "pairs not supported"
-- infer-interpret-tm (TmExpr.snd t) Γ sΓ Γ-ok = type-error "pairs not supported"
-- infer-interpret-tm (refl t) Γ sΓ Γ-ok = {!!}
