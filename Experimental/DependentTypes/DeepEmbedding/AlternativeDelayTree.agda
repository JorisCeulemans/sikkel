module Experimental.DependentTypes.DeepEmbedding.AlternativeDelayTree where

open import Level
open import Data.String
open import Data.Unit
open import Data.Product
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

data TCM ℓ′ (A : Set ℓ) : Set (Level.suc ℓ′ Level.⊔ ℓ)
record TCMThunk ℓ′ (A : Set ℓ) : Set (Level.suc ℓ′ Level.⊔ ℓ) where
  coinductive
  field force : TCM ℓ′ A

data TCM ℓ′ A where
  type-error : String → TCM ℓ′ A
  ok : A → TCM ℓ′ A
  bind : {B : Set ℓ′} → (m : TCM ℓ′ B) → (B → TCM ℓ′ A) → TCM ℓ′ A
  delay : TCMThunk ℓ′ A → TCM ℓ′ A

data HasRes {ℓ ℓ′} {A : Set ℓ} : TCM ℓ′ A → A → Set (ℓ ⊔ Level.suc ℓ′) where
  here : {v : A} {m : TCM ℓ′ A} → m ≡ ok v → HasRes m v
  bind : {v : A} {v′ : B} {m : TCM ℓ′ B} {k : (v′ : B) → TCM ℓ′ A} →
         (hr : HasRes m v′) → HasRes (k v′) v → HasRes (bind m k) v
  next : {v : A} {m : TCMThunk ℓ′ A} → HasRes (TCMThunk.force m) v → HasRes (delay m) v


return : {A : Set ℓ} → A → TCM ℓ′ A
return = ok


_t>>=p_ : (m : TCMThunk ℓ′ A) → (∀ v → HasRes (TCMThunk.force m) v → TCM ℓ′ B) → TCMThunk ℓ′ B
_>>=p_ : (m : TCM ℓ′ A) → (∀ v → HasRes m v → TCM ℓ′ B) → TCM ℓ′ B
type-error x >>=p k = type-error x
ok x >>=p k = k x (here refl)
delay x >>=p k = delay (x t>>=p λ v p → k v (next p))
bind m k1 >>=p k2 = bind m (λ v → {!!})
TCMThunk.force (m t>>=p k) = TCMThunk.force m >>=p k

-- _t>>=_ : {A : Set ℓ} {B : Set ℓ′} → TCMThunk A → (A → TCM B) → TCMThunk B
-- _>>=_ : {A : Set ℓ} {B : Set ℓ′} → TCM A → (A → TCM B) → TCM B
-- m >>= k = m >>=p λ v _ → k v
-- m t>>= k = m t>>=p λ v _ → k v

-- HasRes-invert-t>>=p : ∀ {v} (m : TCMThunk A) {k : ∀ v → HasRes (TCMThunk.force m) v → TCM B} → HasRes (TCMThunk.force (m t>>=p k)) v →
--                     ∃ λ v' → Σ (HasRes (TCMThunk.force m) v') λ p → HasRes (k v' p) v
-- HasRes-invert->>=p : ∀ {v} (m : TCM A) {k : ∀ v → HasRes m v → TCM B} → HasRes (m >>=p k) v →
--                    ∃ λ v' → Σ (HasRes m v') λ p → HasRes (k v' p) v
-- HasRes-invert->>=p (type-error x) (here ())
-- HasRes-invert->>=p (ok v) hr = v , here refl , hr
-- HasRes-invert->>=p (delay m) (next hr) with HasRes-invert-t>>=p m hr
-- HasRes-invert->>=p (delay m) hr | v' , hrm , hrk = v' , next hrm , hrk
-- HasRes-invert-t>>=p m hr = HasRes-invert->>=p (TCMThunk.force m) hr

-- -- domi: I think the TERMINATING pragma needed because Agda doesn't see that >>=p preserves delays.
-- -- This suggests the need for sized types or guarded recursion...
-- -- On the other hand, we're trying to avoid to depend on host language extensions...
-- {-# TERMINATING #-}
-- interpret-ctx : CtxExpr → TCM (Ctx ★)
-- interpret-ty : TyExpr → (Γ : CtxExpr) (sΓ : Ctx ★) → HasRes (interpret-ctx Γ) sΓ → TCM (Ty sΓ)
-- interpret-ty-delay : TyExpr → (Γ : CtxExpr) (sΓ : Ctx ★) → HasRes (interpret-ctx Γ) sΓ → TCMThunk (Ty sΓ)
-- ty-eq? : (T S : TyExpr) (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : HasRes (interpret-ctx Γ) sΓ)
--          (sT sS : Ty sΓ) → HasRes (interpret-ty T Γ sΓ Γ-ok) sT → HasRes (interpret-ty S Γ sΓ Γ-ok) sS →
--          TCM (sT ≅ᵗʸ sS)
-- ty-eq?-thunk : (T S : TyExpr) (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : HasRes (interpret-ctx Γ) sΓ)
--          (sT sS : Ty sΓ) → HasRes (interpret-ty T Γ sΓ Γ-ok) sT → HasRes (interpret-ty S Γ sΓ Γ-ok) sS →
--          TCMThunk (sT ≅ᵗʸ sS)
-- record InferInterpretResult (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : HasRes (interpret-ctx Γ) sΓ) : Set₁
-- infer-interpret-tm : TmExpr → (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : HasRes (interpret-ctx Γ) sΓ) → TCM (InferInterpretResult Γ sΓ Γ-ok)

-- record InferInterpretResult Γ sΓ Γ-ok where
--   inductive
--   pattern
--   constructor tm-result
--   field
--     T : TyExpr
--     sT : Ty sΓ
--     type-valid : HasRes (interpret-ty T Γ sΓ Γ-ok) sT
--     interpretation : Tm sΓ sT

-- interpret-ctx ◇ = return M.◇
-- interpret-ctx (Γ ,, T) = interpret-ctx Γ >>=p
--                          λ sΓ Γ-ok → interpret-ty T Γ sΓ Γ-ok >>=
--                          λ sT → return (sΓ M.,, sT)

-- interpret-ty T Γ sΓ Γ-ok = delay (interpret-ty-delay T Γ sΓ Γ-ok)
-- TCMThunk.force (interpret-ty-delay Nat Γ sΓ Γ-ok) = return M.Nat'
-- TCMThunk.force (interpret-ty-delay Bool Γ sΓ Γ-ok) = return M.Bool'
-- TCMThunk.force (interpret-ty-delay (T ⇛ S) Γ sΓ Γ-ok) = do
--   sT ← interpret-ty T Γ sΓ Γ-ok
--   sS ← interpret-ty S Γ sΓ Γ-ok
--   return (sT M.⇛ sS)
-- TCMThunk.force (interpret-ty-delay (T ⊠ S) Γ sΓ Γ-ok) = do
--   sT ← interpret-ty T Γ sΓ Γ-ok
--   sS ← interpret-ty S Γ sΓ Γ-ok
--   return (sT M.⊠ sS)
-- TCMThunk.force (interpret-ty-delay (Id t s) Γ sΓ Γ-ok) = do
--   tm-result T sT T-ok ⟦t⟧ ← infer-interpret-tm t Γ sΓ Γ-ok
--   tm-result S sS S-ok ⟦s⟧ ← infer-interpret-tm s Γ sΓ Γ-ok
--   sT=sS ← ty-eq? T S Γ sΓ Γ-ok sT sS T-ok S-ok
--   return (M-id.Id ⟦t⟧ (ι[ sT=sS ] ⟦s⟧))

-- ty-eq? T1 T2 Γ sΓ Γ-ok sT1 sT2 T1-ok T2-ok = delay (ty-eq?-thunk T1 T2 Γ sΓ Γ-ok sT1 sT2 T1-ok T2-ok )

-- TCMThunk.force (ty-eq?-thunk Nat Nat Γ sΓ Γ-ok .Nat' .Nat' (next (here refl)) (next (here refl))) = return ≅ᵗʸ-refl
-- TCMThunk.force (ty-eq?-thunk Bool Bool Γ sΓ Γ-ok .Bool' .Bool' (next (here refl)) (next (here refl))) = return ≅ᵗʸ-refl
-- TCMThunk.force (ty-eq?-thunk (T1 ⇛ T2) (S1 ⇛ S2) Γ sΓ Γ-ok sT sS (next T-ok) (next S-ok)) with tt
-- TCMThunk.force (ty-eq?-thunk (T1 ⇛ T2) (S1 ⇛ S2) Γ sΓ Γ-ok sT sS (next T-ok) (next S-ok)) | tt
--   with
--     HasRes-invert->>=p (interpret-ty T1 Γ sΓ Γ-ok) {λ sT1 _ → interpret-ty T2 Γ sΓ Γ-ok >>= λ sT2 → return (sT1 M.⇛ sT2)} T-ok
--   | HasRes-invert->>=p (interpret-ty S1 Γ sΓ Γ-ok) {λ sS1 _ → interpret-ty S2 Γ sΓ Γ-ok >>= λ sS2 → return (sS1 M.⇛ sS2)} S-ok
-- TCMThunk.force (ty-eq?-thunk (T1 ⇛ T2) (S1 ⇛ S2) Γ sΓ Γ-ok sT sS (next T-ok) (next S-ok)) | tt 
--   | sT1 , T1-ok , kT-ok | sS1 , S1-ok , kS-ok
--   with
--     HasRes-invert->>=p (interpret-ty T2 Γ sΓ Γ-ok) {λ sT2 _ → return (sT1 M.⇛ sT2)} kT-ok
--   | HasRes-invert->>=p (interpret-ty S2 Γ sΓ Γ-ok) {λ sS2 _ → return (sS1 M.⇛ sS2)} kS-ok
-- TCMThunk.force (ty-eq?-thunk (T1 ⇛ T2) (S1 ⇛ S2) Γ sΓ Γ-ok sT sS (next T-ok) (next S-ok)) | tt 
--   | sT1 , T1-ok , kT-ok | sS1 , S1-ok , kS-ok
--   | sT2 , T2-ok , here refl | sS2 , S2-ok , here refl
--  = do
--   T1=S1 ← ty-eq? T1 S1 Γ sΓ Γ-ok sT1 sS1 T1-ok S1-ok
--   T2=S2 ← ty-eq? T2 S2 Γ sΓ Γ-ok sT2 sS2 T2-ok S2-ok
--   return (⇛-cong T1=S1 T2=S2)
-- -- -- ty-eq?-thunk (T1 ⊠ T2) (S1 ⊠ S2) Γ sΓ Γ-ok sT sS T-ok S-ok with interpret-ty T1 Γ sΓ Γ-ok in eqT1 | interpret-ty T2 Γ sΓ Γ-ok in eqT2 | interpret-ty S1 Γ sΓ Γ-ok in eqS1 | interpret-ty S2 Γ sΓ Γ-ok in eqS2
-- -- -- ty-eq?-thunk (T1 ⊠ T2) (S1 ⊠ S2) Γ sΓ Γ-ok .(sT1 M.⊠ sT2) .(sS1 M.⊠ sS2) refl refl | ok sT1 | ok sT2 | ok sS1 | ok sS2 = do
-- -- --   T1=S1 ← ty-eq?-thunk T1 S1 Γ sΓ Γ-ok sT1 sS1 eqT1 eqS1
-- -- --   T2=S2 ← ty-eq?-thunk T2 S2 Γ sΓ Γ-ok sT2 sS2 eqT2 eqS2
-- -- --   return (⊠-cong T1=S1 T2=S2)
-- -- ty-eq?-thunk (Id t1 t2) (Id s1 s2) Γ sΓ Γ-ok sT sS T-ok S-ok = type-error "123"
-- TCMThunk.force (ty-eq?-thunk T S Γ sΓ Γ-ok sT sS T-ok S-ok) = type-error ""

-- infer-interpret-tm t Γ sΓ Γ-ok  = {!!}
-- -- infer-interpret-tm (ann t ∈ x) Γ sΓ Γ-ok = {!!}
-- -- infer-interpret-tm (var x) Γ sΓ Γ-ok = {!!}
-- -- infer-interpret-tm (TmExpr.lam x t) Γ sΓ Γ-ok = {!!}
-- -- infer-interpret-tm (t ∙ t₁) Γ sΓ Γ-ok = {!!}
-- -- infer-interpret-tm (lit x) Γ sΓ Γ-ok = return (tm-result Nat M.Nat' refl (discr x))
-- -- infer-interpret-tm suc Γ sΓ Γ-ok = return (tm-result (Nat ⇛ Nat) (Nat' M.⇛ Nat') refl M.suc')
-- -- infer-interpret-tm plus Γ sΓ Γ-ok = return (tm-result (Nat ⇛ Nat ⇛ Nat) (Nat' M.⇛ Nat' M.⇛ Nat') refl M.nat-sum)
-- -- infer-interpret-tm true Γ sΓ Γ-ok = return (tm-result Bool M.Bool' refl M.true')
-- -- infer-interpret-tm false Γ sΓ Γ-ok = return (tm-result Bool M.Bool' refl M.false')
-- -- infer-interpret-tm (if t t₁ t₂) Γ sΓ Γ-ok = {!!}
-- -- infer-interpret-tm (TmExpr.pair t t₁) Γ sΓ Γ-ok = type-error "pairs not supported"
-- -- infer-interpret-tm (TmExpr.fst t) Γ sΓ Γ-ok = type-error "pairs not supported"
-- -- infer-interpret-tm (TmExpr.snd t) Γ sΓ Γ-ok = type-error "pairs not supported"
-- -- infer-interpret-tm (refl t) Γ sΓ Γ-ok = {!!}
