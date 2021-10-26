module Experimental.DependentTypes.DeepEmbedding.AlternativeDelayTree2 where

open import Level
open import Data.String
open import Data.Nat
open import Data.Maybe
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
eval : ℕ → TCM ℓ′ A → Maybe A
evalT : ℕ → TCMThunk ℓ′ A → Maybe A
HasRes : {A : Set ℓ} → TCM ℓ′ A → A → Set ℓ
evalBind : (n : ℕ) → {B : Set ℓ′} → (m : TCM ℓ′ B) → (k : (v : B) → HasRes m v → TCM ℓ′ A) → (res : Maybe B) → eval n m ≡ res → Maybe A

HasRes m v = ∃ λ k → eval k m ≡ just v

data TCM ℓ′ A where
  type-error : String → TCM ℓ′ A
  ok : A → TCM ℓ′ A
  bind : {B : Set ℓ′} → (m : TCM ℓ′ B) → ((v : B) → HasRes m v → TCM ℓ′ A) → TCM ℓ′ A
  delay : TCMThunk ℓ′ A → TCM ℓ′ A

evalBind n m k nothing _ = nothing
evalBind n m k (just v) eq = eval n (k v (n , eq))
eval ℕ.zero m = nothing
eval (ℕ.suc n) (type-error _) = nothing
eval (ℕ.suc n) (ok x) = just x
eval (ℕ.suc n) (bind m k) = evalBind n m k (eval n m) refl
eval (ℕ.suc n) (delay x) = evalT n x
evalT n x = eval n (TCMThunk.force x)

return : {A : Set ℓ} → A → TCM ℓ′ A
return = ok

_>>=p_ : {A : Set ℓ} (m : TCM ℓ A) → (∀ v → HasRes m v → TCM ℓ B) → TCM ℓ B
_>>=p_ = bind
_t>>=p_ : {A : Set ℓ} (m : TCMThunk ℓ A) → (∀ v → HasRes (delay m) v → TCM ℓ B) → TCMThunk ℓ B
TCMThunk.force (m t>>=p k) = TCMThunk.force m >>=p λ { v (n , eq) → k v (ℕ.suc n , eq)}

-- _t>>=_ : {A : Set ℓ} {B : Set ℓ′} → TCMThunk ℓ′ A → (A → TCM ℓ′ B) → TCMThunk ℓ′ B
-- _>>=_ : {A : Set ℓ} {B : Set ℓ′} → TCM ℓ′ A → (A → TCM ℓ′ B) → TCM ℓ′ B
-- m >>= k = m >>=p λ v _ → k v
-- m t>>= k = m t>>=p λ v _ → k v

HasRes-invert->>=p : ∀ {v} (m : TCM ℓ′ A) {k : ∀ v → HasRes m v → TCM ℓ′ B} → HasRes (m >>=p k) v →
                   ∃ λ v' → Σ (HasRes m v') λ p → HasRes (k v' p) v
HasRes-invert->>=p-evalBind : ∀ (n : ℕ) → {B : Set ℓ′} → (m : TCM ℓ′ B) →
                             (k : (v : B) → HasRes m v → TCM ℓ′ A) →
                             (res : Maybe B) → (eq : eval (ℕ.suc n) m ≡ res) →
                              ∀ {v} → evalBind (ℕ.suc n) m k res eq ≡ just v →
                              ∃ λ v' → Σ (HasRes m v') λ p → HasRes (k v' p) v
HasRes-invert->>=p-evalBind n (ok v) k (just .v) refl eq′ = v , (ℕ.suc n , refl) , (ℕ.suc n , eq′)
HasRes-invert->>=p-evalBind n (bind m k₁) k₂ (just x) eq eq′ = x , (ℕ.suc n , eq) , (ℕ.suc n , eq′)
HasRes-invert->>=p-evalBind n (delay m) k (just x) eq eq′ = x , (ℕ.suc n , eq) , ℕ.suc n , eq′
HasRes-invert->>=p m (ℕ.suc (ℕ.suc n) , eq) = HasRes-invert->>=p-evalBind n m _ (eval (ℕ.suc n) m) refl eq

-- interpret-ctx : CtxExpr → TCM ℓ′ (Ctx ★)
-- interpret-ty : TyExpr → (Γ : CtxExpr) (sΓ : Ctx ★) → HasRes (interpret-ctx Γ) sΓ → TCM ℓ′ (Ty sΓ)
-- interpret-ty-delay : TyExpr → (Γ : CtxExpr) (sΓ : Ctx ★) → HasRes (interpret-ctx Γ) sΓ → TCMThunk ℓ′ (Ty sΓ)
-- ty-eq? : (T S : TyExpr) (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : HasRes (interpret-ctx Γ) sΓ)
--          (sT sS : Ty sΓ) → HasRes (interpret-ty T Γ sΓ Γ-ok) sT → HasRes (interpret-ty S Γ sΓ Γ-ok) sS →
--          TCM ℓ′ (sT ≅ᵗʸ sS)
-- ty-eq?-thunk : (T S : TyExpr) (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : HasRes (interpret-ctx Γ) sΓ)
--          (sT sS : Ty sΓ) → HasRes (interpret-ty T Γ sΓ Γ-ok) sT → HasRes (interpret-ty S Γ sΓ Γ-ok) sS →
--          TCMThunk ℓ′ (sT ≅ᵗʸ sS)
-- record InferInterpretResult (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : HasRes (interpret-ctx Γ) sΓ) : Set₁
-- infer-interpret-tm : TmExpr → (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : HasRes (interpret-ctx Γ) sΓ) → TCM ℓ′ (InferInterpretResult Γ sΓ Γ-ok)

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
