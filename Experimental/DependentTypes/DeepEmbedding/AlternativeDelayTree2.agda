module Experimental.DependentTypes.DeepEmbedding.AlternativeDelayTree2 where

open import Level hiding (suc)
open import Data.Nat renaming (_≟_ to _≟nat_)
open import Data.Unit hiding (_≟_)
open import Function using (_∘_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.String
open import Data.Maybe hiding (_>>=_)
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

open import Experimental.DependentTypes.DeepEmbedding.Alternative3.Syntax hiding (is-fun-ty; is-prod-ty)
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

_t>>=_ : {A : Set ℓ′} {B : Set ℓ} → TCMThunk ℓ′ A → (A → TCM ℓ′ B) → TCMThunk ℓ′ B
_>>=_ : {A : Set ℓ′} {B : Set ℓ} → TCM ℓ′ A → (A → TCM ℓ′ B) → TCM ℓ′ B
m >>= k = m >>=p λ v _ → k v
m t>>= k = m t>>=p λ v _ → k v

_>>_ : {A : Set ℓ′} {B : Set ℓ} → TCM ℓ′ A → TCM ℓ′ B → TCM ℓ′ B
m₁ >> m₂ = m₁ >>= λ _ → m₂

infixr 10 _>>_

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




-- TODO: Use of de Bruijn indices is incorrect, e.g. shift needed when extending context.

is-yes : ∀ {ℓ} {A : Set ℓ} → Dec A → TCM 0ℓ ⊤
is-yes (yes _) = return tt
is-yes (no _)  = type-error ""

_≟tm_ : TmExpr → TmExpr → TCM 0ℓ ⊤
_≟ty_ : TyExpr → TyExpr → TCM 0ℓ ⊤

(ann t ∈ T) ≟tm (ann s ∈ S) = (t ≟tm s) >> (T ≟ty S)
var x ≟tm var y = is-yes (x ≟nat y)
lam T b ≟tm lam S c = (T ≟ty S) >> (b ≟tm c)
(t1 ∙ s1) ≟tm (t2 ∙ s2) = (t1 ≟tm t2) >> (s1 ≟tm s2)
lit n ≟tm lit m = is-yes (n ≟nat m)
suc ≟tm suc = return tt
plus ≟tm plus = return tt
true ≟tm true = return tt
false ≟tm false = return tt
if c t f ≟tm if c' t' f' = (c ≟tm c') >> (t ≟tm t') >> (f ≟tm f')
pair t1 s1 ≟tm pair t2 s2 = (t1 ≟tm t2) >> (s1 ≟tm s2)
fst p1 ≟tm fst p2 = p1 ≟tm p2
snd p1 ≟tm snd p2 = p1 ≟tm p2
refl t ≟tm refl s = t ≟tm s
t ≟tm s = type-error ""

Nat ≟ty Nat = return tt
Bool ≟ty Bool = return tt
(T1 ⇛ S1) ≟ty (T2 ⇛ S2) = (T1 ≟ty T2) >> (S1 ≟ty S2)
(T1 ⊠ S1) ≟ty (T2 ⊠ S2) = (T1 ≟ty T2) >> (S1 ≟ty S2)
Id T1 t1 s1 ≟ty Id T2 t2 s2 = (T1 ≟ty T2) >> (t1 ≟tm t2) >> (s1 ≟tm s2)
T ≟ty S = type-error ""

lookup-var : ℕ → CtxExpr → TCM 0ℓ TyExpr
lookup-var x ◇ = type-error ""
lookup-var zero    (Γ ,, T) = return T
lookup-var (suc x) (Γ ,, T) = lookup-var x Γ

is-fun-ty : (T : TyExpr) → TCM 0ℓ (IsFunTy T)
is-fun-ty (T ⇛ S) = ok (fun-ty T S)
is-fun-ty T = type-error ""

is-prod-ty : (T : TyExpr) → TCM 0ℓ (IsProdTy T)
is-prod-ty (T ⊠ S) = ok (prod-ty T S)
is-prod-ty T = type-error ""

check-ty : TyExpr → CtxExpr → TCM 0ℓ ⊤
infer-tm : TmExpr → CtxExpr → TCM 0ℓ TyExpr
infer-tm (ann t ∈ S) Γ = do
  T ← infer-tm t Γ
  check-ty S Γ
  T ≟ty S
  return S
infer-tm (var x) Γ = lookup-var x Γ
infer-tm (lam T b) Γ = do
  S ← infer-tm b (Γ ,, T)
  return (T ⇛ S)
infer-tm (t1 ∙ t2) Γ = do
  T1 ← infer-tm t1 Γ
  fun-ty T S ← is-fun-ty T1
  T2 ← infer-tm t2 Γ
  T2 ≟ty T
  return S
infer-tm (lit n) Γ = return Nat
infer-tm suc Γ = return (Nat ⇛ Nat)
infer-tm plus Γ = return (Nat ⇛ Nat ⇛ Nat)
infer-tm true Γ = return Bool
infer-tm false Γ = return Bool
infer-tm (if c t f) Γ = do
  C ← infer-tm c Γ
  C ≟ty Bool
  T ← infer-tm t Γ
  F ← infer-tm f Γ
  T ≟ty F
  return T
infer-tm (pair t1 t2) Γ = do
  T1 ← infer-tm t1 Γ
  T2 ← infer-tm t2 Γ
  return (T1 ⊠ T2)
infer-tm (fst p) Γ = do
  P ← infer-tm p Γ
  prod-ty T S ← is-prod-ty P
  return T
infer-tm (snd p) Γ = do
  P ← infer-tm p Γ
  prod-ty T S ← is-prod-ty P
  return S
infer-tm (refl t) Γ = do
  T ← infer-tm t Γ
  return (Id T t t)

check-ty Nat Γ = return tt
check-ty Bool Γ = return tt
check-ty (T ⇛ S) Γ = check-ty T Γ >> check-ty S Γ
check-ty (T ⊠ S) Γ = check-ty T Γ >> check-ty S Γ
check-ty (Id R t s) Γ = do
  check-ty R Γ
  T ← infer-tm t Γ
  R ≟ty T
  S ← infer-tm s Γ
  R ≟ty S

check-ctx : CtxExpr → TCM 0ℓ ⊤
check-ctx CtxExpr.◇ = ok tt
check-ctx (Γ ,, T) = do tt <- check-ctx Γ
                        check-ty T Γ

inferredTypes-check : ∀ (t : TmExpr) {Γ T} → HasRes (check-ctx Γ) tt → HasRes (infer-tm t Γ) T → HasRes (check-ty T Γ) tt
inferredTypes-check (ann t ∈ T) {Γ} {T′} Γ-ok ta-ok with HasRes-invert->>=p (infer-tm t Γ) ta-ok
inferredTypes-check (ann t ∈ T) {Γ} {T′} Γ-ok ta-ok | T₁ , t-ok , Teqret-ok with HasRes-invert->>=p (check-ty T Γ) Teqret-ok
inferredTypes-check (ann t ∈ T) {Γ} {T′} Γ-ok ta-ok | T₁ , t-ok , _ | tt , T-ok , eqret-ok with HasRes-invert->>=p (T₁ ≟ty T) eqret-ok
inferredTypes-check (ann t ∈ T) {Γ} {T′} Γ-ok ta-ok | T₁ , t-ok , _ | tt , T-ok , eqret-ok | tt , eq-ok , (suc n , refl) = T-ok
inferredTypes-check (var x) Γ-ok t-ok = {!!}
inferredTypes-check (TmExpr.lam x t) Γ-ok t-ok = {!!}
inferredTypes-check (t ∙ t₁) Γ-ok t-ok = {!!}
inferredTypes-check (lit x) Γ-ok (suc n , refl) = 10 + n , refl
inferredTypes-check TmExpr.suc Γ-ok (suc n , refl) = 10 + n , refl
inferredTypes-check plus Γ-ok (suc n , refl) = 10 + n , refl
inferredTypes-check true Γ-ok (suc n , refl) = suc n , refl
inferredTypes-check false Γ-ok (suc n , refl) = suc n , refl
inferredTypes-check (if t t₁ t₂) Γ-ok t-ok = {!!}
inferredTypes-check (TmExpr.pair t t₁) Γ-ok t-ok = {!!}
inferredTypes-check (TmExpr.fst t) Γ-ok t-ok = {!!}
inferredTypes-check (TmExpr.snd t) Γ-ok t-ok = {!!}
inferredTypes-check (refl t) Γ-ok t-ok = {!!}



1ℓ : Level
1ℓ = Level.suc 0ℓ

interpret-ctx : (Γ : CtxExpr) → HasRes (check-ctx Γ) tt → Ctx ★
interpret-ty : (T : TyExpr) → (Γ : CtxExpr) →
               (Γ-ok : HasRes (check-ctx Γ) tt) →
               HasRes (check-ty T Γ) tt →
               Ty (interpret-ctx Γ Γ-ok)
interpret-tm : (t : TmExpr) → (Γ : CtxExpr) {T : TyExpr} →
               (Γ-ok : HasRes (check-ctx Γ) tt) →
               (t-ok : HasRes (infer-tm t Γ) T) →
               Tm (interpret-ctx Γ Γ-ok) (interpret-ty T Γ Γ-ok (inferredTypes-check t Γ-ok t-ok))
interpret-eq : (T S : TyExpr) (Γ : CtxExpr)
         (Γ-ok : HasRes (check-ctx Γ) tt) →
         (T-ok : HasRes (check-ty T Γ) tt) →
         (S-ok : HasRes (check-ty S Γ) tt) →
         (eq-ok : HasRes (T ≟ty S) tt) →
         interpret-ty T Γ Γ-ok T-ok ≅ᵗʸ interpret-ty S Γ Γ-ok S-ok

interpret-ctx CtxExpr.◇ Γ-ok = M.◇
interpret-ctx (Γ ,, T) ΓT-ok with HasRes-invert->>=p (check-ctx Γ) ΓT-ok
interpret-ctx (Γ ,, T) ΓT-ok | tt , Γ-ok , T-ok = interpret-ctx Γ Γ-ok M.,, interpret-ty T Γ Γ-ok T-ok

interpret-ty Nat Γ Γ-ok T-ok = M.Nat'
interpret-ty Bool Γ Γ-ok T-ok = M.Bool'
interpret-ty (T₁ ⇛ T₂) Γ Γ-ok TA-ok with HasRes-invert->>=p (check-ty T₁ Γ) TA-ok
interpret-ty (T₁ ⇛ T₂) Γ Γ-ok TA-ok | tt , T₁-ok , T₂-ok =
  interpret-ty T₁ Γ Γ-ok T₁-ok M.⇛ interpret-ty T₂ Γ Γ-ok T₂-ok
interpret-ty (T₁ ⊠ T₂) Γ Γ-ok TA-ok with HasRes-invert->>=p (check-ty T₁ Γ) TA-ok
interpret-ty (T₁ ⊠ T₂) Γ Γ-ok TA-ok | tt , T₁-ok , T₂-ok =
  interpret-ty T₁ Γ Γ-ok T₁-ok M.⊠ interpret-ty T₂ Γ Γ-ok T₂-ok
interpret-ty (Id T t₁ t₂) Γ Γ-ok IdTt₁t₂-ok with HasRes-invert->>=p (check-ty T Γ) IdTt₁t₂-ok
interpret-ty (Id T t₁ t₂) Γ Γ-ok IdTt₁t₂-ok | tt , T-ok , T₁eq₁T₂eq₂-ok with HasRes-invert->>=p (infer-tm t₁ Γ) T₁eq₁T₂eq₂-ok
interpret-ty (Id T t₁ t₂) Γ Γ-ok IdTt₁t₂-ok | tt , T-ok , _ | T₁ , T₁-ok , eqT₂eq-ok with HasRes-invert->>=p (T ≟ty T₁) eqT₂eq-ok
interpret-ty (Id T t₁ t₂) Γ Γ-ok IdTt₁t₂-ok | tt , T-ok , _ | T₁ , T₁-ok , _ | tt , eq₁-ok , T₂eq-ok with HasRes-invert->>=p (infer-tm t₂ Γ) T₂eq-ok
interpret-ty (Id T t₁ t₂) Γ Γ-ok IdTt₁t₂-ok | tt , T-ok , _ | T₁ , t₁-ok , _ | tt , eq₁-ok , _ | T₂ , t₂-ok , eq₂-ok =
  M-id.Id
    (ι[ interpret-eq T T₁ Γ Γ-ok T-ok (inferredTypes-check t₁ Γ-ok t₁-ok) eq₁-ok  ] interpret-tm t₁ Γ Γ-ok t₁-ok)
    (ι[ interpret-eq T T₂ Γ Γ-ok T-ok (inferredTypes-check t₂ Γ-ok t₂-ok) eq₂-ok ] interpret-tm t₂ Γ Γ-ok t₂-ok)
-- interpret-ty-delay : TyExpr → (Γ : CtxExpr) (sΓ : Ctx ★) → HasRes (interpret-ctx Γ) sΓ → TCMThunk 1ℓ (Ty sΓ)
-- ty-eq? : (T S : TyExpr) (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : HasRes (interpret-ctx Γ) sΓ)
--          (sT sS : Ty sΓ) → HasRes (interpret-ty T Γ sΓ Γ-ok) sT → HasRes (interpret-ty S Γ sΓ Γ-ok) sS →
--          TCM 1ℓ (Lift 1ℓ (sT ≅ᵗʸ sS))
-- ty-eq?-thunk : (T S : TyExpr) (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : HasRes (interpret-ctx Γ) sΓ)
--          (sT sS : Ty sΓ) → HasRes (interpret-ty T Γ sΓ Γ-ok) sT → HasRes (interpret-ty S Γ sΓ Γ-ok) sS →
--          TCMThunk 1ℓ (Lift 1ℓ (sT ≅ᵗʸ sS))
-- record InferInterpretResult (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : HasRes (interpret-ctx Γ) sΓ) : Set₁
-- infer-interpret-tm : TmExpr → (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : HasRes (interpret-ctx Γ) sΓ) → TCM 1ℓ (InferInterpretResult Γ sΓ Γ-ok)

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
--   lift sT=sS ← ty-eq? T S Γ sΓ Γ-ok sT sS T-ok S-ok
--   return (M-id.Id ⟦t⟧ (ι[ sT=sS ] ⟦s⟧))

-- ty-eq? T1 T2 Γ sΓ Γ-ok sT1 sT2 T1-ok T2-ok = delay (ty-eq?-thunk T1 T2 Γ sΓ Γ-ok sT1 sT2 T1-ok T2-ok )

-- ty-eq?-thunk T S Γ sΓ Γ-ok = {!!}
-- -- TCMThunk.force (ty-eq?-thunk Nat Nat Γ sΓ Γ-ok .Nat' .Nat' (next (here refl)) (next (here refl))) = return ≅ᵗʸ-refl
-- -- TCMThunk.force (ty-eq?-thunk Bool Bool Γ sΓ Γ-ok .Bool' .Bool' (next (here refl)) (next (here refl))) = return ≅ᵗʸ-refl
-- -- TCMThunk.force (ty-eq?-thunk (T1 ⇛ T2) (S1 ⇛ S2) Γ sΓ Γ-ok sT sS (next T-ok) (next S-ok)) with tt
-- -- TCMThunk.force (ty-eq?-thunk (T1 ⇛ T2) (S1 ⇛ S2) Γ sΓ Γ-ok sT sS (next T-ok) (next S-ok)) | tt
-- --   with
-- --     HasRes-invert->>=p (interpret-ty T1 Γ sΓ Γ-ok) {λ sT1 _ → interpret-ty T2 Γ sΓ Γ-ok >>= λ sT2 → return (sT1 M.⇛ sT2)} T-ok
-- --   | HasRes-invert->>=p (interpret-ty S1 Γ sΓ Γ-ok) {λ sS1 _ → interpret-ty S2 Γ sΓ Γ-ok >>= λ sS2 → return (sS1 M.⇛ sS2)} S-ok
-- -- TCMThunk.force (ty-eq?-thunk (T1 ⇛ T2) (S1 ⇛ S2) Γ sΓ Γ-ok sT sS (next T-ok) (next S-ok)) | tt 
-- --   | sT1 , T1-ok , kT-ok | sS1 , S1-ok , kS-ok
-- --   with
-- --     HasRes-invert->>=p (interpret-ty T2 Γ sΓ Γ-ok) {λ sT2 _ → return (sT1 M.⇛ sT2)} kT-ok
-- --   | HasRes-invert->>=p (interpret-ty S2 Γ sΓ Γ-ok) {λ sS2 _ → return (sS1 M.⇛ sS2)} kS-ok
-- -- TCMThunk.force (ty-eq?-thunk (T1 ⇛ T2) (S1 ⇛ S2) Γ sΓ Γ-ok sT sS (next T-ok) (next S-ok)) | tt 
-- --   | sT1 , T1-ok , kT-ok | sS1 , S1-ok , kS-ok
-- --   | sT2 , T2-ok , here refl | sS2 , S2-ok , here refl
-- --  = do
-- --   T1=S1 ← ty-eq? T1 S1 Γ sΓ Γ-ok sT1 sS1 T1-ok S1-ok
-- --   T2=S2 ← ty-eq? T2 S2 Γ sΓ Γ-ok sT2 sS2 T2-ok S2-ok
-- --   return (⇛-cong T1=S1 T2=S2)
-- -- -- -- ty-eq?-thunk (T1 ⊠ T2) (S1 ⊠ S2) Γ sΓ Γ-ok sT sS T-ok S-ok with interpret-ty T1 Γ sΓ Γ-ok in eqT1 | interpret-ty T2 Γ sΓ Γ-ok in eqT2 | interpret-ty S1 Γ sΓ Γ-ok in eqS1 | interpret-ty S2 Γ sΓ Γ-ok in eqS2
-- -- -- -- ty-eq?-thunk (T1 ⊠ T2) (S1 ⊠ S2) Γ sΓ Γ-ok .(sT1 M.⊠ sT2) .(sS1 M.⊠ sS2) refl refl | ok sT1 | ok sT2 | ok sS1 | ok sS2 = do
-- -- -- --   T1=S1 ← ty-eq?-thunk T1 S1 Γ sΓ Γ-ok sT1 sS1 eqT1 eqS1
-- -- -- --   T2=S2 ← ty-eq?-thunk T2 S2 Γ sΓ Γ-ok sT2 sS2 eqT2 eqS2
-- -- -- --   return (⊠-cong T1=S1 T2=S2)
-- -- -- ty-eq?-thunk (Id t1 t2) (Id s1 s2) Γ sΓ Γ-ok sT sS T-ok S-ok = type-error "123"
-- -- TCMThunk.force (ty-eq?-thunk T S Γ sΓ Γ-ok sT sS T-ok S-ok) = type-error ""

-- -- infer-interpret-tm t Γ sΓ Γ-ok  = {!!}
-- -- -- infer-interpret-tm (ann t ∈ x) Γ sΓ Γ-ok = {!!}
-- -- -- infer-interpret-tm (var x) Γ sΓ Γ-ok = {!!}
-- -- -- infer-interpret-tm (TmExpr.lam x t) Γ sΓ Γ-ok = {!!}
-- -- -- infer-interpret-tm (t ∙ t₁) Γ sΓ Γ-ok = {!!}
-- -- -- infer-interpret-tm (lit x) Γ sΓ Γ-ok = return (tm-result Nat M.Nat' refl (discr x))
-- -- -- infer-interpret-tm suc Γ sΓ Γ-ok = return (tm-result (Nat ⇛ Nat) (Nat' M.⇛ Nat') refl M.suc')
-- -- -- infer-interpret-tm plus Γ sΓ Γ-ok = return (tm-result (Nat ⇛ Nat ⇛ Nat) (Nat' M.⇛ Nat' M.⇛ Nat') refl M.nat-sum)
-- -- -- infer-interpret-tm true Γ sΓ Γ-ok = return (tm-result Bool M.Bool' refl M.true')
-- -- -- infer-interpret-tm false Γ sΓ Γ-ok = return (tm-result Bool M.Bool' refl M.false')
-- -- -- infer-interpret-tm (if t t₁ t₂) Γ sΓ Γ-ok = {!!}
-- -- -- infer-interpret-tm (TmExpr.pair t t₁) Γ sΓ Γ-ok = type-error "pairs not supported"
-- -- -- infer-interpret-tm (TmExpr.fst t) Γ sΓ Γ-ok = type-error "pairs not supported"
-- -- -- infer-interpret-tm (TmExpr.snd t) Γ sΓ Γ-ok = type-error "pairs not supported"
-- -- -- infer-interpret-tm (refl t) Γ sΓ Γ-ok = {!!}
