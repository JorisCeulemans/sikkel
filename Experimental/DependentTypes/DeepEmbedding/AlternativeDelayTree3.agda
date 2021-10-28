module Experimental.DependentTypes.DeepEmbedding.AlternativeDelayTree3 where

open import Level hiding (suc)
open import Data.Nat renaming (_≟_ to _≟nat_)
import Data.Bool as Bool
open import Data.Unit hiding (_≟_)
open import Data.Empty
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

open import Experimental.DependentTypes.DeepEmbedding.Syntax.EvenMoreAnnotated hiding (is-fun-ty; is-prod-ty)
-- open import MSTT.TCMonad

private
  variable
    ℓ ℓ′ : Level
    A B : Set ℓ

data TCM ℓ′ (A : Set ℓ) : Set (Level.suc ℓ′ Level.⊔ ℓ)
record TCMThunk ℓ′ (A : Set ℓ) : Set (Level.suc ℓ′ Level.⊔ ℓ) where
  coinductive
  field force : TCM ℓ′ A
HasRes : {A : Set ℓ} → TCM ℓ′ A → A → Set (ℓ Level.⊔ ℓ′)

data TCM ℓ′ A where
  type-error : String → TCM ℓ′ A
  ok : A → TCM ℓ′ A
  bind : {B : Set ℓ′} → (m : TCM ℓ′ B) → ((v : B) → HasRes m v → TCM ℓ′ A) → TCM ℓ′ A
  -- delay : TCMThunk ℓ′ A → TCM ℓ′ A

-- HasRes m v = ∃ λ n → HasResBound n m v
HasRes (type-error x) v = Lift _ ⊥
HasRes {ℓ = ℓ} {ℓ′ = ℓ′} (ok x) v = Lift (ℓ Level.⊔ ℓ′) (x ≡ v)
HasRes (bind m k) v = ∃ λ v′ → Σ (HasRes m v′) λ m-ok → HasRes (k v′ m-ok) v
-- HasResBound (suc n) (delay m) v = HasResBound n (TCMThunk.force m) v

return : {A : Set ℓ} → A → TCM ℓ′ A
return = ok

_>>=p_ : {A : Set ℓ} (m : TCM ℓ A) → (∀ v → HasRes m v → TCM ℓ B) → TCM ℓ B
_>>=p_ = bind
-- _t>>=p_ : {A : Set ℓ} (m : TCMThunk ℓ A) → (∀ v → HasRes (delay m) v → TCM ℓ B) → TCMThunk ℓ B
-- TCMThunk.force (m t>>=p k) = TCMThunk.force m >>=p λ { v (n , eq) → k v (ℕ.suc n , eq)}

-- _t>>=_ : {A : Set ℓ′} {B : Set ℓ} → TCMThunk ℓ′ A → (A → TCM ℓ′ B) → TCMThunk ℓ′ B
_>>=_ : {A : Set ℓ′} {B : Set ℓ} → TCM ℓ′ A → (A → TCM ℓ′ B) → TCM ℓ′ B
m >>= k = m >>=p λ v _ → k v
-- m t>>= k = m t>>=p λ v _ → k v

_>>_ : {A : Set ℓ′} {B : Set ℓ} → TCM ℓ′ A → TCM ℓ′ B → TCM ℓ′ B
m₁ >> m₂ = m₁ >>= λ _ → m₂

infixr 10 _>>_

-- HasRes-invert->>=p : ∀ {v} (m : TCM ℓ′ A) {k : ∀ v → HasRes m v → TCM ℓ′ B} → HasRes (m >>=p k) v →
--                    ∃ λ v' → Σ (HasRes m v') λ p → HasRes (k v' p) v
-- HasRes-invert->>=p m (n , v′ , m-ok , k-ok) = v′ , (_ , m-ok) , (_ , k-ok)




-- TODO: Use of de Bruijn indices is incorrect, e.g. shift needed when extending context.

is-yes : ∀ {ℓ} {A : Set ℓ} → Dec A → TCM 0ℓ ⊤
is-yes (yes _) = return tt
is-yes (no _)  = type-error ""

_≟tm_ : TmExpr → TmExpr → TCM 0ℓ ⊤
_≟ty_ : TyExpr → TyExpr → TCM 0ℓ ⊤

(ann t ∈ T) ≟tm (ann s ∈ S) = (t ≟tm s) >> (T ≟ty S)
var x ≟tm var y = is-yes (x ≟nat y)
lam T b ≟tm lam S c = (T ≟ty S) >> (b ≟tm c)
(app T1 t1 s1) ≟tm (app T2 t2 s2) = (t1 ≟tm t2) >> (s1 ≟tm s2)
lit n ≟tm lit m = is-yes (n ≟nat m)
suc ≟tm suc = return tt
plus ≟tm plus = return tt
true ≟tm true = return tt
false ≟tm false = return tt
if c t f ≟tm if c' t' f' = (c ≟tm c') >> (t ≟tm t') >> (f ≟tm f')
pair t1 s1 ≟tm pair t2 s2 = (t1 ≟tm t2) >> (s1 ≟tm s2)
fst T1 p1 ≟tm fst T2 p2 = p1 ≟tm p2
snd T1 p1 ≟tm snd T2 p2 = p1 ≟tm p2
refl T t ≟tm refl S s = t ≟tm s
t ≟tm s = type-error ""

Nat ≟ty Nat = return tt
Bool ≟ty Bool = return tt
(T1 ⇛ S1) ≟ty (T2 ⇛ S2) = (T1 ≟ty T2) >> (S1 ≟ty S2)
(T1 ⊠ S1) ≟ty (T2 ⊠ S2) = (T1 ≟ty T2) >> (S1 ≟ty S2)
Id T1 t1 s1 ≟ty Id T2 t2 s2 = (T1 ≟ty T2) >> (t1 ≟tm t2) >> (s1 ≟tm s2)
T ≟ty S = type-error ""

check-var : ℕ → CtxExpr → TyExpr → TCM 0ℓ ⊤
check-var x ◇ T = type-error ""
check-var zero    (Γ ,, T) T′ = T ≟ty T′
check-var (suc x) (Γ ,, T) = check-var x Γ

is-fun-ty : (T : TyExpr) → TCM 0ℓ (IsFunTy T)
is-fun-ty (T ⇛ S) = ok (fun-ty T S)
is-fun-ty T = type-error ""

is-prod-ty : (T : TyExpr) → TCM 0ℓ (IsProdTy T)
is-prod-ty (T ⊠ S) = ok (prod-ty T S)
is-prod-ty T = type-error ""

check-ty : TyExpr → CtxExpr → TCM 0ℓ ⊤
check-tm : TmExpr → CtxExpr → TyExpr → TCM 0ℓ ⊤
check-tm (ann t ∈ S) Γ T = do
  check-ty S Γ
  check-tm t Γ S
  T ≟ty S
check-tm (var x) Γ T = check-var x Γ T
check-tm (lam _ b) Γ T = do
  fun-ty T₁ T₂ ← is-fun-ty T
  check-tm b (Γ ,, T₁) T₂ -- domi: should T₂ be shifted up?
check-tm (app T₁ t1 t2) Γ T₂ = do
  check-ty T₁ Γ
  check-tm t1 Γ (T₁ ⇛ T₂)
  check-tm t2 Γ T₁
check-tm (lit n) Γ T = T ≟ty Nat
check-tm suc Γ T = T ≟ty (Nat ⇛ Nat)
check-tm plus Γ T = T ≟ty (Nat ⇛ Nat ⇛ Nat)
check-tm true Γ T = T ≟ty Bool
check-tm false Γ T = T ≟ty Bool
check-tm (if c t f) Γ T = do
  check-tm c Γ Bool
  check-tm t Γ T
  check-tm f Γ T
-- check-tm (pair t1 t2) Γ T = do
--   T1 ← check-tm t1 Γ
--   T2 ← check-tm t2 Γ
--   return (T1 ⊠ T2)
-- check-tm (fst T p) Γ = do
--   P ← check-tm p Γ
--   prod-ty T S ← is-prod-ty P
--   return T
-- check-tm (snd T p) Γ = do
--   P ← check-tm p Γ
--   prod-ty T S ← is-prod-ty P
--   return S
check-tm (refl T t) Γ T′ = do
  check-ty T Γ
  check-tm t Γ T
  T′ ≟ty (Id T t t)
check-tm t Γ T = type-error "not implemented yet"

check-ty Nat Γ = return tt
check-ty Bool Γ = return tt
check-ty (T ⇛ S) Γ = check-ty T Γ >> check-ty S Γ
check-ty (T ⊠ S) Γ = check-ty T Γ >> check-ty S Γ
check-ty (Id R t s) Γ = do
  check-ty R Γ
  check-tm t Γ R
  check-tm s Γ R

check-ctx : CtxExpr → TCM 0ℓ ⊤
check-ctx CtxExpr.◇ = ok tt
check-ctx (Γ ,, T) = do tt <- check-ctx Γ
                        check-ty T Γ

1ℓ : Level
1ℓ = Level.suc 0ℓ

interpret-ctx : (Γ : CtxExpr) → HasRes (check-ctx Γ) tt → Ctx ★
interpret-ty : (T : TyExpr) → (Γ : CtxExpr) →
               (Γ-ok : HasRes (check-ctx Γ) tt) →
               HasRes (check-ty T Γ) tt →
               Ty (interpret-ctx Γ Γ-ok)
interpret-tm : (t : TmExpr) → (Γ : CtxExpr) {T : TyExpr} →
               (Γ-ok : HasRes (check-ctx Γ) tt) →
               (T-ok : HasRes (check-ty T Γ) tt) →
               (t-ok : HasRes (check-tm t Γ T) tt) →
               Tm (interpret-ctx Γ Γ-ok) (interpret-ty T Γ Γ-ok T-ok)
interpret-eq : (T S : TyExpr) (Γ : CtxExpr)
         (Γ-ok : HasRes (check-ctx Γ) tt) →
         (T-ok : HasRes (check-ty T Γ) tt) →
         (S-ok : HasRes (check-ty S Γ) tt) →
         (eq-ok : HasRes (T ≟ty S) tt) →
         interpret-ty T Γ Γ-ok T-ok ≅ᵗʸ interpret-ty S Γ Γ-ok S-ok

interpret-ctx CtxExpr.◇ Γ-ok = M.◇
interpret-ctx (Γ ,, T) (tt , Γ-ok , T-ok) =
  interpret-ctx Γ Γ-ok M.,, interpret-ty T Γ Γ-ok T-ok

interpret-ty Nat Γ Γ-ok T-ok = M.Nat'
interpret-ty Bool Γ Γ-ok T-ok = M.Bool'
interpret-ty (T₁ ⇛ T₂) Γ Γ-ok (tt , T₁-ok , T₂-ok) =
  interpret-ty T₁ Γ Γ-ok T₁-ok M.⇛ interpret-ty T₂ Γ Γ-ok T₂-ok
interpret-ty (T₁ ⊠ T₂) Γ Γ-ok (tt , T₁-ok , T₂-ok) =
  interpret-ty T₁ Γ Γ-ok T₁-ok M.⊠ interpret-ty T₂ Γ Γ-ok T₂-ok
interpret-ty (Id T t₁ t₂) Γ Γ-ok (tt , T-ok , T₁ , t₁-ok , t₂-ok) =
  M-id.Id
    (interpret-tm t₁ Γ Γ-ok T-ok t₁-ok)
    (interpret-tm t₂ Γ Γ-ok T-ok t₂-ok)

interpret-tm (ann t ∈ x) Γ Γ-ok T-ok t-ok = {!!}
interpret-tm (var x) Γ Γ-ok T-ok t-ok = {!!}
interpret-tm (TmExpr.lam _ t) Γ Γ-ok (tt , T₁-ok , T₂-ok) (fun-ty T₁ T₂ , lift refl , t-ok) =
  M.lam (interpret-ty T₁ Γ Γ-ok T₁-ok) {!interpret-tm t (Γ ,, T₁) (tt , Γ-ok , T₁-ok) ? t-ok!}
interpret-tm (TmExpr.app T₁ t₁ t₂) Γ {T₂} Γ-ok T₂-ok (tt , T₁-ok , tt , t₁-ok , t₂-ok) =
  M.app {!interpret-tm t₁ Γ {T₁ ⇛ T₂} Γ-ok (tt , T₁-ok , T₂-ok) t₁-ok!}
    (interpret-tm t₂ Γ {T₁} Γ-ok T₁-ok t₂-ok)
interpret-tm (lit x) Γ {T} Γ-ok T-ok t-ok = ι[ interpret-eq T Nat Γ Γ-ok T-ok (lift refl) t-ok ] discr x
interpret-tm suc Γ {T} Γ-ok T-ok t-ok =
  ι[ {!interpret-eq T (Nat ⇛ Nat) Γ Γ-ok T-ok (tt , lift refl , lift refl) t-ok!} ] M.suc'
interpret-tm plus Γ {T} Γ-ok T-ok t-ok = {!!}
interpret-tm true Γ {T} Γ-ok T-ok t-ok =
  ι[ interpret-eq T Bool Γ Γ-ok T-ok (lift refl) t-ok ] discr Bool.true
interpret-tm false Γ {T} Γ-ok T-ok t-ok =
  ι[ interpret-eq T Bool Γ Γ-ok T-ok (lift refl) t-ok ] discr Bool.false
interpret-tm (if t t₁ t₂) Γ {T} Γ-ok T-ok (tt , t-ok , tt , t₁-ok , t₂-ok) =
  if' (interpret-tm t Γ Γ-ok (lift refl) t-ok)
  then' interpret-tm t₁ Γ Γ-ok T-ok t₁-ok
  else' interpret-tm t₂ Γ Γ-ok T-ok t₂-ok
interpret-tm (refl T′ t) Γ {T} Γ-ok T-ok (tt , T′-ok , tt , t-ok , eq-ok) =
  ι[ interpret-eq T (Id T′ t t) Γ Γ-ok T-ok (tt , T′-ok , tt , t-ok , t-ok) eq-ok ]
  M-id.refl' (interpret-tm t Γ Γ-ok T′-ok t-ok)

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
