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
open import Model.Type.Constant as M
open import Model.Type.Function as M hiding (_⇛_)
open import Model.Type.Product as M hiding (_⊠_)

import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M

open import Experimental.DependentTypes.DeepEmbedding.Syntax.EvenMoreAnnotated hiding (is-fun-ty; is-prod-ty)
-- open import MSTT.TCMonad

private
  variable
    ℓ ℓ′ : Level
    A B : Set ℓ

data TCM ℓ′ (A : Set ℓ) : Set (Level.suc ℓ′ Level.⊔ ℓ)
-- record TCMThunk ℓ′ (A : Set ℓ) : Set (Level.suc ℓ′ Level.⊔ ℓ) where
--   coinductive
--   field force : TCM ℓ′ A
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

-- (ann t ∈ T) ≟tm (ann s ∈ S) = (t ≟tm s) >> (T ≟ty S)
-- var x ≟tm var y = is-yes (x ≟nat y)
-- lam T b ≟tm lam S c = (T ≟ty S) >> (b ≟tm c)
-- (app T1 t1 s1) ≟tm (app T2 t2 s2) = (t1 ≟tm t2) >> (s1 ≟tm s2)
-- lit n ≟tm lit m = is-yes (n ≟nat m)
-- suc ≟tm suc = return tt
-- plus ≟tm plus = return tt
true ≟tm true = return tt
false ≟tm false = return tt
-- if c t f ≟tm if c' t' f' = (c ≟tm c') >> (t ≟tm t') >> (f ≟tm f')
-- pair t1 s1 ≟tm pair t2 s2 = (t1 ≟tm t2) >> (s1 ≟tm s2)
-- fst T1 p1 ≟tm fst T2 p2 = p1 ≟tm p2
-- snd T1 p1 ≟tm snd T2 p2 = p1 ≟tm p2
-- refl T t ≟tm refl S s = t ≟tm s
t ≟tm s = type-error ""

Nat ≟ty Nat = return tt
Bool ≟ty Bool = return tt
(T1 ⇛ S1) ≟ty (T2 ⇛ S2) = (T1 ≟ty T2) >> (S1 ≟ty S2)
(T1 ⊠ S1) ≟ty (T2 ⊠ S2) = (T1 ≟ty T2) >> (S1 ≟ty S2)
Id T1 t1 s1 ≟ty Id T2 t2 s2 = (T1 ≟ty T2) >> (t1 ≟tm t2) >> (s1 ≟tm s2)
T ≟ty S = type-error ""

check-var : ℕ → CtxExpr → TyExpr → TCM 0ℓ ⊤
check-var x ◇ T = type-error ""
check-var zero    (Γ ,, T) T′ = T ≟ty T′ -- T needs to be weakened?
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
check-tm (app T t1 t2) Γ T₂ = do
  check-ty T Γ
  fun-ty T₁ T₂′ ← is-fun-ty T
  T₂ ≟ty T₂′
  check-tm t1 Γ T
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
interpret-var : (x : ℕ) → (Γ : CtxExpr) {T : TyExpr} →
               (Γ-ok : HasRes (check-ctx Γ) tt) →
               (T-ok : HasRes (check-ty T Γ) tt) →
               (x-ok : HasRes (check-var x Γ T) tt) →
               Tm (interpret-ctx Γ Γ-ok) (interpret-ty T Γ Γ-ok T-ok)
interpret-ty-eq : (T S : TyExpr) (Γ : CtxExpr)
         (Γ-ok : HasRes (check-ctx Γ) tt) →
         (T-ok : HasRes (check-ty T Γ) tt) →
         (S-ok : HasRes (check-ty S Γ) tt) →
         (eq-ok : HasRes (T ≟ty S) tt) →
         interpret-ty T Γ Γ-ok T-ok ≅ᵗʸ interpret-ty S Γ Γ-ok S-ok
interpret-tm-eq : (t₁ t₂ : TmExpr) (Γ : CtxExpr) (T₁ T₂ : TyExpr)
         (Γ-ok : HasRes (check-ctx Γ) tt) →
         (T₁-ok : HasRes (check-ty T₁ Γ) tt) →
         (T₂-ok : HasRes (check-ty T₂ Γ) tt) →
         (t₁-ok : HasRes (check-tm t₁ Γ T₁) tt) →
         (t₂-ok : HasRes (check-tm t₂ Γ T₂) tt) →
         (ty-eq-ok : HasRes (T₁ ≟ty T₂) tt) →
         (tm-eq-ok : HasRes (t₁ ≟tm t₂) tt) →
         interpret-tm t₁ Γ Γ-ok T₁-ok t₁-ok ≅ᵗᵐ
           ι[ interpret-ty-eq T₁ T₂ Γ Γ-ok T₁-ok T₂-ok ty-eq-ok ]
             interpret-tm t₂ Γ Γ-ok T₂-ok t₂-ok


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
  M.Id
    (interpret-tm t₁ Γ Γ-ok T-ok t₁-ok)
    (interpret-tm t₂ Γ Γ-ok T-ok t₂-ok)

interpret-var ℕ.zero (Γ ,, T) Γ-ok T-ok x-ok = {!!}
interpret-var (suc x) (Γ ,, T) Γ-ok T-ok t-ok = {!!}

interpret-tm (ann t ∈ T′) Γ {T} Γ-ok T-ok (tt , T′-ok , tt , t-ok , T-eq) =
  ι[ interpret-ty-eq T T′ Γ Γ-ok T-ok T′-ok T-eq ] interpret-tm t Γ Γ-ok T′-ok t-ok
interpret-tm (var x) Γ Γ-ok T-ok t-ok = interpret-var x Γ Γ-ok T-ok t-ok
interpret-tm (TmExpr.lam _ t) Γ Γ-ok (tt , T₁-ok , T₂-ok) (fun-ty T₁ T₂ , lift refl , t-ok) =
  M.lam (interpret-ty T₁ Γ Γ-ok T₁-ok) {!interpret-tm t (Γ ,, T₁) (tt , Γ-ok , T₁-ok) ? t-ok!}
interpret-tm (TmExpr.app T t₁ t₂) Γ {T₂} Γ-ok T₂-ok (tt , (tt , T₁-ok , T₂′-ok) , fun-ty T₁ T₂′ , lift refl , tt , eq₂ , tt , t₁-ok , t₂-ok) =
  M.app (ι[ ⇛-cong M.reflᵗʸ (interpret-ty-eq T₂ T₂′ Γ Γ-ok T₂-ok T₂′-ok eq₂) ] interpret-tm t₁ Γ {T₁ ⇛ T₂′} Γ-ok (tt , T₁-ok , T₂′-ok) t₁-ok)
    (interpret-tm t₂ Γ {T₁} Γ-ok T₁-ok t₂-ok)
interpret-tm (lit x) Γ {T} Γ-ok T-ok t-ok = ι[ interpret-ty-eq T Nat Γ Γ-ok T-ok (lift refl) t-ok ] const x
interpret-tm suc Γ {Nat ⇛ Nat} Γ-ok T-ok t-ok = {!M.suc'!}
interpret-tm plus Γ {Nat ⇛ Nat ⇛ Nat} Γ-ok T-ok t-ok = nat-sum
interpret-tm true Γ {T} Γ-ok T-ok t-ok =
  ι[ interpret-ty-eq T Bool Γ Γ-ok T-ok (lift refl) t-ok ] const Bool.true
interpret-tm false Γ {T} Γ-ok T-ok t-ok =
  ι[ interpret-ty-eq T Bool Γ Γ-ok T-ok (lift refl) t-ok ] const Bool.false
interpret-tm (if t t₁ t₂) Γ {T} Γ-ok T-ok (tt , t-ok , tt , t₁-ok , t₂-ok) =
  if' (interpret-tm t Γ Γ-ok (lift refl) t-ok)
  then' interpret-tm t₁ Γ Γ-ok T-ok t₁-ok
  else' interpret-tm t₂ Γ Γ-ok T-ok t₂-ok
interpret-tm (refl T′ t) Γ {T} Γ-ok T-ok (tt , T′-ok , tt , t-ok , eq-ok) =
  ι[ interpret-ty-eq T (Id T′ t t) Γ Γ-ok T-ok (tt , T′-ok , tt , t-ok , t-ok) eq-ok ]
  M.refl' (interpret-tm t Γ Γ-ok T′-ok t-ok)

interpret-ty-eq Nat Nat Γ Γ-ok T-ok S-ok eq-ok = M.reflᵗʸ
interpret-ty-eq Bool Bool Γ Γ-ok T-ok S-ok eq-ok = M.reflᵗʸ
interpret-ty-eq (T₁ ⇛ T₂) (S₁ ⇛ S₂) Γ Γ-ok (tt , T₁-ok , T₂-ok) (tt , S₁-ok , S₂-ok) (tt , eq₁-ok , eq₂-ok) =
  M.⇛-cong (interpret-ty-eq T₁ S₁ Γ Γ-ok T₁-ok S₁-ok eq₁-ok)
    (interpret-ty-eq T₂ S₂ Γ Γ-ok T₂-ok S₂-ok eq₂-ok)
interpret-ty-eq (T₁ ⊠ T₂) (S₁ ⊠ S₂) Γ Γ-ok (tt , T₁-ok , T₂-ok) (tt , S₁-ok , S₂-ok) (tt , eq₁-ok , eq₂-ok) =
  M.⊠-cong (interpret-ty-eq T₁ S₁ Γ Γ-ok T₁-ok S₁-ok eq₁-ok)
    (interpret-ty-eq T₂ S₂ Γ Γ-ok T₂-ok S₂-ok eq₂-ok)
interpret-ty-eq (Id T t₁ t₂) (Id S s₁ s₂) Γ Γ-ok (tt , T-ok , tt , t₁-ok , t₂-ok) (tt , S-ok , tt , s₁-ok , s₂-ok) (tt , T-eq , tt , eq₁-ok , eq₂-ok) =
  M.Id-cong
    (interpret-ty-eq T S Γ Γ-ok T-ok S-ok T-eq)
    (interpret-tm-eq t₁ s₁ Γ T S Γ-ok T-ok S-ok t₁-ok s₁-ok T-eq eq₁-ok)
    (interpret-tm-eq t₂ s₂ Γ T S Γ-ok T-ok S-ok t₂-ok s₂-ok T-eq eq₂-ok)

-- interpret-tm-eq (ann t₁ ∈ x) (ann t₂ ∈ x₁) Γ T₁ T₂ Γ-ok T₁-ok T₂-ok t₁-ok t₂-ok ty-eq-ok tm-eq-ok =
--   {!!}
-- interpret-tm-eq (var x) (var x₁) Γ T₁ T₂ Γ-ok T₁-ok T₂-ok t₁-ok t₂-ok ty-eq-ok tm-eq-ok = {!!}
-- interpret-tm-eq (TmExpr.lam x t₁) (TmExpr.lam x₁ t₂) Γ T₁ T₂ Γ-ok T₁-ok T₂-ok t₁-ok t₂-ok ty-eq-ok tm-eq-ok = {!!}
-- interpret-tm-eq (TmExpr.app S₁ t₁ t₂) (TmExpr.app S₂ t₃ t₄) Γ T₁ T₂ Γ-ok T₁-ok T₂-ok t₁-ok t₂-ok ty-eq-ok tm-eq-ok = {!!}
-- interpret-tm-eq (lit x) (lit x₁) Γ Nat Nat Γ-ok T₁-ok T₂-ok t₁-ok t₂-ok ty-eq-ok tm-eq-ok = {!!}
-- interpret-tm-eq suc suc Γ (Nat ⇛ Nat) (Nat ⇛ Nat) Γ-ok T₁-ok T₂-ok t₁-ok t₂-ok ty-eq-ok tm-eq-ok =
--   {!!}
-- interpret-tm-eq plus plus Γ (Nat ⇛ Nat ⇛ Nat) (Nat ⇛ Nat ⇛ Nat) Γ-ok T₁-ok T₂-ok t₁-ok t₂-ok ty-eq-ok tm-eq-ok = {!!}
interpret-tm-eq true true Γ Bool Bool Γ-ok T₁-ok T₂-ok t₁-ok t₂-ok ty-eq-ok tm-eq-ok = {!reflᵗᵐ!}
interpret-tm-eq false false Γ Bool Bool Γ-ok T₁-ok T₂-ok t₁-ok t₂-ok ty-eq-ok tm-eq-ok = {!reflᵗᵐ!}
-- interpret-tm-eq (if t₁ t₃ t₄) (if t₂ t₅ t₆) Γ T₁ T₂ Γ-ok T₁-ok T₂-ok t₁-ok t₂-ok ty-eq-ok tm-eq-ok = {!!}
-- interpret-tm-eq (refl x t₁) (refl x₁ t₂) Γ T₁ T₂ Γ-ok T₁-ok T₂-ok t₁-ok t₂-ok ty-eq-ok tm-eq-ok = {!!}
