module Experimental.DependentTypes.DeepEmbedding.Alternative2-bis where

open import Data.Empty
open import Data.Nat renaming (_≟_ to _≟nat_)
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Model.BaseCategory as M
open import Model.CwF-Structure as M hiding (_,,_)
open import Model.Type.Discrete as M
open import Model.Type.Function as M hiding (_⇛_)
open import Model.Type.Product as M hiding (_⊠_)

import Experimental.DependentTypes.Model.IdentityType
module M-id = Experimental.DependentTypes.Model.IdentityType.Alternative1
open M-id hiding (Id)

open import Experimental.DependentTypes.DeepEmbedding.Syntax.FullyAnnotated
open import MSTT.TCMonad


-- TODO: Use of de Bruijn indices is incorrect, e.g. shift needed when extending context.

is-yes : ∀ {ℓ} {A : Set ℓ} → Dec A → TCM ⊤
is-yes (yes _) = return tt
is-yes (no _)  = type-error ""

_≟tm_ : TmExpr → TmExpr → TCM ⊤
_≟ty_ : TyExpr → TyExpr → TCM ⊤

(ann t ∈ T) ≟tm (ann s ∈ S) = (t ≟tm s) >> (T ≟ty S)
var x ≟tm var y = is-yes (x ≟nat y)
lam T b ≟tm lam S c = (T ≟ty S) >> (b ≟tm c)
(app R1 t1 s1) ≟tm (app R2 t2 s2) = (R1 ≟ty R2) >> (t1 ≟tm t2) >> (s1 ≟tm s2)
lit n ≟tm lit m = is-yes (n ≟nat m)
suc ≟tm suc = return tt
plus ≟tm plus = return tt
true ≟tm true = return tt
false ≟tm false = return tt
if c t f ≟tm if c' t' f' = (c ≟tm c') >> (t ≟tm t') >> (f ≟tm f')
pair t1 s1 ≟tm pair t2 s2 = (t1 ≟tm t2) >> (s1 ≟tm s2)
fst S1 p1 ≟tm fst S2 p2 = (S1 ≟ty S2) >> (p1 ≟tm p2)
snd T1 p1 ≟tm snd T2 p2 = (T1 ≟ty T2) >> (p1 ≟tm p2)
refl T t ≟tm refl S s = (T ≟ty S) >> (t ≟tm s)
t ≟tm s = type-error ""

Nat ≟ty Nat = return tt
Bool ≟ty Bool = return tt
(T1 ⇛ S1) ≟ty (T2 ⇛ S2) = (T1 ≟ty T2) >> (S1 ≟ty S2)
(T1 ⊠ S1) ≟ty (T2 ⊠ S2) = (T1 ≟ty T2) >> (S1 ≟ty S2)
Id T1 t1 s1 ≟ty Id T2 t2 s2 = (T1 ≟ty T2) >> (t1 ≟tm t2) >> (s1 ≟tm s2)
T ≟ty S = type-error ""

_≃ᵗʸ_ : TyExpr → TyExpr → Set
T ≃ᵗʸ S = (T ≟ty S) ≡ ok tt

_≃ᵗᵐ_ : TmExpr → TmExpr → Set
t ≃ᵗᵐ s = (t ≟tm s) ≡ ok tt


infix 3 _⊢var_∈_
_⊢var_∈_ : CtxExpr → ℕ → TyExpr → Set
◇      ⊢var n     ∈ T = ⊥
Γ ,, A ⊢var zero  ∈ T = T ≃ᵗʸ A
Γ ,, A ⊢var suc n ∈ T = Γ ⊢var n ∈ T

infix 3 _⊢ctx _⊢ty_ _⊢_∈_
_⊢ctx : CtxExpr → Set
_⊢ty_ : CtxExpr → TyExpr → Set
_⊢_∈_ : CtxExpr → TmExpr → TyExpr → Set

◇ ⊢ctx = ⊤
Γ ,, T ⊢ctx = Γ ⊢ctx × Γ ⊢ty T

_ ⊢ty Nat = ⊤
_ ⊢ty Bool = ⊤
Γ ⊢ty T ⇛ S = Γ ⊢ty T × Γ ⊢ty S
Γ ⊢ty T ⊠ S = Γ ⊢ty T × Γ ⊢ty S
Γ ⊢ty Id R t s = (Γ ⊢ty R) × (Γ ⊢ t ∈ R) × (Γ ⊢ s ∈ R)

Γ ⊢ (ann t ∈ S) ∈ T = (Γ ⊢ty S) × (Γ ⊢ t ∈ S) × (S ≃ᵗʸ T)
Γ ⊢ var x ∈ T = Γ ⊢var x ∈ T
Γ ⊢ lam A t ∈ R = (Γ ⊢ty A) × Σ[ T ∈ TyExpr ] (R ≃ᵗʸ (A ⇛ T)) × (Γ ,, A ⊢ t ∈ T)
Γ ⊢ app T f t ∈ S = (Γ ⊢ f ∈ T ⇛ S) × (Γ ⊢ t ∈ T)
Γ ⊢ lit n ∈ T = T ≃ᵗʸ Nat
Γ ⊢ suc ∈ T = T ≃ᵗʸ (Nat ⇛ Nat)
Γ ⊢ plus ∈ T = T ≃ᵗʸ (Nat ⇛ Nat ⇛ Nat)
Γ ⊢ true ∈ T = T ≃ᵗʸ Bool
Γ ⊢ false ∈ T = T ≃ᵗʸ Bool
Γ ⊢ if c t f ∈ T = (Γ ⊢ c ∈ Bool) × (Γ ⊢ t ∈ T) × (Γ ⊢ f ∈ T)
Γ ⊢ pair t s ∈ P = Σ (IsProdTy P) λ { (prod-ty T S) → (Γ ⊢ t ∈ T) × (Γ ⊢ s ∈ S) }
Γ ⊢ fst S p ∈ T = Σ (IsProdTy S) λ { (prod-ty S₁ S₂) → Γ ⊢ty S × (T ≃ᵗʸ S₁) × Γ ⊢ p ∈ S}
Γ ⊢ snd T p ∈ S = Γ ⊢ p ∈ T ⊠ S
Γ ⊢ refl T t ∈ S = S ≃ᵗʸ Id T t t

≃ᵗʸ-valid : {T S : TyExpr} {Γ : CtxExpr} →
            T ≃ᵗʸ S → Γ ⊢ty T → Γ ⊢ty S
≃ᵗʸ-valid T=S Γ⊢T = {!!}

{-
weaken-ty : {Γ : CtxExpr} (A T : TyExpr) → Γ ⊢ty T → Γ ,, A ⊢ty T
weaken-ty A Nat Γ⊢T = tt
weaken-ty A Bool Γ⊢T = tt
weaken-ty A (T ⇛ S) (Γ⊢T , Γ⊢S) = weaken-ty A T Γ⊢T , weaken-ty A S Γ⊢S
weaken-ty A (T ⊠ S) (Γ⊢T , Γ⊢S) = weaken-ty A T Γ⊢T , weaken-ty A S Γ⊢S
weaken-ty A (Id R t s) (Γ⊢R , Γ⊢t∈R , Γ⊢s∈R) = weaken-ty A R Γ⊢R , {!!} , {!!}
-}

interpret-ctx : (Γ : CtxExpr) → Γ ⊢ctx → Ctx ★
interpret-ty : (T : TyExpr) {Γ : CtxExpr} → Γ ⊢ty T → {Γ-ok : Γ ⊢ctx} → Ty (interpret-ctx Γ Γ-ok)
interpret-tm : (t : TmExpr) {Γ : CtxExpr} {Γ-ok : Γ ⊢ctx} (T : TyExpr) (T-ok : Γ ⊢ty T) →
               Γ ⊢ t ∈ T → Tm (interpret-ctx Γ Γ-ok) (interpret-ty T T-ok)
≃ᵗʸ-sound : {Γ : CtxExpr} {Γ-ok : Γ ⊢ctx} {T S : TyExpr} {T-ok : Γ ⊢ty T} {S-ok : Γ ⊢ty S} →
            T ≃ᵗʸ S → interpret-ty T T-ok {Γ-ok} ≅ᵗʸ interpret-ty S S-ok

interpret-ctx ◇ Γ-ok = M.◇
interpret-ctx (Γ ,, T) (Γ-ok , T-ok) = interpret-ctx Γ Γ-ok M.,, interpret-ty T T-ok

interpret-ty Nat T-ok = M.Nat'
interpret-ty Bool T-ok = M.Bool'
interpret-ty (T ⇛ S) (T-ok , S-ok) = interpret-ty T T-ok M.⇛ interpret-ty S S-ok
interpret-ty (T ⊠ S) (T-ok , S-ok) = interpret-ty T T-ok M.⊠ interpret-ty S S-ok
interpret-ty (Id R t s) (R-ok , t∈R , s∈R) = M-id.Id (interpret-tm t R R-ok t∈R)
                                                     (interpret-tm s R R-ok s∈R)

interpret-tm (ann t ∈ S) T T-ok (Γ⊢S , Γ⊢t∈S , S=T) = ι⁻¹[ ≃ᵗʸ-sound {T-ok = Γ⊢S} {S-ok = T-ok} S=T ] interpret-tm t S Γ⊢S Γ⊢t∈S
interpret-tm (var x) T T-ok t∈T = {!!}
interpret-tm (lam A t) R R-ok (Γ⊢A , T , R=A⇛T , Γ,,A⊢t∈T) =
  {!ι⁻¹[ ≃ᵗʸ-sound R=A⇛T ] M.lam (interpret-ty A Γ⊢A) (ι[ {!{-naturality-}!} ] interpret-tm t T {!!} Γ,,A⊢t∈T)!}
interpret-tm (app T f t) S S-ok (Γ⊢f∈T⇛S , Γ⊢t∈T) = {!M.app (interpret-tm f (T ⇛ S) {!!} Γ⊢f∈T⇛S)
                                                        (interpret-tm t T {!!} Γ⊢t∈T)!}
interpret-tm (lit n) T T-ok T=Nat = ι[ ≃ᵗʸ-sound {T = T} T=Nat ] M.discr n
interpret-tm suc (Nat ⇛ Nat) T-ok T=Nat⇛Nat = M.suc'
interpret-tm plus T T-ok T=Nat⇛Nat⇛Nat = {!ι[ ≃ᵗʸ-sound {T = T} {!T=Nat⇛Nat⇛Nat!} ] M.nat-sum!} -- same
interpret-tm true T T-ok T=Bool = ι[ ≃ᵗʸ-sound {T = T} T=Bool ] M.true'
interpret-tm false T T-ok T=Bool = ι[ ≃ᵗʸ-sound {T = T} T=Bool ] M.false'
interpret-tm (if c t f) T T-ok (Γ⊢c∈Bool , Γ⊢t∈T , Γ⊢f∈T) =
  M.if' interpret-tm c Bool tt Γ⊢c∈Bool
  then' interpret-tm t T T-ok Γ⊢t∈T
  else' interpret-tm f T T-ok Γ⊢f∈T
interpret-tm (pair t s) P (Γ⊢T , Γ⊢S) (prod-ty T S , Γ⊢t∈T , Γ⊢s∈S) = M.pair $ interpret-tm t T Γ⊢T Γ⊢t∈T
                                                                             $ interpret-tm s S Γ⊢S Γ⊢s∈S
interpret-tm (fst .(S₁ ⊠ S₂) p) T T-ok (prod-ty S₁ S₂ , (S₁-ok , S₂-ok) , T≃S₁ , Γ⊢p∈S) =
  M.fst $ (ι[ M.⊠-cong (≃ᵗʸ-sound {T = T} {S = S₁} {T-ok} {S₁-ok} T≃S₁) M.≅ᵗʸ-refl ]
    interpret-tm p (S₁ ⊠ S₂) (S₁-ok , S₂-ok) Γ⊢p∈S)
interpret-tm (snd T p) S S-ok Γ⊢p∈T⊠S = {!M.snd $ interpret-tm p (T ⊠ S) {!!} Γ⊢p∈T⊠S!}
interpret-tm (refl T t) R R-ok T=Idtt = {!ι[ ≃ᵗʸ-sound T=Idtt ] {!!}!}

≃ᵗʸ-sound = {!!}
