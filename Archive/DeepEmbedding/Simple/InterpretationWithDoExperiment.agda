open import Model.BaseCategory

module Archive.DeepEmbedding.Simple.InterpretationWithDoExperiment {C : Category} where

open import Data.Fin hiding (_+_; _≟_)
open import Data.Maybe hiding (_>>=_)
open import Data.Nat hiding (_≟_)
open import Data.Product
open import Data.Unit hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.CwF-Structure
open import Model.Type.Function
open import Model.Type.Discrete

private
  variable
    n : ℕ


-- Needed for the do-notation below to desugar properly (this operator is
--   not exported by Data.Maybe).
_>>_ : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} → Maybe A → Maybe B → Maybe B
ma >> mb = ma Data.Maybe.>>= (λ _ → mb)


--------------------------------------------------
-- Expressions representing types, contexts and terms

data TyExpr : Set where
  e-bool : TyExpr
  _e→_ : (e1 e2 : TyExpr) → TyExpr

data CtxExpr : ℕ → Set where
  e-◇ : CtxExpr 0
  _,_ : ∀ {n} → (Γ : CtxExpr n) (T : TyExpr) → CtxExpr (1 + n)

data TmExpr (n : ℕ) : Set where
  e-var : Fin n → TmExpr n
  e-lam : TyExpr → TmExpr (1 + n) → TmExpr n
  e-app : TmExpr n → TmExpr n → TmExpr n
  e-true e-false : TmExpr n
  e-if : TmExpr n → TmExpr n → TmExpr n → TmExpr n


-- Deciding whether a type expression is a function type.

record IsFuncTyExpr (T : TyExpr) : Set where
  constructor func-ty
  field
    dom cod : TyExpr
    is-func : T ≡ dom e→ cod

is-func-ty : (T : TyExpr) → Maybe (IsFuncTyExpr T)
is-func-ty e-bool = nothing
is-func-ty (T1 e→ T2) = just (func-ty T1 T2 refl)


-- Decidable equality for type expressions.

e→injˡ : {T T' S S' : TyExpr} → (T e→ S) ≡ (T' e→ S') → T ≡ T'
e→injˡ refl = refl

e→injʳ : {T T' S S' : TyExpr} → (T e→ S) ≡ (T' e→ S') → S ≡ S'
e→injʳ refl = refl

_≟_ : (T1 T2 : TyExpr) → Dec (T1 ≡ T2)
e-bool ≟ e-bool = yes refl
e-bool ≟ (_ e→ _) = no (λ ())
(_ e→ _) ≟ e-bool = no (λ ())
(T1 e→ T2) ≟ (T3 e→ T4) with T1 ≟ T3 | T2 ≟ T4
(T1 e→ T2) ≟ (T1 e→ T2) | yes refl | yes refl = yes refl
(T1 e→ T2) ≟ (T1 e→ T4) | yes refl | no ne = no (λ e → ne (e→injʳ e))
(T1 e→ T2) ≟ (T3 e→ T4) | no ne    | _ = no (λ e → ne (e→injˡ e))


--------------------------------------------------
-- Interpretation of types and contexts in a presheaf model

⟦_⟧ty : TyExpr → ClosedType C
⟦ e-bool ⟧ty = Bool'
⟦ T1 e→ T2 ⟧ty = ⟦ T1 ⟧ty ⇛ ⟦ T2 ⟧ty

⟦_⟧ctx : CtxExpr n → Ctx C
⟦ e-◇ ⟧ctx = ◇
⟦ Γ , T ⟧ctx = ⟦ Γ ⟧ctx ,, ⟦ T ⟧ty

instance
  ⟦⟧ty-natural : {T : TyExpr} → IsClosedNatural ⟦ T ⟧ty
  ⟦⟧ty-natural {e-bool} = discr-closed
  ⟦⟧ty-natural {T1 e→ T2} = fun-closed {{⟦⟧ty-natural {T1}}} {{⟦⟧ty-natural {T2}}}


--------------------------------------------------
-- Definition of a typechecker for the deeply embedded language

lookup-ctx : Fin n → CtxExpr n → TyExpr
lookup-ctx zero    (Γ , T) = T
lookup-ctx (suc i) (Γ , T) = lookup-ctx i Γ

module InferType where

  open Data.Maybe using (_>>=_)

  infer-type : TmExpr n → CtxExpr n → Maybe TyExpr
  infer-type (e-var x) Γ = just (lookup-ctx x Γ)
  infer-type (e-lam T b) Γ = do
    codomain ← infer-type b (Γ , T)
    just (T e→ codomain)
  infer-type (e-app t1 t2) Γ = do
    T1 ← infer-type t1 Γ
    func-ty dom cod _ ← is-func-ty T1
    T2 ← infer-type t2 Γ
    decToMaybe (dom ≟ T2)
    just cod
  infer-type e-true Γ = just e-bool
  infer-type e-false Γ = just e-bool
  infer-type (e-if t-c t-t t-f) Γ = do
    T-c ← infer-type t-c Γ
    decToMaybe (T-c ≟ e-bool)
    T-t ← infer-type t-t Γ
    T-f ← infer-type t-f Γ
    decToMaybe (T-t ≟ T-f)
    just T-t

open InferType


--------------------------------------------------
-- Interpretation of terms that are accepted by the typechecker
-- in a presheaf model

InterpretResult : CtxExpr n → Maybe TyExpr → Set
InterpretResult Γ = maybe′ (λ T → Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty) ⊤

module InterpretTerm where

  data SingleOrPair (A : Set) : (B : A → Set) → Set₁ where
    single : A → SingleOrPair A (λ _ → ⊤)
    pair : {B : A → Set} → (a : A) → B a → SingleOrPair A B

  BindResult : {A B : Set} (C : B → Set) {D : Maybe A → Set}
               (x : SingleOrPair (Maybe A) D) (f : A → Maybe B) →
               Set
  BindResult {A = A} C {D} (single ma) f =
    ((a : A) → maybe′ C ⊤ (f a)) → maybe′ C ⊤ (ma Data.Maybe.>>= f)
  BindResult {A = A} C {D} (pair ma _) f =
    ((p : Σ[ a ∈ A ] D (just a)) → maybe′ C ⊤ (f (proj₁ p))) → maybe′ C ⊤ (ma Data.Maybe.>>= f)

  _>>=_ : {A B : Set} {C : B → Set} {D : Maybe A → Set}
          {f : A → Maybe B}
          (x : SingleOrPair (Maybe A) D) → BindResult C x f
  _>>=_ (single (just a)) = λ g → g a
  _>>=_ (single nothing ) = λ _ → tt
  _>>=_ (pair (just a) d) = λ g → g (a , d)
  _>>=_ (pair nothing  d) = λ _ → tt

  ⟦_⟧tm-in_ : (t : TmExpr n) (Γ : CtxExpr n) → InterpretResult Γ (infer-type t Γ)
  infer-interpret : (t : TmExpr n) (Γ : CtxExpr n) → SingleOrPair (Maybe TyExpr) (InterpretResult Γ)

  infer-interpret t Γ = pair (infer-type t Γ) (⟦ t ⟧tm-in Γ)

  ⟦ e-var zero    ⟧tm-in (Γ , T) = ι⁻¹[ closed-natural {{⟦⟧ty-natural {T}}} π ] ξ
  ⟦ e-var (suc x) ⟧tm-in (Γ , T) = ι⁻¹[ closed-natural {{⟦⟧ty-natural {lookup-ctx x Γ}}} π ] ((⟦ e-var x ⟧tm-in Γ) [ π ]')
  ⟦ e-lam T b ⟧tm-in Γ = do
    S , ⟦b⟧  ← infer-interpret b (Γ , T)
    lam ⟦ T ⟧ty (ι[ closed-natural {{⟦⟧ty-natural {S}}} π ] ⟦b⟧)
  ⟦ e-app t1 t2 ⟧tm-in Γ = do
    T1 , ⟦t1⟧ ← infer-interpret t1 Γ
    func-ty dom cod refl ← single (is-func-ty T1)
    T2 , ⟦t2⟧ ← infer-interpret t2 Γ
    refl ← single (decToMaybe (dom ≟ T2))
    app ⟦t1⟧ ⟦t2⟧
  ⟦ e-true ⟧tm-in Γ = true'
  ⟦ e-false ⟧tm-in Γ = false'
  ⟦ e-if t-c t-t t-f ⟧tm-in Γ = do
    T-c , ⟦t-c⟧ ← infer-interpret t-c Γ
    refl ← single (decToMaybe (T-c ≟ e-bool))
    T-t , ⟦t-t⟧ ← infer-interpret t-t Γ
    T-f , ⟦t-f⟧ ← infer-interpret t-f Γ
    refl ← single (decToMaybe (T-t ≟ T-f))
    if' ⟦t-c⟧ then' ⟦t-t⟧ else' ⟦t-f⟧

{-
  ⟦_⟧tm-in_ : (t : TmExpr n) (Γ : CtxExpr n) → InterpretResult t Γ
  ⟦ e-var zero    ⟧tm-in (Γ , T) = ι⁻¹[ closed-natural {{⟦⟧ty-natural {T}}} π ] ξ
  ⟦ e-var (suc x) ⟧tm-in (Γ , T) = ι⁻¹[ closed-natural {{⟦⟧ty-natural {lookup-ctx x Γ}}} π ] ((⟦ e-var x ⟧tm-in Γ) [ π ]')
  ⟦ e-lam T b ⟧tm-in Γ with infer-type b (Γ , T) | ⟦ b ⟧tm-in (Γ , T)
  ⟦ e-lam T b ⟧tm-in Γ | just S | ⟦b⟧ = lam ⟦ T ⟧ty (ι[ closed-natural {{⟦⟧ty-natural {S}}} π ] ⟦b⟧)
  ⟦ e-lam T b ⟧tm-in Γ | nothing | _ = tt
  ⟦ e-app t1 t2 ⟧tm-in Γ with infer-type t1 Γ | ⟦ t1 ⟧tm-in Γ
  ⟦ e-app t1 t2 ⟧tm-in Γ | just T1             | ⟦t1⟧ with is-func-ty T1
  ⟦ e-app t1 t2 ⟧tm-in Γ | just .(dom e→ cod) | ⟦t1⟧ | just (func-ty dom cod refl) with infer-type t2 Γ | ⟦ t2 ⟧tm-in Γ
  ⟦ e-app t1 t2 ⟧tm-in Γ | just .(dom e→ cod) | ⟦t1⟧ | just (func-ty dom cod refl) | just T2 | ⟦t2⟧ with dom ≟ T2
  ⟦ e-app t1 t2 ⟧tm-in Γ | just .(T2  e→ cod) | ⟦t1⟧ | just (func-ty dom cod refl) | just T2 | ⟦t2⟧ | yes refl = app ⟦t1⟧ ⟦t2⟧
  ⟦ e-app t1 t2 ⟧tm-in Γ | just .(dom e→ cod) | ⟦t1⟧ | just (func-ty dom cod refl) | just T2 | ⟦t2⟧ | no ne = tt
  ⟦ e-app t1 t2 ⟧tm-in Γ | just .(dom e→ cod) | ⟦t1⟧ | just (func-ty dom cod refl) | nothing | _ = tt
  ⟦ e-app t1 t2 ⟧tm-in Γ | just T1             | ⟦t1⟧ | nothing = tt
  ⟦ e-app t1 t2 ⟧tm-in Γ | nothing | _ = tt
  ⟦ e-true ⟧tm-in Γ = true'
  ⟦ e-false ⟧tm-in Γ = false'
  ⟦ e-if t-c t-t t-f ⟧tm-in Γ with infer-type t-c Γ | ⟦ t-c ⟧tm-in Γ
  ⟦ e-if t-c t-t t-f ⟧tm-in Γ | just T-c     | ⟦t-c⟧ with T-c ≟ e-bool
  ⟦ e-if t-c t-t t-f ⟧tm-in Γ | just .e-bool | ⟦t-c⟧ | yes refl with infer-type t-t Γ | ⟦ t-t ⟧tm-in Γ
  ⟦ e-if t-c t-t t-f ⟧tm-in Γ | just .e-bool | ⟦t-c⟧ | yes refl | just T-t | ⟦t-t⟧ with infer-type t-f Γ | ⟦ t-f ⟧tm-in Γ
  ⟦ e-if t-c t-t t-f ⟧tm-in Γ | just .e-bool | ⟦t-c⟧ | yes refl | just T-t | ⟦t-t⟧ | just T-f | ⟦t-f⟧ with T-t ≟ T-f
  ⟦ e-if t-c t-t t-f ⟧tm-in Γ | just .e-bool | ⟦t-c⟧ | yes refl | just T-t | ⟦t-t⟧ | just T-f | ⟦t-f⟧ | yes refl = if' ⟦t-c⟧ then' ⟦t-t⟧ else' ⟦t-f⟧
  ⟦ e-if t-c t-t t-f ⟧tm-in Γ | just .e-bool | ⟦t-c⟧ | yes refl | just T-t | ⟦t-t⟧ | just T-f | ⟦t-f⟧ | no _ = tt
  ⟦ e-if t-c t-t t-f ⟧tm-in Γ | just .e-bool | ⟦t-c⟧ | yes refl | just T-t | ⟦t-t⟧ | nothing  | ⟦t-f⟧ = tt
  ⟦ e-if t-c t-t t-f ⟧tm-in Γ | just .e-bool | ⟦t-c⟧ | yes refl | nothing  | ⟦t-t⟧ = tt
  ⟦ e-if t-c t-t t-f ⟧tm-in Γ | just T-c     | ⟦t-c⟧ | no _ = tt
  ⟦ e-if t-c t-t t-f ⟧tm-in Γ | nothing      | ⟦t-c⟧ = tt
-}
