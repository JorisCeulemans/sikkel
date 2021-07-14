module Experimental.DeepEmbedding.GuardedRecursion.TypeChecker where

open import Data.Maybe
open import Data.Nat hiding (_≟_)
open import Data.Product
open import Data.Unit hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Categories
open import CwF-Structure
open import Modalities
open Modality
open import Types.Functions
open import Types.Discrete
open import Types.Instances
open import GuardedRecursion.Modalities
open import GuardedRecursion.Streams.Guarded


-- Needed for the do-notation below to desugar properly (this operator is
--   not exported by Data.Maybe).
infixl 1 _>>_
_>>_ : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} → Maybe A → Maybe B → Maybe B
just _  >> x = x
nothing >> x = nothing


--------------------------------------------------
-- Expressions representing modes, modalities, types, contexts and terms

data ModeExpr : Set where
  e-★ e-ω : ModeExpr

private
  variable
    m m' : ModeExpr

data ModalityExpr : ModeExpr → ModeExpr → Set where
  e-timeless : ModalityExpr e-★ e-ω

infixr 5 _e→_
data TyExpr : ModeExpr → Set where
  e-Nat : TyExpr m
  _e→_ : TyExpr m → TyExpr m → TyExpr m
  e-mod : ModalityExpr m' m → TyExpr m' → TyExpr m
  e-▻' : TyExpr e-ω → TyExpr e-ω
  e-GStreamN : TyExpr e-ω

data CtxExpr (m : ModeExpr) : Set where
  e-◇ : CtxExpr m
  _,_ : (Γ : CtxExpr m) (T : TyExpr m) → CtxExpr m
  _,lock⟨_⟩ : (Γ : CtxExpr m') → ModalityExpr m m' → CtxExpr m

data TmExpr : ModeExpr → Set where
  e-var : ℕ → TmExpr m
  e-lam : TyExpr m → TmExpr m → TmExpr m
  e-app : TmExpr m → TmExpr m → TmExpr m
  e-lit : ℕ → TmExpr m
  e-suc e-plus : TmExpr m
  e-mod-intro : ModalityExpr m m' → TmExpr m → TmExpr m'
  e-mod-elim : ModalityExpr m m' → TmExpr m' → TmExpr m
  e-next' : TmExpr e-ω → TmExpr e-ω
  e-⊛' : TmExpr e-ω → TmExpr e-ω → TmExpr e-ω
  e-löb : TyExpr e-ω → TmExpr e-ω → TmExpr e-ω
  e-cons e-head e-tail : TmExpr e-ω


-- Deciding whether a type expression is a function type or a modal type and
--   whether a context is of the form Γ ,lock⟨ μ ⟩.

record IsFuncTyExpr (T : TyExpr m) : Set where
  constructor func-ty
  field
    dom cod : TyExpr m
    is-func : T ≡ dom e→ cod

is-func-ty : (T : TyExpr m) → Maybe (IsFuncTyExpr T)
is-func-ty e-Nat = nothing
is-func-ty (T1 e→ T2) = just (func-ty T1 T2 refl)
is-func-ty (e-mod μ T) = nothing
is-func-ty (e-▻' T) = nothing
is-func-ty e-GStreamN = nothing

record IsModalTyExpr (T : TyExpr m) : Set where
  constructor modal-ty
  field
    {n} : ModeExpr
    S : TyExpr n
    μ : ModalityExpr n m
    is-modal : T ≡ e-mod μ S

is-modal-ty : (T : TyExpr m) → Maybe (IsModalTyExpr T)
is-modal-ty e-Nat = nothing
is-modal-ty (T1 e→ T2) = nothing
is-modal-ty (e-mod μ T) = just (modal-ty T μ refl)
is-modal-ty (e-▻' T) = nothing
is-modal-ty e-GStreamN = nothing

record IsLaterTyExpr (T : TyExpr e-ω) : Set where
  constructor later-ty
  field
    S : TyExpr e-ω
    is-later : T ≡ e-▻' S

is-later-ty : (T : TyExpr e-ω) → Maybe (IsLaterTyExpr T)
is-later-ty e-Nat = nothing
is-later-ty (T1 e→ T2) = nothing
is-later-ty (e-mod μ T) = nothing
is-later-ty (e-▻' T) = just (later-ty T refl)
is-later-ty e-GStreamN = nothing

record IsModalCtxExpr (Γ : CtxExpr m) : Set where
  constructor modal-ctx
  field
    {n} : ModeExpr
    Γ' : CtxExpr n
    μ : ModalityExpr m n
    is-modal : Γ ≡ (Γ' ,lock⟨ μ ⟩)

is-modal-ctx : (Γ : CtxExpr m) → Maybe (IsModalCtxExpr Γ)
is-modal-ctx e-◇ = nothing
is-modal-ctx (Γ , T) = nothing
is-modal-ctx (Γ ,lock⟨ μ ⟩) = just (modal-ctx Γ μ refl)


-- Decidable equality for mode, modality and type expressions.

_≟mode_ : (m1 m2 : ModeExpr) → Dec (m1 ≡ m2)
e-★ ≟mode e-★ = yes refl
e-★ ≟mode e-ω = no (λ ())
e-ω ≟mode e-★ = no (λ ())
e-ω ≟mode e-ω = yes refl

_≟modality_ : (μ ρ : ModalityExpr m m') → Dec (μ ≡ ρ)
e-timeless ≟modality e-timeless = yes refl

_≟ty_ : (T1 T2 : TyExpr m) → Dec (T1 ≡ T2)
e-Nat ≟ty e-Nat = yes refl
e-Nat ≟ty (_ e→ _) = no (λ ())
e-Nat ≟ty (e-mod _ _) = no (λ ())
e-Nat ≟ty (e-▻' _) = no (λ ())
e-Nat ≟ty e-GStreamN = no (λ ())
(_ e→ _) ≟ty e-Nat = no (λ ())
(T1 e→ T2) ≟ty (T3 e→ T4) with T1 ≟ty T3 | T2 ≟ty T4
(T1 e→ T2) ≟ty (T1 e→ T2) | yes refl | yes refl = yes refl
(T1 e→ T2) ≟ty (T1 e→ T4) | yes refl | no ne = no (λ { refl → ne refl }) -- (λ e → ne (e→injʳ e))
(T1 e→ T2) ≟ty (T3 e→ T4) | no ne    | _ = no (λ { refl → ne refl }) -- (λ e → ne (e→injˡ e))
(_ e→ _) ≟ty (e-mod _ _) = no (λ ())
(_ e→ _) ≟ty (e-▻' _) = no (λ ())
(_ e→ _) ≟ty e-GStreamN = no (λ ())
(e-mod μ T) ≟ty e-Nat = no (λ ())
(e-mod μ T) ≟ty (_ e→ _) = no (λ ())
(e-mod {m1} μ1 T1) ≟ty (e-mod {m2} μ2 T2) with m1 ≟mode m2
(e-mod {m1} μ1 T1) ≟ty (e-mod {.m1} μ2  T2)  | yes refl with μ1 ≟modality μ2 | T1 ≟ty T2
(e-mod {m1} μ1 T1) ≟ty (e-mod {.m1} .μ1 .T1) | yes refl | yes refl | yes refl = yes refl
(e-mod {m1} μ1 T1) ≟ty (e-mod {.m1} .μ1 T2)  | yes refl | yes refl | no ne = no (λ { refl → ne refl })
(e-mod {m1} μ1 T1) ≟ty (e-mod {.m1} μ2  T2)  | yes refl | no ne    | _ = no (λ { refl → ne refl })
(e-mod {m1} μ1 T1) ≟ty (e-mod {m2}  μ2  T2)  | no ne = no (λ { refl → ne refl })
(e-mod μ T) ≟ty (e-▻' _) = no (λ ())
(e-mod μ T) ≟ty e-GStreamN = no (λ ())
(e-▻' T) ≟ty e-Nat = no (λ ())
(e-▻' T) ≟ty (_ e→ _) = no (λ ())
(e-▻' T) ≟ty (e-mod _ _) = no (λ ())
(e-▻' T) ≟ty (e-▻' S) with T ≟ty S
(e-▻' T) ≟ty (e-▻' .T) | yes refl = yes refl
(e-▻' T) ≟ty (e-▻' S)  | no ne = no (λ { refl → ne refl }) -- (λ e → ne (e-▻'-inj e))
(e-▻' T) ≟ty e-GStreamN = no (λ ())
e-GStreamN ≟ty e-Nat = no (λ ())
e-GStreamN ≟ty (_ e→ _) = no (λ ())
e-GStreamN ≟ty (e-mod _ _) = no (λ ())
e-GStreamN ≟ty (e-▻' _) = no (λ ())
e-GStreamN ≟ty e-GStreamN = yes refl


--------------------------------------------------
-- Interpretation of modes, modalities, types and contexts in a presheaf model

⟦_⟧mode : ModeExpr → Category
⟦ e-★ ⟧mode = ★
⟦ e-ω ⟧mode = ω

⟦_⟧modality : ModalityExpr m m' → Modality ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ e-timeless ⟧modality = timeless

⟦_⟧ty : TyExpr m → ClosedType ⟦ m ⟧mode
⟦ e-Nat ⟧ty = Nat'
⟦ T1 e→ T2 ⟧ty = ⟦ T1 ⟧ty ⇛ ⟦ T2 ⟧ty
⟦ e-mod μ T ⟧ty = mod ⟦ μ ⟧modality ⟦ T ⟧ty
⟦ e-▻' T ⟧ty = ▻' ⟦ T ⟧ty
⟦ e-GStreamN ⟧ty = GStream Nat'

⟦_⟧ctx : CtxExpr m → Ctx ⟦ m ⟧mode
⟦ e-◇ ⟧ctx = ◇
⟦ Γ , T ⟧ctx = ⟦ Γ ⟧ctx ,, ⟦ T ⟧ty
⟦ Γ ,lock⟨ μ ⟩ ⟧ctx = ctx-op ⟦ μ ⟧modality ⟦ Γ ⟧ctx

⟦⟧ty-natural : (T : TyExpr m) → IsClosedNatural ⟦ T ⟧ty
⟦⟧ty-natural e-Nat = discr-closed
⟦⟧ty-natural (T1 e→ T2) = fun-closed {{⟦⟧ty-natural T1}} {{⟦⟧ty-natural T2}}
⟦⟧ty-natural (e-mod μ T) = record { closed-natural = λ σ → ≅ᵗʸ-trans (mod-natural ⟦ μ ⟧modality σ) (mod-cong ⟦ μ ⟧modality (closed-natural {{⟦⟧ty-natural T}} _)) }
⟦⟧ty-natural (e-▻' T) = ▻'-closed {{⟦⟧ty-natural T}}
⟦⟧ty-natural e-GStreamN = gstream-closed


--------------------------------------------------
-- Definition of a typechecker for the deeply embedded language

lookup-ctx : ℕ → CtxExpr m → Maybe (TyExpr m)
lookup-ctx x       e-◇ = nothing
lookup-ctx zero    (Γ , T) = just T
lookup-ctx (suc x) (Γ , T) = lookup-ctx x Γ
lookup-ctx x       (Γ ,lock⟨ μ ⟩) = nothing

infer-type : TmExpr m → CtxExpr m → Maybe (TyExpr m)
infer-type (e-var x) Γ = lookup-ctx x Γ
infer-type (e-lam T b) Γ =  do
  codomain ← infer-type b (Γ , T)
  just (T e→ codomain)
infer-type (e-app t1 t2) Γ = do
  T1 ← infer-type t1 Γ
  func-ty dom cod _ ← is-func-ty T1
  T2 ← infer-type t2 Γ
  decToMaybe (dom ≟ty T2)
  just cod
infer-type (e-lit n) Γ = just e-Nat
infer-type e-suc Γ = just (e-Nat e→ e-Nat)
infer-type e-plus Γ = just (e-Nat e→ e-Nat e→ e-Nat)
infer-type (e-mod-intro μ t) Γ = do
  T ← infer-type t (Γ ,lock⟨ μ ⟩)
  just (e-mod μ T)
infer-type (e-mod-elim {m} {mμ} μ t) Γ = do
  modal-ctx {mρ} Γ' ρ _ ← is-modal-ctx Γ
  refl ← decToMaybe (mμ ≟mode mρ)
  decToMaybe (μ ≟modality ρ)
  S ← infer-type t Γ'
  modal-ty {mκ} T κ _ ← is-modal-ty S
  refl ← decToMaybe (m ≟mode mκ)
  decToMaybe (μ ≟modality κ)
  just T
infer-type (e-next' t) Γ = do
  T ← infer-type t Γ
  just (e-▻' T)
infer-type (e-⊛' f t) Γ = do
  T-f ← infer-type f Γ
  later-ty S _ ← is-later-ty T-f
  func-ty dom cod _ ← is-func-ty S
  T-t ← infer-type t Γ
  later-ty R _ ← is-later-ty T-t
  decToMaybe (R ≟ty dom)
  just (e-▻' cod)
infer-type (e-löb T t) Γ = do
  S ← infer-type t (Γ , e-▻' T)
  decToMaybe (T ≟ty S)
  just T
infer-type e-cons Γ = just ((e-mod e-timeless e-Nat) e→ (e-▻' e-GStreamN) e→ e-GStreamN)
infer-type e-head Γ = just (e-GStreamN e→ (e-mod e-timeless e-Nat))
infer-type e-tail Γ = just (e-GStreamN e→ (e-▻' e-GStreamN))


--------------------------------------------------
-- Interpretation of terms that are accepted by the typechecker
-- in a presheaf model

semantic-type : TmExpr m → CtxExpr m → Set
semantic-type t Γ = maybe′ (λ T → Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty) ⊤ (infer-type t Γ)

interpret-var : (x : ℕ) (Γ : CtxExpr m) → semantic-type (e-var x) Γ
interpret-var x e-◇ = tt
interpret-var zero (Γ , T) = ι⁻¹[ closed-natural {{⟦⟧ty-natural T}} π ] ξ
interpret-var (suc x) (Γ , T) with lookup-ctx x Γ | interpret-var x Γ
interpret-var (suc x) (Γ , T) | just S  | ⟦x⟧ = ι⁻¹[ closed-natural {{⟦⟧ty-natural S}} π ] (⟦x⟧ [ π ]')
interpret-var (suc x) (Γ , T) | nothing | ⟦x⟧ = tt
interpret-var x (Γ ,lock⟨ μ ⟩) = tt

open import Reflection.Tactic.Lambda
⟦_⟧tm-in_ : (t : TmExpr m) (Γ : CtxExpr m) → semantic-type t Γ
⟦ e-var x ⟧tm-in Γ = interpret-var x Γ
⟦ e-lam T b ⟧tm-in Γ with infer-type b (Γ , T) | ⟦ b ⟧tm-in (Γ , T)
⟦ e-lam T b ⟧tm-in Γ | just S  | ⟦b⟧ = lam ⟦ T ⟧ty (ι[ closed-natural {{⟦⟧ty-natural S}} π ] ⟦b⟧)
⟦ e-lam T b ⟧tm-in Γ | nothing | ⟦b⟧ = tt
⟦ e-app t1 t2 ⟧tm-in Γ with infer-type t1 Γ | ⟦ t1 ⟧tm-in Γ
⟦ e-app t1 t2 ⟧tm-in Γ | just T1             | ⟦t1⟧ with is-func-ty T1
⟦ e-app t1 t2 ⟧tm-in Γ | just .(dom e→ cod) | ⟦t1⟧ | just (func-ty dom cod refl) with infer-type t2 Γ | ⟦ t2 ⟧tm-in Γ
⟦ e-app t1 t2 ⟧tm-in Γ | just .(dom e→ cod) | ⟦t1⟧ | just (func-ty dom cod refl) | just T2 | ⟦t2⟧ with dom ≟ty T2
⟦ e-app t1 t2 ⟧tm-in Γ | just .(T2  e→ cod) | ⟦t1⟧ | just (func-ty dom cod refl) | just T2 | ⟦t2⟧ | yes refl = app ⟦t1⟧ ⟦t2⟧
⟦ e-app t1 t2 ⟧tm-in Γ | just .(dom e→ cod) | ⟦t1⟧ | just (func-ty dom cod refl) | just T2 | ⟦t2⟧ | no ne = tt
⟦ e-app t1 t2 ⟧tm-in Γ | just .(dom e→ cod) | ⟦t1⟧ | just (func-ty dom cod refl) | nothing | _ = tt
⟦ e-app t1 t2 ⟧tm-in Γ | just T1             | ⟦t1⟧ | nothing = tt
⟦ e-app t1 t2 ⟧tm-in Γ | nothing | _ = tt
⟦ e-lit n ⟧tm-in Γ = discr n
⟦ e-suc ⟧tm-in Γ = suc'
⟦ e-plus ⟧tm-in Γ = nat-sum
⟦ e-mod-intro μ t ⟧tm-in Γ with infer-type t (Γ ,lock⟨ μ ⟩) | ⟦ t ⟧tm-in (Γ ,lock⟨ μ ⟩)
⟦ e-mod-intro μ t ⟧tm-in Γ | just T  | ⟦t⟧ = mod-intro ⟦ μ ⟧modality ⟦t⟧
⟦ e-mod-intro μ t ⟧tm-in Γ | nothing | ⟦t⟧ = tt
⟦ e-mod-elim μ t ⟧tm-in Γ with is-modal-ctx Γ
⟦ e-mod-elim {m} {mμ} μ t ⟧tm-in .(Γ' ,lock⟨ ρ ⟩) | just (modal-ctx {mρ} Γ' ρ refl) with mμ ≟mode mρ
⟦ e-mod-elim {m} {mμ} μ t ⟧tm-in .(Γ' ,lock⟨ ρ ⟩) | just (modal-ctx {mμ} Γ' ρ refl) | yes refl with μ ≟modality ρ
⟦ e-mod-elim {m} {mμ} μ t ⟧tm-in .(Γ' ,lock⟨ μ ⟩) | just (modal-ctx {mμ} Γ' μ refl) | yes refl | yes refl with infer-type t Γ' | ⟦ t ⟧tm-in Γ'
⟦ e-mod-elim {m} {mμ} μ t ⟧tm-in .(Γ' ,lock⟨ μ ⟩) | just (modal-ctx {mμ} Γ' μ refl) | yes refl | yes refl | just S             | ⟦t⟧ with is-modal-ty S
⟦ e-mod-elim {m} {mμ} μ t ⟧tm-in .(Γ' ,lock⟨ μ ⟩) | just (modal-ctx {mμ} Γ' μ refl) | yes refl | yes refl | just .(e-mod κ T)  | ⟦t⟧ | just (modal-ty {mκ} T κ refl) with m ≟mode mκ
⟦ e-mod-elim {m} {mμ} μ t ⟧tm-in .(Γ' ,lock⟨ μ ⟩) | just (modal-ctx {mμ} Γ' μ refl) | yes refl | yes refl | just .(e-mod κ T)  | ⟦t⟧ | just (modal-ty {m} T κ refl) | yes refl with μ ≟modality κ
⟦ e-mod-elim {m} {mμ} μ t ⟧tm-in .(Γ' ,lock⟨ μ ⟩) | just (modal-ctx {mμ} Γ' μ refl) | yes refl | yes refl | just .(e-mod μ T)  | ⟦t⟧ | just (modal-ty {m} T μ refl) | yes refl | yes refl = mod-elim ⟦ μ ⟧modality ⟦t⟧
⟦ e-mod-elim {m} {mμ} μ t ⟧tm-in .(Γ' ,lock⟨ μ ⟩) | just (modal-ctx {mμ} Γ' μ refl) | yes refl | yes refl | just .(e-mod κ T)  | ⟦t⟧ | just (modal-ty {m} T κ refl) | yes refl | no _ = tt
⟦ e-mod-elim {m} {mμ} μ t ⟧tm-in .(Γ' ,lock⟨ μ ⟩) | just (modal-ctx {mμ} Γ' μ refl) | yes refl | yes refl | just .(e-mod κ T)  | ⟦t⟧ | just (modal-ty {mκ} T κ refl) | no ne = tt
⟦ e-mod-elim {m} {mμ} μ t ⟧tm-in .(Γ' ,lock⟨ μ ⟩) | just (modal-ctx {mμ} Γ' μ refl) | yes refl | yes refl | just S             | ⟦t⟧ | nothing = tt
⟦ e-mod-elim {m} {mμ} μ t ⟧tm-in .(Γ' ,lock⟨ μ ⟩) | just (modal-ctx {mμ} Γ' μ refl) | yes refl | yes refl | nothing            | ⟦t⟧ = tt
⟦ e-mod-elim {m} {mμ} μ t ⟧tm-in .(Γ' ,lock⟨ ρ ⟩) | just (modal-ctx {mμ} Γ' ρ refl) | yes refl | no _ = tt
⟦ e-mod-elim {m} {mμ} μ t ⟧tm-in .(Γ' ,lock⟨ ρ ⟩) | just (modal-ctx {mρ} Γ' ρ refl) | no _ = tt
⟦ e-mod-elim μ t ⟧tm-in Γ                        | nothing = tt
⟦ e-next' t ⟧tm-in Γ with infer-type t Γ | ⟦ t ⟧tm-in Γ
⟦ e-next' t ⟧tm-in Γ | just T  | ⟦t⟧ = next' ⟦t⟧
⟦ e-next' t ⟧tm-in Γ | nothing | ⟦t⟧ = tt
⟦ e-⊛' f t ⟧tm-in Γ with infer-type f Γ | ⟦ f ⟧tm-in Γ
⟦ e-⊛' f t ⟧tm-in Γ | just T-f                  | ⟦f⟧ with is-later-ty T-f
⟦ e-⊛' f t ⟧tm-in Γ | just (e-▻' S)             | ⟦f⟧ | just (later-ty S refl) with is-func-ty S
⟦ e-⊛' f t ⟧tm-in Γ | just (e-▻' (dom e→ cod))  | ⟦f⟧ | just (later-ty (dom e→ cod) refl) | just (func-ty dom cod refl) with infer-type t Γ | ⟦ t ⟧tm-in Γ
⟦ e-⊛' f t ⟧tm-in Γ | just (e-▻' (dom e→ cod))  | ⟦f⟧ | just (later-ty (dom e→ cod) refl) | just (func-ty dom cod refl) | just T-t      | ⟦t⟧ with is-later-ty T-t
⟦ e-⊛' f t ⟧tm-in Γ | just (e-▻' (dom e→ cod))  | ⟦f⟧ | just (later-ty (dom e→ cod) refl) | just (func-ty dom cod refl) | just (e-▻' R) | ⟦t⟧ | just (later-ty R refl) with R ≟ty dom
⟦ e-⊛' f t ⟧tm-in Γ | just (e-▻' (R   e→ cod))  | ⟦f⟧ | just (later-ty (R   e→ cod) refl) | just (func-ty R   cod refl) | just (e-▻' R) | ⟦t⟧ | just (later-ty R refl) | yes refl = ⟦f⟧ ⊛' ⟦t⟧
⟦ e-⊛' f t ⟧tm-in Γ | just (e-▻' (dom e→ cod))  | ⟦f⟧ | just (later-ty (dom e→ cod) refl) | just (func-ty dom cod refl) | just (e-▻' R) | ⟦t⟧ | just (later-ty R refl) | no _ = tt
⟦ e-⊛' f t ⟧tm-in Γ | just (e-▻' (dom e→ cod))  | ⟦f⟧ | just (later-ty (dom e→ cod) refl) | just (func-ty dom cod refl) | just T-t      | ⟦t⟧ | nothing = tt
⟦ e-⊛' f t ⟧tm-in Γ | just (e-▻' (dom e→ cod))  | ⟦f⟧ | just (later-ty (dom e→ cod) refl) | just (func-ty dom cod refl) | nothing       | ⟦t⟧ = tt
⟦ e-⊛' f t ⟧tm-in Γ | just (e-▻' S)             | ⟦f⟧ | just (later-ty S refl) | nothing = tt
⟦ e-⊛' f t ⟧tm-in Γ | just T-f                  | ⟦f⟧ | nothing = tt
⟦ e-⊛' f t ⟧tm-in Γ | nothing                   | ⟦f⟧ = tt
⟦ e-löb T t ⟧tm-in Γ with infer-type t (Γ , e-▻' T) | ⟦ t ⟧tm-in (Γ , e-▻' T)
⟦ e-löb T t ⟧tm-in Γ | just S  | ⟦t⟧ with T ≟ty S
⟦ e-löb T t ⟧tm-in Γ | just .T | ⟦t⟧ | yes refl = löb' ⟦ T ⟧ty (ι[ closed-natural {{⟦⟧ty-natural T}} π ] ⟦t⟧)
⟦ e-löb T t ⟧tm-in Γ | just S  | ⟦t⟧ | no ne = tt
⟦ e-löb T t ⟧tm-in Γ | nothing | ⟦t⟧ = tt
⟦ e-cons ⟧tm-in Γ = g-cons
⟦ e-head ⟧tm-in Γ = g-head
⟦ e-tail ⟧tm-in Γ = g-tail
