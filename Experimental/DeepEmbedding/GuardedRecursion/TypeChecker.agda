module Experimental.DeepEmbedding.GuardedRecursion.TypeChecker where

open import Data.Maybe
open import Data.Nat hiding (_≟_)
open import Data.Product hiding (map)
open import Data.Unit hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Categories
open import CwF-Structure
open import Modalities
open Modality
open import Types.Functions
open import Types.Discrete
open import Types.Products
open import Types.Instances
open import GuardedRecursion.Modalities
open import GuardedRecursion.Streams.Guarded


--------------------------------------------------
-- Expressions representing modes, modalities, types, contexts and terms

data ModeExpr : Set where
  e-★ e-ω : ModeExpr

private
  variable
    m m' : ModeExpr

data ModalityExpr : ModeExpr → ModeExpr → Set where
  e-timeless : ModalityExpr e-★ e-ω
  e-allnow : ModalityExpr e-ω e-★

infixr 5 _e→_
data TyExpr : ModeExpr → Set where
  e-Nat : TyExpr m
  _e→_ : TyExpr m → TyExpr m → TyExpr m
  _e-⊠_ : TyExpr m → TyExpr m → TyExpr m
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
  e-pair : TmExpr m → TmExpr m → TmExpr m
  e-fst e-snd : TmExpr m → TmExpr m
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
is-func-ty (T1 e-⊠ T2) = nothing
is-func-ty (e-mod μ T) = nothing
is-func-ty (e-▻' T) = nothing
is-func-ty e-GStreamN = nothing

record IsProdTyExpr (T : TyExpr m) : Set where
  constructor prod-ty
  field
    comp₁ comp₂ : TyExpr m
    is-prod : T ≡ comp₁ e-⊠ comp₂

is-prod-ty : (T : TyExpr m) → Maybe (IsProdTyExpr T)
is-prod-ty e-Nat = nothing
is-prod-ty (T1 e→ T2) = nothing
is-prod-ty (T1 e-⊠ T2) = just (prod-ty T1 T2 refl)
is-prod-ty (e-mod μ T) = nothing
is-prod-ty (e-▻' T) = nothing
is-prod-ty e-GStreamN = nothing

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
is-modal-ty (T1 e-⊠ T2) = nothing
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
is-later-ty (T1 e-⊠ T2) = nothing
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
e-allnow ≟modality e-allnow = yes refl

_≟ty_ : (T1 T2 : TyExpr m) → Dec (T1 ≡ T2)
e-Nat ≟ty e-Nat = yes refl
e-Nat ≟ty (_ e→ _) = no (λ ())
e-Nat ≟ty (_ e-⊠ _) = no (λ ())
e-Nat ≟ty (e-mod _ _) = no (λ ())
e-Nat ≟ty (e-▻' _) = no (λ ())
e-Nat ≟ty e-GStreamN = no (λ ())
(_ e→ _) ≟ty e-Nat = no (λ ())
(T1 e→ T2) ≟ty (T3 e→ T4) with T1 ≟ty T3 | T2 ≟ty T4
(T1 e→ T2) ≟ty (T1 e→ T2) | yes refl | yes refl = yes refl
(T1 e→ T2) ≟ty (T1 e→ T4) | yes refl | no ne = no (λ { refl → ne refl })
(T1 e→ T2) ≟ty (T3 e→ T4) | no ne    | _ = no (λ { refl → ne refl })
(_ e→ _) ≟ty (_ e-⊠ _) = no (λ ())
(_ e→ _) ≟ty (e-mod _ _) = no (λ ())
(_ e→ _) ≟ty (e-▻' _) = no (λ ())
(_ e→ _) ≟ty e-GStreamN = no (λ ())
(_ e-⊠ _) ≟ty e-Nat = no (λ ())
(_ e-⊠ _) ≟ty (_ e→ _) = no (λ ())
(T1 e-⊠ T2) ≟ty (T3 e-⊠ T4) with T1 ≟ty T3 | T2 ≟ty T4
(T1 e-⊠ T2) ≟ty (T1 e-⊠ T2) | yes refl | yes refl = yes refl
(T1 e-⊠ T2) ≟ty (T1 e-⊠ T4) | yes refl | no ne = no (λ { refl → ne refl })
(T1 e-⊠ T2) ≟ty (T3 e-⊠ T4) | no ne    | _ = no (λ { refl → ne refl })
(_ e-⊠ _) ≟ty (e-mod _ _) = no (λ ())
(_ e-⊠ _) ≟ty (e-▻' _) = no (λ ())
(_ e-⊠ _) ≟ty e-GStreamN = no (λ ())
(e-mod μ T) ≟ty e-Nat = no (λ ())
(e-mod μ T) ≟ty (_ e→ _) = no (λ ())
(e-mod μ T) ≟ty (_ e-⊠ _) = no (λ ())
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
(e-▻' T) ≟ty (_ e-⊠ _) = no (λ ())
(e-▻' T) ≟ty (e-mod _ _) = no (λ ())
(e-▻' T) ≟ty (e-▻' S) with T ≟ty S
(e-▻' T) ≟ty (e-▻' .T) | yes refl = yes refl
(e-▻' T) ≟ty (e-▻' S)  | no ne = no (λ { refl → ne refl })
(e-▻' T) ≟ty e-GStreamN = no (λ ())
e-GStreamN ≟ty e-Nat = no (λ ())
e-GStreamN ≟ty (_ e→ _) = no (λ ())
e-GStreamN ≟ty (_ e-⊠ _) = no (λ ())
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
⟦ e-allnow ⟧modality = allnow

⟦_⟧ty : TyExpr m → ClosedType ⟦ m ⟧mode
⟦ e-Nat ⟧ty = Nat'
⟦ T1 e→ T2 ⟧ty = ⟦ T1 ⟧ty ⇛ ⟦ T2 ⟧ty
⟦ T1 e-⊠ T2 ⟧ty = ⟦ T1 ⟧ty ⊠ ⟦ T2 ⟧ty
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
⟦⟧ty-natural (T1 e-⊠ T2) = prod-closed {{⟦⟧ty-natural T1}} {{⟦⟧ty-natural T2}}
⟦⟧ty-natural (e-mod μ T) = record { closed-natural = λ σ → ≅ᵗʸ-trans (mod-natural ⟦ μ ⟧modality σ) (mod-cong ⟦ μ ⟧modality (closed-natural {{⟦⟧ty-natural T}} _)) }
⟦⟧ty-natural (e-▻' T) = ▻'-closed {{⟦⟧ty-natural T}}
⟦⟧ty-natural e-GStreamN = gstream-closed


--------------------------------------------------
-- Definition of a typechecker for the deeply embedded language
--   and interpretaion of well-typed terms in a presheaf model

record InferInterpretResult (Γ : CtxExpr m) : Set where
  constructor _,_
  field
    type : TyExpr m
    interpretation : Tm ⟦ Γ ⟧ctx ⟦ type ⟧ty

infer-interpret-var : ℕ → (Γ : CtxExpr m) → Maybe (InferInterpretResult Γ)
infer-interpret-var x       e-◇ = nothing
infer-interpret-var zero    (Γ , T) = just (T , ι⁻¹[ closed-natural {{⟦⟧ty-natural T}} π ] ξ)
infer-interpret-var (suc x) (Γ , T) = do
  S , ⟦x⟧ ← infer-interpret-var x Γ
  just (S , ι⁻¹[ closed-natural {{⟦⟧ty-natural S}} π ] (⟦x⟧ [ π ]'))
infer-interpret-var x       (Γ ,lock⟨ μ ⟩) = nothing

infer-interpret : TmExpr m → (Γ : CtxExpr m) → Maybe (InferInterpretResult Γ)
infer-interpret (e-var x) Γ = infer-interpret-var x Γ
infer-interpret (e-lam T b) Γ = do
  S , ⟦b⟧ ← infer-interpret b (Γ , T)
  just (T e→ S , lam ⟦ T ⟧ty (ι[ closed-natural {{⟦⟧ty-natural S}} π ] ⟦b⟧))
infer-interpret (e-app t1 t2) Γ = do
  T1 , ⟦t1⟧ ← infer-interpret t1 Γ
  func-ty dom cod refl ← is-func-ty T1
  T2 , ⟦t2⟧ ← infer-interpret t2 Γ
  refl ← decToMaybe (dom ≟ty T2)
  just (cod , app ⟦t1⟧ ⟦t2⟧)
infer-interpret (e-lit n) Γ = just (e-Nat , discr n)
infer-interpret e-suc Γ = just (e-Nat e→ e-Nat , suc')
infer-interpret e-plus Γ = just (e-Nat e→ e-Nat e→ e-Nat , nat-sum)
infer-interpret (e-pair t s) Γ = do
  T , ⟦t⟧ ← infer-interpret t Γ
  S , ⟦s⟧ ← infer-interpret s Γ
  just (T e-⊠ S , pair $ ⟦t⟧ $ ⟦s⟧)
infer-interpret (e-fst p) Γ = do
  P , ⟦p⟧ ← infer-interpret p Γ
  prod-ty T S refl ← is-prod-ty P
  just (T , fst $ ⟦p⟧)
infer-interpret (e-snd p) Γ = do
  P , ⟦p⟧ ← infer-interpret p Γ
  prod-ty T S refl ← is-prod-ty P
  just (S , snd $ ⟦p⟧)
infer-interpret (e-mod-intro μ t) Γ = do
  T , ⟦t⟧ ← infer-interpret t (Γ ,lock⟨ μ ⟩)
  just (e-mod μ T , mod-intro ⟦ μ ⟧modality ⟦t⟧)
infer-interpret (e-mod-elim {m} {mμ} μ t) Γ = do
  modal-ctx {mρ} Γ' ρ refl ← is-modal-ctx Γ
  refl ← decToMaybe (mμ ≟mode mρ)
  refl ← decToMaybe (μ ≟modality ρ)
  S , ⟦t⟧ ← infer-interpret t Γ'
  modal-ty {mκ} T κ refl ← is-modal-ty S
  refl ← decToMaybe (m ≟mode mκ)
  refl ← decToMaybe (μ ≟modality κ)
  just (T , mod-elim ⟦ μ ⟧modality ⟦t⟧)
infer-interpret (e-next' t) Γ = do
  T , ⟦t⟧ ← infer-interpret t Γ
  just (e-▻' T , next' ⟦t⟧)
infer-interpret (e-⊛' f t) Γ = do
  T-f , ⟦f⟧ ← infer-interpret f Γ
  later-ty S refl ← is-later-ty T-f
  func-ty dom cod refl ← is-func-ty S
  T-t , ⟦t⟧ ← infer-interpret t Γ
  later-ty R refl ← is-later-ty T-t
  refl ← decToMaybe (R ≟ty dom)
  just (e-▻' cod , ⟦f⟧ ⊛' ⟦t⟧)
infer-interpret (e-löb T t) Γ = do
  S , ⟦t⟧ ← infer-interpret t (Γ , e-▻' T)
  refl ← decToMaybe (T ≟ty S)
  just (T , löb' ⟦ T ⟧ty (ι[ closed-natural {{⟦⟧ty-natural T}} π ] ⟦t⟧))
infer-interpret e-cons Γ = just ((e-mod e-timeless e-Nat) e→ (e-▻' e-GStreamN) e→ e-GStreamN , g-cons)
infer-interpret e-head Γ = just (e-GStreamN e→ (e-mod e-timeless e-Nat) , g-head)
infer-interpret e-tail Γ = just (e-GStreamN e→ (e-▻' e-GStreamN) , g-tail)

infer-type : TmExpr m → CtxExpr m → Maybe (TyExpr m)
infer-type t Γ = map InferInterpretResult.type (infer-interpret t Γ)

⟦_⟧tm-in_ : (t : TmExpr m) (Γ : CtxExpr m) → maybe′ (λ T → Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty) ⊤ (infer-type t Γ)
⟦ t ⟧tm-in Γ with infer-interpret t Γ
⟦ t ⟧tm-in Γ | just (T , ⟦t⟧) = ⟦t⟧
⟦ t ⟧tm-in Γ | nothing = tt
