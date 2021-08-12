module Experimental.DeepEmbedding.GuardedRecursion.TypeChecker where

open import Data.Maybe
open import Data.Nat hiding (_≟_)
open import Data.Product hiding (map)
open import Data.Unit hiding (_≟_)
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
    m m' m'' : ModeExpr

data ModalityExpr : ModeExpr → ModeExpr → Set where
  e-𝟙 : ModalityExpr m m
  _e-ⓜ_ : ModalityExpr m' m'' → ModalityExpr m m' → ModalityExpr m m''
  e-timeless : ModalityExpr e-★ e-ω
  e-allnow : ModalityExpr e-ω e-★
  e-later : ModalityExpr e-ω e-ω


infixr 5 _e→_
data TyExpr : ModeExpr → Set where
  e-Nat : TyExpr m
  e-Bool : TyExpr m
  _e→_ : TyExpr m → TyExpr m → TyExpr m
  _e-⊠_ : TyExpr m → TyExpr m → TyExpr m
  e-mod : ModalityExpr m' m → TyExpr m' → TyExpr m
  e-▻' : TyExpr e-ω → TyExpr e-ω
  e-GStream : TyExpr e-★ → TyExpr e-ω

data CtxExpr (m : ModeExpr) : Set where
  e-◇ : CtxExpr m
  _,_ : (Γ : CtxExpr m) (T : TyExpr m) → CtxExpr m
  _,lock⟨_⟩ : (Γ : CtxExpr m') → ModalityExpr m m' → CtxExpr m

infixl 5 _e-⊛'_
data TmExpr : ModeExpr → Set where
  e-ann_∈_ : TmExpr m → TyExpr m → TmExpr m   -- term with type annotation
  e-var : ℕ → TmExpr m
  e-lam : TyExpr m → TmExpr m → TmExpr m
  e-app : TmExpr m → TmExpr m → TmExpr m
  e-lit : ℕ → TmExpr m
  e-suc e-plus : TmExpr m
  e-true e-false : TmExpr m
  e-if : TmExpr m → TmExpr m → TmExpr m → TmExpr m
  e-timeless-if : TmExpr e-ω → TmExpr e-ω → TmExpr e-ω → TmExpr e-ω
  e-pair : TmExpr m → TmExpr m → TmExpr m
  e-fst e-snd : TmExpr m → TmExpr m
  e-mod-intro : ModalityExpr m m' → TmExpr m → TmExpr m'
  e-mod-elim : ModalityExpr m m' → TmExpr m' → TmExpr m
  e-next' : TmExpr e-ω → TmExpr e-ω
  _e-⊛'_ : TmExpr e-ω → TmExpr e-ω → TmExpr e-ω
  e-löb : TyExpr e-ω → TmExpr e-ω → TmExpr e-ω
  e-cons e-head e-tail : TyExpr e-★ → TmExpr e-ω


-- Deciding whether a type expression is a function type, a product type or
--   a modal type and whether a context is of the form Γ ,lock⟨ μ ⟩.

record IsFuncTyExpr (T : TyExpr m) : Set where
  constructor func-ty
  field
    dom cod : TyExpr m
    is-func : T ≡ dom e→ cod

is-func-ty : (T : TyExpr m) → Maybe (IsFuncTyExpr T)
is-func-ty e-Nat = nothing
is-func-ty e-Bool = nothing
is-func-ty (T1 e→ T2) = just (func-ty T1 T2 refl)
is-func-ty (T1 e-⊠ T2) = nothing
is-func-ty (e-mod μ T) = nothing
is-func-ty (e-▻' T) = nothing
is-func-ty (e-GStream T) = nothing

record IsProdTyExpr (T : TyExpr m) : Set where
  constructor prod-ty
  field
    comp₁ comp₂ : TyExpr m
    is-prod : T ≡ comp₁ e-⊠ comp₂

is-prod-ty : (T : TyExpr m) → Maybe (IsProdTyExpr T)
is-prod-ty e-Nat = nothing
is-prod-ty e-Bool = nothing
is-prod-ty (T1 e→ T2) = nothing
is-prod-ty (T1 e-⊠ T2) = just (prod-ty T1 T2 refl)
is-prod-ty (e-mod μ T) = nothing
is-prod-ty (e-▻' T) = nothing
is-prod-ty (e-GStream T) = nothing

record IsModalTyExpr (T : TyExpr m) : Set where
  constructor modal-ty
  field
    {n} : ModeExpr
    S : TyExpr n
    μ : ModalityExpr n m
    is-modal : T ≡ e-mod μ S

is-modal-ty : (T : TyExpr m) → Maybe (IsModalTyExpr T)
is-modal-ty e-Nat = nothing
is-modal-ty e-Bool = nothing
is-modal-ty (T1 e→ T2) = nothing
is-modal-ty (T1 e-⊠ T2) = nothing
is-modal-ty (e-mod μ T) = just (modal-ty T μ refl)
is-modal-ty (e-▻' T) = nothing
is-modal-ty (e-GStream T) = nothing

record IsLaterTyExpr (T : TyExpr e-ω) : Set where
  constructor later-ty
  field
    S : TyExpr e-ω
    is-later : T ≡ e-▻' S

is-later-ty : (T : TyExpr e-ω) → Maybe (IsLaterTyExpr T)
is-later-ty e-Nat = nothing
is-later-ty e-Bool = nothing
is-later-ty (T1 e→ T2) = nothing
is-later-ty (T1 e-⊠ T2) = nothing
is-later-ty (e-mod μ T) = nothing
is-later-ty (e-▻' T) = just (later-ty T refl)
is-later-ty (e-GStream T) = nothing

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


-- Checking equality for mode, modality and type expressions.

_≟mode_ : (m1 m2 : ModeExpr) → Maybe (m1 ≡ m2)
e-★ ≟mode e-★ = just refl
e-ω ≟mode e-ω = just refl
_ ≟mode _ = nothing

_≟modality_ : (μ ρ : ModalityExpr m m') → Maybe (μ ≡ ρ)
e-𝟙 ≟modality e-𝟙 = just refl
e-timeless ≟modality e-timeless = just refl
e-allnow ≟modality e-allnow = just refl
e-later ≟modality e-later = just refl
_ ≟modality _ = nothing

_≟ty_ : (T1 T2 : TyExpr m) → Maybe (T1 ≡ T2)
e-Nat ≟ty e-Nat = just refl
(T1 e→ T2) ≟ty (T3 e→ T4) = do
  refl ← T1 ≟ty T3
  refl ← T2 ≟ty T4
  just refl
(T1 e-⊠ T2) ≟ty (T3 e-⊠ T4) = do
  refl ← T1 ≟ty T3
  refl ← T2 ≟ty T4
  just refl
(e-mod {m1} μ1 T1) ≟ty (e-mod {m2} μ2 T2) = do
  refl ← m1 ≟mode m2
  refl ← μ1 ≟modality μ2
  refl ← T1 ≟ty T2
  just refl
(e-▻' T) ≟ty (e-▻' S) = map (cong e-▻') (T ≟ty S)
(e-GStream T) ≟ty (e-GStream S) = map (cong e-GStream) (T ≟ty S)
_ ≟ty _ = nothing


--------------------------------------------------
-- Interpretation of modes, modalities, types and contexts in a presheaf model

⟦_⟧mode : ModeExpr → Category
⟦ e-★ ⟧mode = ★
⟦ e-ω ⟧mode = ω

⟦_⟧modality : ModalityExpr m m' → Modality ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ e-𝟙 ⟧modality = 𝟙
⟦ μ e-ⓜ ρ ⟧modality = ⟦ μ ⟧modality ⓜ ⟦ ρ ⟧modality
⟦ e-timeless ⟧modality = timeless
⟦ e-allnow ⟧modality = allnow
⟦ e-later ⟧modality = later

⟦_⟧ty : TyExpr m → ClosedType ⟦ m ⟧mode
⟦ e-Nat ⟧ty = Nat'
⟦ e-Bool ⟧ty = Bool'
⟦ T1 e→ T2 ⟧ty = ⟦ T1 ⟧ty ⇛ ⟦ T2 ⟧ty
⟦ T1 e-⊠ T2 ⟧ty = ⟦ T1 ⟧ty ⊠ ⟦ T2 ⟧ty
⟦ e-mod μ T ⟧ty = mod ⟦ μ ⟧modality ⟦ T ⟧ty
⟦ e-▻' T ⟧ty = ▻' ⟦ T ⟧ty
⟦ e-GStream T ⟧ty = GStream ⟦ T ⟧ty

⟦_⟧ctx : CtxExpr m → Ctx ⟦ m ⟧mode
⟦ e-◇ ⟧ctx = ◇
⟦ Γ , T ⟧ctx = ⟦ Γ ⟧ctx ,, ⟦ T ⟧ty
⟦ Γ ,lock⟨ μ ⟩ ⟧ctx = ctx-op ⟦ μ ⟧modality ⟦ Γ ⟧ctx

⟦⟧ty-natural : (T : TyExpr m) → IsClosedNatural ⟦ T ⟧ty
⟦⟧ty-natural e-Nat = discr-closed
⟦⟧ty-natural e-Bool = discr-closed
⟦⟧ty-natural (T1 e→ T2) = fun-closed {{⟦⟧ty-natural T1}} {{⟦⟧ty-natural T2}}
⟦⟧ty-natural (T1 e-⊠ T2) = prod-closed {{⟦⟧ty-natural T1}} {{⟦⟧ty-natural T2}}
⟦⟧ty-natural (e-mod μ T) = record { closed-natural = λ σ → ≅ᵗʸ-trans (mod-natural ⟦ μ ⟧modality σ) (mod-cong ⟦ μ ⟧modality (closed-natural {{⟦⟧ty-natural T}} _)) }
⟦⟧ty-natural (e-▻' T) = ▻'-closed {{⟦⟧ty-natural T}}
⟦⟧ty-natural (e-GStream T) = gstream-closed {{⟦⟧ty-natural T}}


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
infer-interpret (e-ann t ∈ T) Γ = do
  T' , ⟦t⟧ ← infer-interpret t Γ
  refl ← T ≟ty T'
  just (T , ⟦t⟧)
infer-interpret (e-var x) Γ = infer-interpret-var x Γ
infer-interpret (e-lam T b) Γ = do
  S , ⟦b⟧ ← infer-interpret b (Γ , T)
  just (T e→ S , lam ⟦ T ⟧ty (ι[ closed-natural {{⟦⟧ty-natural S}} π ] ⟦b⟧))
infer-interpret (e-app t1 t2) Γ = do
  T1 , ⟦t1⟧ ← infer-interpret t1 Γ
  func-ty dom cod refl ← is-func-ty T1
  T2 , ⟦t2⟧ ← infer-interpret t2 Γ
  refl ← dom ≟ty T2
  just (cod , app ⟦t1⟧ ⟦t2⟧)
infer-interpret (e-lit n) Γ = just (e-Nat , discr n)
infer-interpret e-suc Γ = just (e-Nat e→ e-Nat , suc')
infer-interpret e-plus Γ = just (e-Nat e→ e-Nat e→ e-Nat , nat-sum)
infer-interpret e-true Γ = just (e-Bool , true')
infer-interpret e-false Γ = just (e-Bool , false')
infer-interpret (e-if c t f) Γ = do
  C , ⟦c⟧ ← infer-interpret c Γ
  refl ← C ≟ty e-Bool
  T , ⟦t⟧ ← infer-interpret t Γ
  F , ⟦f⟧ ← infer-interpret f Γ
  refl ← T ≟ty F
  just (T , if' ⟦c⟧ then' ⟦t⟧ else' ⟦f⟧)
infer-interpret (e-timeless-if c t f) Γ = do
  C , ⟦c⟧ ← infer-interpret c Γ
  modal-ty {m} B μ refl ← is-modal-ty C
  refl ← m ≟mode e-★
  refl ← μ ≟modality e-timeless
  refl ← B ≟ty e-Bool
  T , ⟦t⟧ ← infer-interpret t Γ
  F , ⟦f⟧ ← infer-interpret f Γ
  refl ← T ≟ty F
  just (T , timeless-if' ⟦c⟧ then' ⟦t⟧ else' ⟦f⟧)
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
  refl ← mμ ≟mode mρ
  refl ← μ ≟modality ρ
  S , ⟦t⟧ ← infer-interpret t Γ'
  modal-ty {mκ} T κ refl ← is-modal-ty S
  refl ← m ≟mode mκ
  refl ← μ ≟modality κ
  just (T , mod-elim ⟦ μ ⟧modality ⟦t⟧)
infer-interpret (e-next' t) Γ = do
  T , ⟦t⟧ ← infer-interpret t Γ
  just (e-▻' T , next' ⟦t⟧)
infer-interpret (f e-⊛' t) Γ = do
  T-f , ⟦f⟧ ← infer-interpret f Γ
  later-ty S refl ← is-later-ty T-f
  func-ty dom cod refl ← is-func-ty S
  T-t , ⟦t⟧ ← infer-interpret t Γ
  later-ty R refl ← is-later-ty T-t
  refl ← R ≟ty dom
  just (e-▻' cod , ⟦f⟧ ⊛' ⟦t⟧)
infer-interpret (e-löb T t) Γ = do
  S , ⟦t⟧ ← infer-interpret t (Γ , e-▻' T)
  refl ← T ≟ty S
  just (T , löb' ⟦ T ⟧ty (ι[ closed-natural {{⟦⟧ty-natural T}} π ] ⟦t⟧))
infer-interpret (e-cons T) Γ = just (e-mod e-timeless T e→ e-▻' (e-GStream T) e→ e-GStream T , g-cons)
infer-interpret (e-head T) Γ = just (e-GStream T e→ e-mod e-timeless T , g-head)
infer-interpret (e-tail T) Γ = just (e-GStream T e→ e-▻' (e-GStream T) , g-tail)

infer-type : TmExpr m → CtxExpr m → Maybe (TyExpr m)
infer-type t Γ = map InferInterpretResult.type (infer-interpret t Γ)

⟦_⟧tm-in_ : (t : TmExpr m) (Γ : CtxExpr m) → maybe′ (λ T → Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty) ⊤ (infer-type t Γ)
⟦ t ⟧tm-in Γ with infer-interpret t Γ
⟦ t ⟧tm-in Γ | just (T , ⟦t⟧) = ⟦t⟧
⟦ t ⟧tm-in Γ | nothing = tt
