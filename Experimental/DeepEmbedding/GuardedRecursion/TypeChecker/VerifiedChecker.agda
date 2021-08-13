--------------------------------------------------
-- Definition of a typechecker for the deeply embedded language
--   and interpretation of well-typed terms in a presheaf model
--------------------------------------------------

module Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.VerifiedChecker where

open import Data.Nat
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Categories
open import CwF-Structure
open import Modalities
open Modality
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import Types.Instances
open import GuardedRecursion.Modalities
open import GuardedRecursion.Streams.Guarded

open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Syntax
open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Monad
open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Equality

private
  variable
    m m' : ModeExpr


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
-- Implementation of the verified type checker.

infix 1 _,_
record InferInterpretResult (Γ : CtxExpr m) : Set where
  constructor _,_
  field
    type : TyExpr m
    interpretation : Tm ⟦ Γ ⟧ctx ⟦ type ⟧ty

infer-interpret-var : ℕ → (Γ : CtxExpr m) → TCM (InferInterpretResult Γ)
infer-interpret-var x       e-◇ = type-error "There is a reference to a variable that does not exist in this context."
infer-interpret-var zero    (Γ , T) = return (T , ι⁻¹[ closed-natural {{⟦⟧ty-natural T}} π ] ξ)
infer-interpret-var (suc x) (Γ , T) = do
  S , ⟦x⟧ ← infer-interpret-var x Γ
  return (S , ι⁻¹[ closed-natural {{⟦⟧ty-natural S}} π ] (⟦x⟧ [ π ]'))
infer-interpret-var x       (Γ ,lock⟨ μ ⟩) = type-error "Impossible to directly use a variable from a locked context."

infer-interpret : TmExpr m → (Γ : CtxExpr m) → TCM (InferInterpretResult Γ)
infer-interpret (e-ann t ∈ T) Γ = do
  T' , ⟦t⟧ ← infer-interpret t Γ
  refl ← T ≟ty T'
  return (T , ⟦t⟧)
infer-interpret (e-var x) Γ = infer-interpret-var x Γ
infer-interpret (e-lam T b) Γ = do
  S , ⟦b⟧ ← infer-interpret b (Γ , T)
  return (T e→ S , lam ⟦ T ⟧ty (ι[ closed-natural {{⟦⟧ty-natural S}} π ] ⟦b⟧))
infer-interpret (e-app t1 t2) Γ = do
  T1 , ⟦t1⟧ ← infer-interpret t1 Γ
  func-ty dom cod refl ← is-func-ty T1
  T2 , ⟦t2⟧ ← infer-interpret t2 Γ
  refl ← dom ≟ty T2
  return (cod , app ⟦t1⟧ ⟦t2⟧)
infer-interpret (e-lit n) Γ = return (e-Nat , discr n)
infer-interpret e-suc Γ = return (e-Nat e→ e-Nat , suc')
infer-interpret e-plus Γ = return (e-Nat e→ e-Nat e→ e-Nat , nat-sum)
infer-interpret e-true Γ = return (e-Bool , true')
infer-interpret e-false Γ = return (e-Bool , false')
infer-interpret (e-if c t f) Γ = do
  C , ⟦c⟧ ← infer-interpret c Γ
  refl ← C ≟ty e-Bool
  T , ⟦t⟧ ← infer-interpret t Γ
  F , ⟦f⟧ ← infer-interpret f Γ
  refl ← T ≟ty F
  return (T , if' ⟦c⟧ then' ⟦t⟧ else' ⟦f⟧)
infer-interpret (e-timeless-if c t f) Γ = do
  C , ⟦c⟧ ← infer-interpret c Γ
  modal-ty {m} B μ refl ← is-modal-ty C
  refl ← m ≟mode e-★
  refl ← μ ≟modality e-timeless
  refl ← B ≟ty e-Bool
  T , ⟦t⟧ ← infer-interpret t Γ
  F , ⟦f⟧ ← infer-interpret f Γ
  refl ← T ≟ty F
  return (T , timeless-if' ⟦c⟧ then' ⟦t⟧ else' ⟦f⟧)
infer-interpret (e-pair t s) Γ = do
  T , ⟦t⟧ ← infer-interpret t Γ
  S , ⟦s⟧ ← infer-interpret s Γ
  return (T e-⊠ S , pair $ ⟦t⟧ $ ⟦s⟧)
infer-interpret (e-fst p) Γ = do
  P , ⟦p⟧ ← infer-interpret p Γ
  prod-ty T S refl ← is-prod-ty P
  return (T , fst $ ⟦p⟧)
infer-interpret (e-snd p) Γ = do
  P , ⟦p⟧ ← infer-interpret p Γ
  prod-ty T S refl ← is-prod-ty P
  return (S , snd $ ⟦p⟧)
infer-interpret (e-mod-intro μ t) Γ = do
  T , ⟦t⟧ ← infer-interpret t (Γ ,lock⟨ μ ⟩)
  return (e-mod μ T , mod-intro ⟦ μ ⟧modality ⟦t⟧)
infer-interpret (e-mod-elim {m} {mμ} μ t) Γ = do
  modal-ctx {mρ} Γ' ρ refl ← is-modal-ctx Γ
  refl ← mμ ≟mode mρ
  refl ← μ ≟modality ρ
  S , ⟦t⟧ ← infer-interpret t Γ'
  modal-ty {mκ} T κ refl ← is-modal-ty S
  refl ← m ≟mode mκ
  refl ← μ ≟modality κ
  return (T , mod-elim ⟦ μ ⟧modality ⟦t⟧)
infer-interpret (e-next' t) Γ = do
  T , ⟦t⟧ ← infer-interpret t Γ
  return (e-▻' T , next' ⟦t⟧)
infer-interpret (f e-⊛' t) Γ = do
  T-f , ⟦f⟧ ← infer-interpret f Γ
  later-ty S refl ← is-later-ty T-f
  func-ty dom cod refl ← is-func-ty S
  T-t , ⟦t⟧ ← infer-interpret t Γ
  later-ty R refl ← is-later-ty T-t
  refl ← R ≟ty dom
  return (e-▻' cod , ⟦f⟧ ⊛' ⟦t⟧)
infer-interpret (e-löb T t) Γ = do
  S , ⟦t⟧ ← infer-interpret t (Γ , e-▻' T)
  refl ← T ≟ty S
  return (T , löb' ⟦ T ⟧ty (ι[ closed-natural {{⟦⟧ty-natural T}} π ] ⟦t⟧))
infer-interpret (e-cons T) Γ = return (e-mod e-timeless T e→ e-▻' (e-GStream T) e→ e-GStream T , g-cons)
infer-interpret (e-head T) Γ = return (e-GStream T e→ e-mod e-timeless T , g-head)
infer-interpret (e-tail T) Γ = return (e-GStream T e→ e-▻' (e-GStream T) , g-tail)

infer-type : TmExpr m → CtxExpr m → TCM (TyExpr m)
infer-type t Γ = map InferInterpretResult.type (infer-interpret t Γ)

⟦_⟧tm-in_ : (t : TmExpr m) (Γ : CtxExpr m) → tcm-elim (λ _ → ⊤) (λ T → Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty) (infer-type t Γ)
⟦ t ⟧tm-in Γ with infer-interpret t Γ
⟦ t ⟧tm-in Γ | type-error _ = tt
⟦ t ⟧tm-in Γ | ok (T , ⟦t⟧)  = ⟦t⟧
