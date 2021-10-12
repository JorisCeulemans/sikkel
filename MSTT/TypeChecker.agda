--------------------------------------------------
-- Sound type checker for MSTT
-- The main function in this file is `infer-interpret`.
--------------------------------------------------

open import MSTT.Parameter.ModeTheory
open import MSTT.Parameter.TypeExtension using (TyExt)
open import MSTT.Parameter.TermExtension using (TmExt)

module MSTT.TypeChecker (mt : ModeTheory) (ty-ext : TyExt mt) (tm-ext : TmExt mt ty-ext) where


open import Data.Bool hiding (T)
open import Data.List hiding (_++_)
open import Data.Nat
open import Data.Product using (proj₁; proj₂)
open import Data.String renaming (_==_ to _=string=_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure as M hiding (◇; _,,_)
open import Model.CwF-Structure.Reflection.SubstitutionSequence
open import Model.Modality as M hiding (𝟙; _ⓜ_; ⟨_∣_⟩; _,lock⟨_⟩; mod-intro; mod-elim; coe)
open import Model.Type.Discrete as M hiding (Nat'; Bool')
open import Model.Type.Function as M hiding (_⇛_; lam; app)
open import Model.Type.Product as M hiding (_⊠_; pair; fst; snd)

open import MSTT.TCMonad
open import MSTT.Syntax.Type mt ty-ext
open import MSTT.Syntax.Context mt ty-ext
open import MSTT.Syntax.Term mt ty-ext tm-ext
open import MSTT.Equivalence mt ty-ext
open import MSTT.InterpretTypes mt ty-ext
open import MSTT.TypeChecker.ResultType mt ty-ext

open ModeTheory mt
open TmExt tm-ext
open MSTT.Parameter.TermExtension mt ty-ext hiding (TmExt)

private
  variable
    m m' m'' : ModeExpr
    margs : List ModeExpr


--------------------------------------------------
-- Checking + interpretation of variables

-- When checking and interpreting a variable x in a context Γ, all other variables
--   to the right of x are pruned away, locks are kept (in a lock sequence).
--   It is then tested whether the composition of all locks to the right of x
--   is equivalent to the unit modality 𝟙, after which the variable can be
--   interpreted via M.ξ.

-- A value of type LockSeq m m' is a sequence of (compatible) modalities, the first
--   of which has codomain mode m', and the last of which has domain mode m (i.e. they
--   can be composed in the order they appear in the sequence to get a modality from
--   m to m').
data LockSeq : ModeExpr → ModeExpr → Set where
  [] : LockSeq m m
  _,,_ : LockSeq m'' m' → ModalityExpr m m'' → LockSeq m m'

compose-lock-seq : LockSeq m m' → ModalityExpr m m'
compose-lock-seq [] = 𝟙
compose-lock-seq (locks ,, μ) = compose-lock-seq locks ⓜ μ

apply-lock-seq : CtxExpr m' → LockSeq m m' → CtxExpr m
apply-lock-seq Γ [] = Γ
apply-lock-seq Γ (locks ,, μ) = (apply-lock-seq Γ locks) ,lock⟨ μ ⟩

apply-compose-lock-seq : (Γ : CtxExpr m') (locks : LockSeq m m') →
                         ⟦ apply-lock-seq Γ locks ⟧ctx ≅ᶜ ⟦ Γ ,lock⟨ compose-lock-seq locks ⟩ ⟧ctx
apply-compose-lock-seq Γ [] = ≅ᶜ-sym (eq-lock 𝟙-interpretation ⟦ Γ ⟧ctx)
apply-compose-lock-seq Γ (locks ,, μ) = begin
  lock ⟦ μ ⟧modality ⟦ apply-lock-seq Γ locks ⟧ctx
    ≅⟨ ctx-functor-cong (ctx-functor ⟦ μ ⟧modality) (apply-compose-lock-seq Γ locks) ⟩
  lock ⟦ μ ⟧modality (lock ⟦ compose-lock-seq locks ⟧modality ⟦ Γ ⟧ctx)
    ≅˘⟨ eq-lock (ⓜ-interpretation (compose-lock-seq locks) μ) ⟦ Γ ⟧ctx ⟩
  lock ⟦ compose-lock-seq locks ⓜ μ ⟧modality ⟦ Γ ⟧ctx ∎
  where open ≅ᶜ-Reasoning

record PruneCtxResult (Γ : CtxExpr m) (x : String) : Set where
  constructor prune-ctx-result
  field
    n : ModeExpr
    Γ' : CtxExpr n
    T : TyExpr n
    locks : LockSeq m n
    σ : ⟦ Γ ⟧ctx ⇒ ⟦ apply-lock-seq (Γ' , x ∈ T) locks ⟧ctx

prune-ctx-until-var : (x : String) (Γ : CtxExpr m) → TCM (PruneCtxResult Γ x)
prune-ctx-until-var x ◇ = type-error ("The variable " ++ x ++ " is not in scope.")
prune-ctx-until-var x (Γ , y ∈ T) with x =string= y
prune-ctx-until-var x (Γ , y ∈ T) | true = return (prune-ctx-result _ Γ T [] (M.id-subst _))
prune-ctx-until-var x (Γ , y ∈ T) | false = do
  prune-ctx-result n Γ' S locks σ ← prune-ctx-until-var x Γ
  return (prune-ctx-result n Γ' S locks (σ M.⊚ M.π))
prune-ctx-until-var x (Γ ,lock⟨ μ ⟩) = do
  prune-ctx-result n Γ' S locks σ ← prune-ctx-until-var x Γ
  return (prune-ctx-result n Γ' S (locks ,, μ) (M.lock-fmap ⟦ μ ⟧modality σ))

infer-interpret-var : String → (Γ : CtxExpr m) → TCM (InferInterpretResult Γ)
infer-interpret-var {m = m} x Γ = do
  prune-ctx-result n Γ' T locks σ ← prune-ctx-until-var x Γ
  refl ← m ≟mode n
  locks=𝟙 ← modify-error-msg (_++ " when looking for variable " ++ x ++ " in context " ++ show-ctx Γ)
                             (compose-lock-seq locks ≃ᵐ? 𝟙)
  return (T , (ι⁻¹[ ≅ᵗʸ-trans (ty-subst-seq-cong (π ∷ _ ∷ σ ◼) (_ ◼) ⟦ T ⟧ty ≅ˢ-refl) (closed-natural {{⟦⟧ty-natural T}} _) ]
              ((ιc[ ≅ᶜ-trans (apply-compose-lock-seq (Γ' , x ∈ T) locks)
                             (eq-lock (≅ᵐ-trans locks=𝟙 𝟙-interpretation) ⟦ Γ' , x ∈ T ⟧ctx) ]' ξ) [ σ ]')))


--------------------------------------------------
-- Helper for checking + interpreting of the modal eliminator

from-telescope-subst : {Γ : CtxExpr m} (Δ : Telescope m) → ⟦ Γ +tel Δ ⟧ctx ⇒ ⟦ Γ ⟧ctx
from-telescope-subst [] = id-subst _
from-telescope-subst (Δ ,, v ∈ S) = from-telescope-subst Δ ⊚ π

weaken-sem-term : {Γ : CtxExpr m} (Δ : Telescope m) (T : TyExpr m) →
                  Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty → Tm ⟦ Γ +tel Δ ⟧ctx ⟦ T ⟧ty
weaken-sem-term Δ T t = ι⁻¹[ closed-natural {{⟦⟧ty-natural T}} _ ] (t [ from-telescope-subst Δ ]')


--------------------------------------------------
-- The sound type checker

infer-interpret : TmExpr m → (Γ : CtxExpr m) → TCM (InferInterpretResult Γ)
infer-interpret-ext-args : InferInterpretExt margs m → TmExtArgs margs → (Γ : CtxExpr m) →
                           TCM (InferInterpretResult Γ)

infer-interpret (ann t ∈ T) Γ = do
  T' , ⟦t⟧ ← infer-interpret t Γ
  T=T' ← T ≃ᵗʸ? T'
  return (T , ι[ T=T' ] ⟦t⟧)
infer-interpret (var x) Γ = infer-interpret-var x Γ
infer-interpret (lam[ x ∈ T ] b) Γ = do
  S , ⟦b⟧ ← infer-interpret b (Γ , x ∈ T)
  return (T ⇛ S , M.lam ⟦ T ⟧ty (ι[ closed-natural {{⟦⟧ty-natural S}} π ] ⟦b⟧))
infer-interpret (t1 ∙ t2) Γ = do
  T1 , ⟦t1⟧ ← infer-interpret t1 Γ
  func-ty dom cod ← is-func-ty T1
  T2 , ⟦t2⟧ ← infer-interpret t2 Γ
  dom=T2 ← dom ≃ᵗʸ? T2
  return (cod , M.app ⟦t1⟧ (ι[ dom=T2 ] ⟦t2⟧))
infer-interpret (lit n) Γ = return (Nat' , discr n)
infer-interpret suc Γ = return (Nat' ⇛ Nat' , suc')
infer-interpret plus Γ = return (Nat' ⇛ Nat' ⇛ Nat' , nat-sum)
infer-interpret true Γ = return (Bool' , true')
infer-interpret false Γ = return (Bool' , false')
infer-interpret (if c t f) Γ = do
  C , ⟦c⟧ ← infer-interpret c Γ
  Bool'=C ← Bool' ≃ᵗʸ? C
  T , ⟦t⟧ ← infer-interpret t Γ
  F , ⟦f⟧ ← infer-interpret f Γ
  T=F ← T ≃ᵗʸ? F
  return (T , if' (ι[ Bool'=C ] ⟦c⟧) then' ⟦t⟧ else' (ι[ T=F ] ⟦f⟧))
infer-interpret (pair t s) Γ = do
  T , ⟦t⟧ ← infer-interpret t Γ
  S , ⟦s⟧ ← infer-interpret s Γ
  return (T ⊠ S , M.pair $ ⟦t⟧ $ ⟦s⟧)
infer-interpret (fst p) Γ = do
  P , ⟦p⟧ ← infer-interpret p Γ
  prod-ty T S ← is-prod-ty P
  return (T , M.fst $ ⟦p⟧)
infer-interpret (snd p) Γ = do
  P , ⟦p⟧ ← infer-interpret p Γ
  prod-ty T S ← is-prod-ty P
  return (S , M.snd $ ⟦p⟧)
infer-interpret (mod-intro μ t) Γ = do
  T , ⟦t⟧ ← infer-interpret t (Γ ,lock⟨ μ ⟩)
  return (⟨ μ ∣ T ⟩ , M.mod-intro ⟦ μ ⟧modality ⟦t⟧)
infer-interpret (mod-elim {m} {mμ} μ t) Γ = do
  locked-ctx mρ Γ' ρ Δ ← is-locked-ctx Γ
  refl ← mμ ≟mode mρ
  ρ=μ ← ρ ≃ᵐ? μ
  S , ⟦t⟧ ← infer-interpret t Γ'
  modal-ty mκ κ T ← is-modal-ty S
  refl ← m ≟mode mκ
  μ=κ ← μ ≃ᵐ? κ
  return (T , weaken-sem-term Δ T (M.mod-elim ⟦ ρ ⟧modality (ι[ eq-mod-closed (≅ᵐ-trans ρ=μ μ=κ) ⟦ T ⟧ty {{⟦⟧ty-natural T}} ] ⟦t⟧)))
infer-interpret (coe {mμ} μ ρ α t) Γ = do
  T , ⟦t⟧ ← infer-interpret t Γ
  modal-ty mκ κ A ← is-modal-ty T
  refl ← mμ ≟mode mκ
  μ=κ ← μ ≃ᵐ? κ
  return (⟨ ρ ∣ A ⟩ , coe-closed ⟦ α ⟧two-cell {{⟦⟧ty-natural A}} (ι[ eq-mod-closed μ=κ ⟦ A ⟧ty {{⟦⟧ty-natural A}} ] ⟦t⟧))
infer-interpret (ext c args) Γ = infer-interpret-ext-args (infer-interpret-code c) args Γ

infer-interpret-ext-args {[]}        f args Γ = f Γ
infer-interpret-ext-args {m ∷ margs} f args Γ = infer-interpret-ext-args (f (infer-interpret (proj₁ args))) (proj₂ args) Γ


infer-type : TmExpr m → CtxExpr m → TCM (TyExpr m)
infer-type t Γ = InferInterpretResult.type <$> infer-interpret t Γ

⟦_⟧tm-in_ : (t : TmExpr m) (Γ : CtxExpr m) → tcm-elim (λ _ → ⊤) (λ T → Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty) (infer-type t Γ)
⟦ t ⟧tm-in Γ with infer-interpret t Γ
⟦ t ⟧tm-in Γ | type-error _ = tt
⟦ t ⟧tm-in Γ | ok (T , ⟦t⟧) = ⟦t⟧

⟦_⟧tm : (t : TmExpr m) → tcm-elim (λ _ → ⊤) (λ T → Tm ⟦ ◇ {m = m} ⟧ctx ⟦ T ⟧ty) (infer-type t ◇)
⟦ t ⟧tm = ⟦ t ⟧tm-in ◇
