--------------------------------------------------
-- Definition of a typechecker for the deeply embedded language
--   and interpretation of well-typed terms in a presheaf model
--------------------------------------------------

module Applications.GuardedRecursion.MSTT.SoundTypeChecker where

open import Data.Bool
open import Data.Nat
open import Data.String renaming (_==_ to _=string=_)
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure as M hiding (◇; _,,_)
open import Model.Modality as M hiding (𝟙; _ⓜ_; ⟨_∣_⟩; _,lock⟨_⟩; mod-intro; mod-elim; coe)
open import Model.Type.Discrete as M hiding (Nat'; Bool')
open import Model.Type.Function as M hiding (_⇛_; lam; app)
open import Model.Type.Product as M hiding (_⊠_; pair; fst; snd)
open import Applications.GuardedRecursion.Model.Modalities as M hiding (constantly; later; ▻; löb)
open import Applications.GuardedRecursion.Model.Streams.Guarded as M hiding (GStream; g-cons; g-head; g-tail)

open import Applications.GuardedRecursion.MSTT.ModeTheory
open import Applications.GuardedRecursion.MSTT.Syntax
open import Applications.GuardedRecursion.MSTT.TCMonad
open import Applications.GuardedRecursion.MSTT.Equality
open import Applications.GuardedRecursion.MSTT.InterpretTypes

private
  variable
    m : ModeExpr


-- The sound typechecker defined below accepts a term and a context and will,
--   if successful, produce the type of that term and an interpretation of that
--   term in a presheaf model.
infix 1 _,_
record InferInterpretResult (Γ : CtxExpr m) : Set where
  constructor _,_
  field
    type : TyExpr m
    interpretation : Tm ⟦ Γ ⟧ctx ⟦ type ⟧ty

weaken-sem-term : {Γ : CtxExpr m} (Δ : Telescope m) (T : TyExpr m) →
                  Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty → Tm ⟦ Γ +tel Δ ⟧ctx ⟦ T ⟧ty
weaken-sem-term []           T t = t
weaken-sem-term (Δ ,, v ∈ S) T t =
  let weakened-t = weaken-sem-term Δ T t
  in ι⁻¹[ closed-natural {{⟦⟧ty-natural T}} π ] (weakened-t [ π ]')

infer-interpret-var : String → (Γ : CtxExpr m) → TCM (InferInterpretResult Γ)
infer-interpret-var x ◇ = type-error ("The variable "++ x ++ " does not exist in this context.")
infer-interpret-var x (Γ , y ∈ T) with x =string= y
infer-interpret-var x (Γ , y ∈ T) | true = return (T , (ι⁻¹[ closed-natural {{⟦⟧ty-natural T}} π ] ξ))
infer-interpret-var x (Γ , y ∈ T) | false = do
  S , ⟦x⟧ ← infer-interpret-var x Γ
  return (S , ι⁻¹[ closed-natural {{⟦⟧ty-natural S}} π ] (⟦x⟧ [ π ]'))
infer-interpret-var x (Γ ,lock⟨ 𝟙 ⟩) = do
  T , ⟦x⟧ ← infer-interpret-var x Γ
  return (T , ⟦x⟧)
infer-interpret-var x (Γ ,lock⟨ μ ⟩) = type-error ("Impossible to directly use the variable "
                                                  ++ x
                                                  ++ " from the locked context "
                                                  ++ show-ctx (Γ ,lock⟨ μ ⟩) ++ ".")

infer-interpret : TmExpr m → (Γ : CtxExpr m) → TCM (InferInterpretResult Γ)
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
infer-interpret (constantly-if c t f) Γ = do
  C , ⟦c⟧ ← infer-interpret c Γ
  modal-ty m μ B ← is-modal-ty C
  refl ← m ≟mode ★
  constantly=μ ← constantly ≃ᵐ? μ
  Bool'=B ← Bool' ≃ᵗʸ? B
  T , ⟦t⟧ ← infer-interpret t Γ
  F , ⟦f⟧ ← infer-interpret f Γ
  T=F ← T ≃ᵗʸ? F
  return (T , constantly-if' (ι[ ≅ᵗʸ-trans (constantly-ty-cong Bool'=B) (eq-mod-closed constantly=μ ⟦ B ⟧ty {{⟦⟧ty-natural B}}) ] ⟦c⟧)
              then' ⟦t⟧ else' (ι[ T=F ] ⟦f⟧))
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
infer-interpret (löb[ x ∈▻ T ] t) Γ = do
  S , ⟦t⟧ ← infer-interpret t (Γ , x ∈ ▻ T)
  T=S ← T ≃ᵗʸ? S
  return (T , löb' ⟦ T ⟧ty (ι[ ≅ᵗʸ-trans (closed-natural {{⟦⟧ty-natural T}} π) T=S ]
                           (ι⁻¹[ closed-natural {{⟦⟧ty-natural S}} _ ]
                           (ιc[ ,,-cong (▻-cong (closed-natural {{⟦⟧ty-natural T}} (from-earlier _))) ]' ⟦t⟧))))
infer-interpret (g-cons T) Γ = return (⟨ constantly ∣ T ⟩ ⇛ ▻ (GStream T) ⇛ GStream T
                                      , ι⁻¹[ ⇛-cong ≅ᵗʸ-refl (⇛-cong (▻-cong (closed-natural {{⟦⟧ty-natural (GStream T)}} _)) ≅ᵗʸ-refl) ] M.g-cons)
infer-interpret (g-head T) Γ = return (GStream T ⇛ ⟨ constantly ∣ T ⟩ , M.g-head)
infer-interpret (g-tail T) Γ = return (GStream T ⇛ ▻ (GStream T)
                                      , ι⁻¹[ ⇛-cong ≅ᵗʸ-refl (▻-cong (closed-natural {{⟦⟧ty-natural (GStream T)}} _)) ] M.g-tail)

infer-type : TmExpr m → CtxExpr m → TCM (TyExpr m)
infer-type t Γ = InferInterpretResult.type <$> infer-interpret t Γ

⟦_⟧tm-in_ : (t : TmExpr m) (Γ : CtxExpr m) → tcm-elim (λ _ → ⊤) (λ T → Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty) (infer-type t Γ)
⟦ t ⟧tm-in Γ with infer-interpret t Γ
⟦ t ⟧tm-in Γ | type-error _ = tt
⟦ t ⟧tm-in Γ | ok (T , ⟦t⟧) = ⟦t⟧

⟦_⟧tm : (t : TmExpr m) → tcm-elim (λ _ → ⊤) (λ T → Tm ⟦ ◇ {m = m} ⟧ctx ⟦ T ⟧ty) (infer-type t ◇)
⟦ t ⟧tm = ⟦ t ⟧tm-in ◇
