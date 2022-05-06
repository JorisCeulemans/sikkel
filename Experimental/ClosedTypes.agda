--------------------------------------------------
-- Alternative approach for closed types
--------------------------------------------------

module Experimental.ClosedTypes where

open import Data.Product renaming (_,_ to [_,_])
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.BaseCategory
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.Type
open import Model.CwF-Structure.Term
open import Model.CwF-Structure.ContextExtension
open import Model.Type.Function
open import Model.Type.Product

private variable
  C : BaseCategory
  Γ Δ Θ : Ctx C


--------------------------------------------------
-- Definition of a closed type and structural constructions such as substitution

ClosedTy : BaseCategory → Set₁
ClosedTy C = Ty {C = C} ◇

closed-ty-natural : {Δ Γ : Ctx C} (T : ClosedTy C) (σ : Δ ⇒ Γ) → ((T [ !◇ Γ ]) [ σ ]) ≅ᵗʸ (T [ !◇ Δ ])
closed-ty-natural T σ = ≅ᵗʸ-trans (ty-subst-comp T _ σ) (ty-subst-cong-subst (◇-terminal _ _ _) T)

private variable
  T S : ClosedTy C

-- Corresponding notion of a term of a closed type
SimpleTm : Ctx C → ClosedTy C → Set
SimpleTm Γ T = Tm Γ (T [ !◇ Γ ])

_[_]s : SimpleTm Γ T → (Δ ⇒ Γ) → SimpleTm Δ T
_[_]s {T = T} t σ = ι⁻¹[ closed-ty-natural T σ ] (t [ σ ]')

stm-subst-id : (t : SimpleTm Γ T) → (t [ id-subst Γ ]s) ≅ᵗᵐ t
eq (stm-subst-id {T = T} t) γ = ty-id T

stm-subst-comp : (t : SimpleTm Δ T) (σ : Γ ⇒ Δ) (τ : Θ ⇒ Γ) → ((t [ σ ]s) [ τ ]s) ≅ᵗᵐ (t [ σ ⊚ τ ]s)
eq (stm-subst-comp {T = T} t σ τ) θ = ty-id T

-- Extending a context with a closed type
infixl 15 _,,ₛ_
_,,ₛ_ : Ctx C → ClosedTy C → Ctx C
Γ ,,ₛ T = Γ ,, (T [ !◇ Γ ])

sξ : SimpleTm (Γ ,,ₛ T) T
sξ ⟨ x , [ γ , t ] ⟩' = t
naturality sξ f refl = refl

_,ₛ_ : (Δ ⇒ Γ) → SimpleTm Δ T → (Δ ⇒ Γ ,,ₛ T)
σ ,ₛ t = to-ext-subst _ σ (ι[ closed-ty-natural _ σ ] t)

,ₛ-β1 : (σ : Δ ⇒ Γ) (t : SimpleTm Δ T) → π ⊚ (σ ,ₛ t) ≅ˢ σ
,ₛ-β1 σ t = ctx-ext-subst-proj₁ σ _

,ₛ-β2 : (σ : Δ ⇒ Γ) (t : SimpleTm Δ T) → (sξ [ σ ,ₛ t ]s) ≅ᵗᵐ t
eq (,ₛ-β2 {T = T} σ t) δ = trans (ty-id T) (ty-id T)

,ₛ-η : (σ : Δ ⇒ Γ ,,ₛ T) → σ ≅ˢ ((π ⊚ σ) ,ₛ (sξ [ σ ]s))
eq (,ₛ-η {T = T} σ) δ = cong [ _ ,_] (sym (trans (ty-id T) (ty-id T)))

_s⊹ : (σ : Δ ⇒ Γ) → (Δ ,,ₛ T ⇒ Γ ,,ₛ T)
σ s⊹ = (σ ⊚ π) ,ₛ sξ


--------------------------------------------------
-- Simple functions with closed types as (co)domain

sλ[_]_ : (T : ClosedTy C) → SimpleTm (Γ ,,ₛ T) S → SimpleTm Γ (T ⇛ S)
sλ[ T ] b = ι[ ⇛-natural (!◇ _) ] (lam _ (ι[ closed-ty-natural _ π ] b))

_∙ₛ_ : SimpleTm Γ (T ⇛ S) → SimpleTm Γ T → SimpleTm Γ S
f ∙ₛ t = app (ι⁻¹[ ⇛-natural _ ] f) t

sfun-β : {T S : ClosedTy C} (b : SimpleTm (Γ ,,ₛ T) S) (t : SimpleTm Γ T) → (sλ[ T ] b) ∙ₛ t ≅ᵗᵐ (b [ id-subst Γ ,ₛ t ]s)
eq (sfun-β {C = C} {Γ = Γ} {T = T} {S = S} b t) γ =
  trans (ty-cong-2-1 S (BaseCategory.hom-idˡ C)) (trans (naturality b _ proof) (sym (ty-id S)))
  where
    proof = to-Σ-ty-eq T (trans (ctx-id Γ) (ctx-id Γ))
                         (trans (strong-ty-id T) (cong (T ⟪ _ , refl ⟫_) (strong-ty-id T)))

sfun-η : {T S : ClosedTy C} (f : SimpleTm Γ (T ⇛ S)) → f ≅ᵗᵐ (sλ[ T ] ((f [ π ]s) ∙ₛ sξ))
eq (sfun-η {C = C} {Γ = Γ} {T = T} {S = S} f) γ = to-pshfun-eq λ { ρ refl t →
  let proof = _
  -- Agda cannot infer the argument if we replace `proof` below with _
  -- because that metavariable would be created in a bigger context
  -- (it appears in the body of a function as argument to `cong`).
  in
  sym (trans (ty-id S)
             (trans (ty-id S)
                    (trans (cong (f ⟨ _ , _ ⟩' $⟨ _ , proof ⟩_) (ty-id T))
                           (sym (trans ($-cong (f ⟨ _ , γ ⟩') (sym (BaseCategory.hom-idʳ C)))
                                       (trans (cong (_$⟨ BaseCategory.hom-id C , refl ⟩ t) (naturality f ρ refl))
                                              ($-cong (f ⟨ _ , _ ⟩') (sym (BaseCategory.hom-idˡ C))))))))) }


--------------------------------------------------
-- (Non-dependent) products of closed types

spair : SimpleTm Γ T → SimpleTm Γ S → SimpleTm Γ (T ⊠ S)
spair t s = ι[ ⊠-natural _ ] prim-pair t s

sfst : SimpleTm Γ (T ⊠ S) → SimpleTm Γ T
sfst p = prim-fst (ι⁻¹[ ⊠-natural _ ] p)

ssnd : SimpleTm Γ (T ⊠ S) → SimpleTm Γ S
ssnd p = prim-snd (ι⁻¹[ ⊠-natural _ ] p)

sprod-β-fst : (t : SimpleTm Γ T) (s : SimpleTm Γ S) → sfst (spair t s) ≅ᵗᵐ t
sprod-β-fst t s = record { eq = λ _ → refl }

sprod-β-snd : (t : SimpleTm Γ T) (s : SimpleTm Γ S) → ssnd (spair t s) ≅ᵗᵐ s
sprod-β-snd t s = record { eq = λ _ → refl }

sprod-η : (p : SimpleTm Γ (T ⊠ S)) → p ≅ᵗᵐ spair (sfst p) (ssnd p)
sprod-η p = record { eq = λ _ → refl }
