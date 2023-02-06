--------------------------------------------------
-- Alternative approach for closed types
--------------------------------------------------

module Experimental.ClosedTypes where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
open import Function.Nary.NonDependent using (congₙ)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.BaseCategory
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.ContextEquivalence
open import Model.CwF-Structure.Type
open import Model.CwF-Structure.Term
open import Model.CwF-Structure.ContextExtension
open import Model.Type.Constant
open import Model.Type.Function
open import Model.Type.Product

open import Experimental.ClosedTypes.Helpers

private variable
  C : BaseCategory
  Γ Δ Θ : Ctx C


--------------------------------------------------
-- Definition of a closed type and structural constructions such as substitution

ClosedTy : BaseCategory → Set₁
ClosedTy C = Ty {C = C} ◇

closed-ty-natural : {Δ Γ : Ctx C} (T : ClosedTy C) (σ : Δ ⇒ Γ) → ((T [ !◇ Γ ]) [ σ ]) ≅ᵗʸ (T [ !◇ Δ ])
closed-ty-natural T σ = transᵗʸ (ty-subst-comp T _ σ) (ty-subst-cong-subst (◇-terminal _ _ _) T)

private variable
  T S : ClosedTy C

-- Corresponding notion of a term of a closed type
SimpleTm : Ctx C → ClosedTy C → Set
SimpleTm Γ T = Tm Γ (T [ !◇ Γ ])

sι[_]_ : T ≅ᵗʸ S → SimpleTm Γ S → SimpleTm Γ T
sι[ e ] s = ι[ ty-subst-cong-ty _ e ] s

sι⁻¹[_]_ : T ≅ᵗʸ S → SimpleTm Γ T → SimpleTm Γ S
sι⁻¹[ e ] t = ι⁻¹[ ty-subst-cong-ty _ e ] t

_[_]s : SimpleTm Γ T → (Δ ⇒ Γ) → SimpleTm Δ T
_[_]s {T = T} t σ = ι⁻¹[ closed-ty-natural T σ ] (t [ σ ]')

stm-subst-id : (t : SimpleTm Γ T) → (t [ id-subst Γ ]s) ≅ᵗᵐ t
eq (stm-subst-id {T = T} t) γ = ty-id T

stm-subst-comp : (t : SimpleTm Δ T) (σ : Γ ⇒ Δ) (τ : Θ ⇒ Γ) → ((t [ σ ]s) [ τ ]s) ≅ᵗᵐ (t [ σ ⊚ τ ]s)
eq (stm-subst-comp {T = T} t σ τ) θ = ty-id T

stm-subst-cong-subst : (t : SimpleTm Δ T) {σ τ : Γ ⇒ Δ} → σ ≅ˢ τ → t [ σ ]s ≅ᵗᵐ t [ τ ]s
eq (stm-subst-cong-subst {T = T} t e) γ = cong (λ δ → T ⟪ _ , refl ⟫ t ⟨ _ , δ ⟩') (eq e γ)

stm-subst-cong-tm : {t s : SimpleTm Δ T} → t ≅ᵗᵐ s → (σ : Γ ⇒ Δ) → t [ σ ]s ≅ᵗᵐ s [ σ ]s
eq (stm-subst-cong-tm {T = T} e σ) γ = cong (T ⟪ _ , refl ⟫_) (eq e (func σ γ))

-- Extending a context with a closed type
infixl 15 _,,ₛ_
_,,ₛ_ : Ctx C → ClosedTy C → Ctx C
Γ ,,ₛ T = Γ ,, (T [ !◇ Γ ])

,,ₛ-cong : {Γ : Ctx C} → T ≅ᵗʸ S → Γ ,,ₛ T ≅ᶜ Γ ,,ₛ S
,,ₛ-cong T=S = ,,-cong (ty-subst-cong-ty _ T=S)

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

,ₛ-cong1 : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → (t : SimpleTm Δ T) → σ ,ₛ t ≅ˢ τ ,ₛ t
eq (,ₛ-cong1 {T = T} e t) δ = cong [_, T ⟪ _ , refl ⟫ t ⟨ _ , δ ⟩' ] (eq e δ)

,ₛ-cong2 : (σ : Δ ⇒ Γ) {t s : SimpleTm Δ T} → t ≅ᵗᵐ s → σ ,ₛ t ≅ˢ σ ,ₛ s
eq (,ₛ-cong2 {T = T} σ e) δ = cong (λ x → [ func σ δ , T ⟪ _ , refl ⟫ x ]) (eq e δ)

,ₛ-η-id : id-subst (Γ ,,ₛ T) ≅ˢ (π ,ₛ sξ)
,ₛ-η-id {Γ = Γ} {T = T} = transˢ (,ₛ-η (id-subst (Γ ,,ₛ T))) (transˢ (,ₛ-cong1 (⊚-id-substʳ _) _) (,ₛ-cong2 _ (stm-subst-id sξ)))

-- The following is also provable from the η and β laws for _,ₛ_.
,ₛ-⊚ : (σ : Δ ⇒ Γ) (t : SimpleTm Δ T) (τ : Θ ⇒ Δ) → ((σ ,ₛ t) ⊚ τ) ≅ˢ ((σ ⊚ τ) ,ₛ (t [ τ ]s))
eq (,ₛ-⊚ {T = T} σ t τ) θ = cong [ _ ,_] (sym (ty-id T))

_s⊹ : (σ : Δ ⇒ Γ) → (Δ ,,ₛ T ⇒ Γ ,,ₛ T)
σ s⊹ = (σ ⊚ π) ,ₛ sξ


--------------------------------------------------
-- Simple functions with closed types as (co)domain

sλ[_]_ : (T : ClosedTy C) → SimpleTm (Γ ,,ₛ T) S → SimpleTm Γ (T ⇛ S)
sλ[ T ] b = ι[ ⇛-natural (!◇ _) ] (lam _ (ι[ closed-ty-natural _ π ] b))

_∙ₛ_ : SimpleTm Γ (T ⇛ S) → SimpleTm Γ T → SimpleTm Γ S
f ∙ₛ t = app (ι⁻¹[ ⇛-natural _ ] f) t

sλ-natural : {b : SimpleTm (Γ ,,ₛ T) S} (σ : Δ ⇒ Γ) → (sλ[ T ] b) [ σ ]s ≅ᵗᵐ (sλ[ T ] (b [ σ s⊹ ]s))
eq (sλ-natural {C} {Γ = Γ} {T = T} {S = S} {b = b} σ) δ = to-pshfun-eq (λ _ _ _ →
  let proof1 = trans (ctx-id Γ) (trans (cong (λ - → Γ ⟪ - ⟫ _) hom-idˡ) (naturality σ))
      proof2 = trans (strong-ty-id T) (cong (T ⟪ hom-id , refl ⟫_) (ty-cong T refl))
  in
  trans (ty-cong-2-1 S hom-idʳ)
        (trans (naturality b hom-id (to-Σ-ty-eq T proof1 proof2))
               (sym (trans (strong-ty-id S)
                           (trans (ty-id S) (ty-id S))))))
  where open BaseCategory C

sλ-cong : {b1 b2 : SimpleTm (Γ ,,ₛ T) S} → b1 ≅ᵗᵐ b2 → (sλ[ T ] b1) ≅ᵗᵐ (sλ[ T ] b2)
sλ-cong e = ι-cong (lam-cong _ (ι-cong e))

∙ₛ-natural : {f : SimpleTm Γ (T ⇛ S)} {t : SimpleTm Γ T} (σ : Δ ⇒ Γ) → (f ∙ₛ t) [ σ ]s ≅ᵗᵐ (f [ σ ]s) ∙ₛ (t [ σ ]s)
eq (∙ₛ-natural {f = f} σ) δ = trans (sym (naturality (f ⟨ _ , _ ⟩'))) ($-cong (f ⟨ _ , _ ⟩') refl)

∙ₛ-cong : {f1 f2 : SimpleTm Γ (T ⇛ S)} {t1 t2 : SimpleTm Γ T} →
          f1 ≅ᵗᵐ f2 → t1 ≅ᵗᵐ t2 → (f1 ∙ₛ t1) ≅ᵗᵐ (f2 ∙ₛ t2)
∙ₛ-cong ef et = app-cong (ι⁻¹-cong ef) et

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
-- All embedded agda types are closed

sconst : {A : Set} → A → SimpleTm Γ (Const A)
sconst a = (const a) [ !◇ _ ]'

sconst-func : {A B : Set} → (A → B) → SimpleTm Γ (Const A ⇛ Const B)
sconst-func f = (const-func f) [ !◇ _ ]'

sconst-func₂ : {A B C : Set} → (A → B → C) → SimpleTm Γ (Const A ⇛ Const B ⇛ Const C)
sconst-func₂ f = (const-func₂ f) [ !◇ _ ]'

sconst-natural : {A : Set} {a : A} (σ : Δ ⇒ Γ) → (sconst a) [ σ ]s ≅ᵗᵐ sconst a
eq (sconst-natural σ) _ = refl

sconst-func-natural : {A B : Set} {f : A → B} (σ : Δ ⇒ Γ) → (sconst-func f) [ σ ]s ≅ᵗᵐ sconst-func f
eq (sconst-func-natural σ) _ = to-pshfun-eq (λ _ _ _ → refl)

sconst-func₂-natural : {A B C : Set} {f : A → B → C} (σ : Δ ⇒ Γ) →
                       (sconst-func₂ f) [ σ ]s ≅ᵗᵐ sconst-func₂ f
eq (sconst-func₂-natural σ) _ = to-pshfun-eq (λ _ _ _ → to-pshfun-eq (λ _ _ _ → refl))

strue sfalse : SimpleTm Γ Bool'
strue = sconst true
sfalse = sconst false

sif : SimpleTm Γ Bool' → SimpleTm Γ T → SimpleTm Γ T → SimpleTm Γ T
sif b t f = if' (ι⁻¹[ Const-natural _ _ ] b) then' t else' f

sif-natural : {b : SimpleTm Γ Bool'} {t f : SimpleTm Γ T} (σ : Δ ⇒ Γ) →
              (sif b t f) [ σ ]s ≅ᵗᵐ sif (b [ σ ]s) (t [ σ ]s) (f [ σ ]s)
eq (sif-natural {T = T} σ) δ = trans (ty-id T) (sym (cong₂ (λ x y → if _ then x else y) (ty-id T) (ty-id T)))

sif-cong : {b1 b2 : SimpleTm Γ Bool'} {t1 t2 f1 f2 : SimpleTm Γ T} →
           b1 ≅ᵗᵐ b2 → t1 ≅ᵗᵐ t2 → f1 ≅ᵗᵐ f2 →
           sif b1 t1 f1 ≅ᵗᵐ sif b2 t2 f2
eq (sif-cong eb et ef) γ = congₙ 3 if_then_else_ (eq eb γ) (eq et γ) (eq ef γ)

sif-β-true : (t f : SimpleTm Γ T) → sif (sconst true) t f ≅ᵗᵐ t
sif-β-true t f = record { eq = λ _ → refl }

sif-β-false : (t f : SimpleTm Γ T) → sif (sconst false) t f ≅ᵗᵐ f
sif-β-false t f = record { eq = λ _ → refl }

sbool-induction : (T : Ty (Γ ,,ₛ Bool')) →
                  Tm Γ (T [ id-subst Γ ,ₛ strue ]) → Tm Γ (T [ id-subst Γ ,ₛ sfalse ]) →
                  Tm (Γ ,,ₛ Bool') T
sbool-induction T t f ⟨ x , [ γ , false ] ⟩' = f ⟨ x , γ ⟩'
sbool-induction T t f ⟨ x , [ γ , true  ] ⟩' = t ⟨ x , γ ⟩'
naturality (sbool-induction T t f) {γy = [ _ , false ]} {γx = [ _ , false ]} ρ refl = naturality f ρ refl
naturality (sbool-induction T t f) {γy = [ _ , true  ]} {γx = [ _ , true  ]} ρ refl = naturality t ρ refl

szero : SimpleTm Γ Nat'
szero = sconst 0

ssuc : SimpleTm Γ (Nat' ⇛ Nat')
ssuc = sconst-func suc

ssuc-sconst : {n : ℕ} → ssuc {Γ = Γ} ∙ₛ (sconst n) ≅ᵗᵐ sconst (suc n)
eq ssuc-sconst _ = refl

-- This can also be implemented in terms of prim-nat-elim. However,
-- now it is easier to prove prim-snat-elim-natural and prim-snat-elim-cong.
prim-snat-elim : {A : ClosedTy C} → SimpleTm Γ A → SimpleTm (Γ ,,ₛ A) A → SimpleTm (Γ ,,ₛ Nat') A
prim-snat-elim a f ⟨ x , [ γ , zero  ] ⟩' = a ⟨ x , γ ⟩'
prim-snat-elim a f ⟨ x , [ γ , suc n ] ⟩' = f ⟨ x , [ γ , prim-snat-elim a f ⟨ x , [ γ , n ] ⟩' ] ⟩'
naturality (prim-snat-elim a f) {γy = [ _ , zero ]} {γx = [ _ , zero ]} ρ refl = naturality a ρ refl
naturality (prim-snat-elim {A = A} a f) {γy = [ _ , suc n ]} {γx = [ _ , suc n ]} ρ refl =
  trans (ty-cong A refl) (naturality f ρ (cong [ _ ,_] (naturality (prim-snat-elim a f) {γy = [ _ , n ]} ρ refl)))

snat-elim : {A : ClosedTy C} → SimpleTm Γ A → SimpleTm Γ (A ⇛ A) → SimpleTm Γ (Nat' ⇛ A)
snat-elim a f = sλ[ Nat' ] prim-snat-elim a ((f [ π ]s) ∙ₛ sξ)

prim-snat-elim-natural : {A : ClosedTy C} {a : SimpleTm Γ A} {f : SimpleTm (Γ ,,ₛ A) A}
                         (σ : Δ ⇒ Γ) →
                         (prim-snat-elim a f) [ σ s⊹ ]s ≅ᵗᵐ prim-snat-elim (a [ σ ]s) (f [ σ s⊹ ]s)
eq (prim-snat-elim-natural         σ) [ δ , zero  ] = refl
eq (prim-snat-elim-natural {A = A} {f = f} σ) [ δ , suc n ] =
  cong (λ - → A ⟪ _ , _ ⟫ f ⟨ _ , [ _ , - ] ⟩') (trans (sym (ty-id A)) (trans (eq (prim-snat-elim-natural {f = f} σ) [ δ , n ]) (sym (ty-id A))))

prim-snat-elim-cong : {A : ClosedTy C} {a1 a2 : SimpleTm Γ A} {f1 f2 : SimpleTm (Γ ,,ₛ A) A} →
                      a1 ≅ᵗᵐ a2 → f1 ≅ᵗᵐ f2 → prim-snat-elim a1 f1 ≅ᵗᵐ prim-snat-elim a2 f2
eq (prim-snat-elim-cong ea ef) [ γ , zero ] = eq ea γ
eq (prim-snat-elim-cong {f2 = f2} ea ef) [ γ , suc n ] = trans (eq ef _) (cong (λ x → f2 ⟨ _ , [ γ , x ] ⟩') (eq (prim-snat-elim-cong ea ef) [ γ , n ]))

snat-elim-natural : {A : ClosedTy C} {a : SimpleTm Γ A} {f : SimpleTm Γ (A ⇛ A)} (σ : Δ ⇒ Γ) →
                    (snat-elim a f) [ σ ]s ≅ᵗᵐ snat-elim (a [ σ ]s) (f [ σ ]s)
snat-elim-natural {f = f} σ =
  transᵗᵐ (sλ-natural σ)
          (sλ-cong (transᵗᵐ (prim-snat-elim-natural σ)
                            (prim-snat-elim-cong reflᵗᵐ (transᵗᵐ (∙ₛ-natural (σ s⊹))
                                                                 (∙ₛ-cong ⊹-lemma (,ₛ-β2 _ _))))))
  where
    ⊹-lemma : (f [ π ]s) [ σ s⊹ ]s ≅ᵗᵐ (f [ σ ]s) [ π ]s
    ⊹-lemma = transᵗᵐ (stm-subst-comp _ _ _) (transᵗᵐ (stm-subst-cong-subst _ (,ₛ-β1 _ _)) (symᵗᵐ (stm-subst-comp _ _ _)))

snat-elim-cong : {A : ClosedTy C} {a1 a2 : SimpleTm Γ A} {f1 f2 : SimpleTm Γ (A ⇛ A)} →
                 a1 ≅ᵗᵐ a2 → f1 ≅ᵗᵐ f2 → snat-elim a1 f1 ≅ᵗᵐ snat-elim a2 f2
snat-elim-cong ea ef = sλ-cong (prim-snat-elim-cong ea (∙ₛ-cong (stm-subst-cong-tm ef π) reflᵗᵐ))

snat-β-zero : {A : ClosedTy C} (a : SimpleTm Γ A) (f : SimpleTm Γ (A ⇛ A)) → snat-elim a f ∙ₛ szero ≅ᵗᵐ a
eq (snat-β-zero {Γ = Γ} {A = A} a f) γ =
  trans (strong-ty-id A) (trans (ty-cong A refl) (naturality a _ (trans (ctx-id Γ) (ctx-id Γ))))

snat-β-suc : {A : ClosedTy C} (a : SimpleTm Γ A) (f : SimpleTm Γ (A ⇛ A)) (n : SimpleTm Γ Nat') →
             snat-elim a f ∙ₛ (ssuc ∙ₛ n) ≅ᵗᵐ (f ∙ₛ (snat-elim a f ∙ₛ n))
eq (snat-β-suc {C = C} {Γ = Γ} {A = A} a f n) {x} γ =
  trans (cong (A ⟪ hom-id , _ ⟫_) (sym (naturality (f ⟨ x , Γ ⟪ hom-id ⟫ γ ⟩'))))
        (trans (sym (naturality (f ⟨ x , Γ ⟪ hom-id ⟫ γ ⟩')))
               (trans ($-cong (f ⟨ x , Γ ⟪ hom-id ⟫ γ ⟩') (trans hom-idʳ hom-idʳ))
                      (cong (_$⟨ hom-id , _ ⟩ t) (naturality f {x} {x} {Γ ⟪ hom-id ⟫ γ} {γ} hom-id (trans (ctx-id Γ) (ctx-id Γ))))))
  where
    open BaseCategory C
    t = _

snat-induction : (T : Ty (Γ ,,ₛ Nat')) →
                 Tm Γ (T [ id-subst Γ ,ₛ szero ]) → Tm (Γ ,,ₛ Nat' ,, T) (T [ (π ,ₛ (ssuc ∙ₛ sξ)) ⊚ π ]) →
                 Tm (Γ ,,ₛ Nat') T
snat-induction T z s ⟨ x , [ γ , zero  ] ⟩' = z ⟨ x , γ ⟩'
snat-induction T z s ⟨ x , [ γ , suc n ] ⟩' = s ⟨ x , [ [ γ , n ] , snat-induction T z s ⟨ x , [ γ , n ] ⟩' ] ⟩'
naturality (snat-induction T z s) {γy = [ _ , zero  ]} {γx = [ _ , zero  ]} ρ refl = naturality z ρ refl
naturality (snat-induction T z s) {γy = [ _ , suc n ]} {γx = [ _ , suc m ]} ρ refl =
  trans (ty-cong T refl) (naturality s ρ (cong [ _ ,_] (naturality (snat-induction T z s) ρ refl)))


--------------------------------------------------
-- (Non-dependent) products of closed types

spair : SimpleTm Γ T → SimpleTm Γ S → SimpleTm Γ (T ⊠ S)
spair t s = ι[ ⊠-natural _ ] pair t s

sfst : SimpleTm Γ (T ⊠ S) → SimpleTm Γ T
sfst p = fst (ι⁻¹[ ⊠-natural _ ] p)

ssnd : SimpleTm Γ (T ⊠ S) → SimpleTm Γ S
ssnd p = snd (ι⁻¹[ ⊠-natural _ ] p)

spair-natural : {t : SimpleTm Γ T} {s : SimpleTm Γ S} (σ : Δ ⇒ Γ) →
                (spair t s) [ σ ]s ≅ᵗᵐ spair (t [ σ ]s) (s [ σ ]s)
eq (spair-natural σ) _ = refl

spair-cong : {t1 t2 : SimpleTm Γ T} {s1 s2 : SimpleTm Γ S} →
             t1 ≅ᵗᵐ t2 → s1 ≅ᵗᵐ s2 → spair t1 s1 ≅ᵗᵐ spair t2 s2
spair-cong et es = ι-cong (pair-cong et es)

sfst-natural : {p : SimpleTm Γ (T ⊠ S)} (σ : Δ ⇒ Γ) → (sfst p) [ σ ]s ≅ᵗᵐ sfst (p [ σ ]s)
eq (sfst-natural σ) _ = refl

sfst-cong : {p1 p2 : SimpleTm Γ (T ⊠ S)} → p1 ≅ᵗᵐ p2 → sfst p1 ≅ᵗᵐ sfst p2
sfst-cong ep = fst-cong (ι⁻¹-cong ep)

ssnd-natural : {p : SimpleTm Γ (T ⊠ S)} (σ : Δ ⇒ Γ) → (ssnd p) [ σ ]s ≅ᵗᵐ ssnd (p [ σ ]s)
eq (ssnd-natural σ) _ = refl

ssnd-cong : {p1 p2 : SimpleTm Γ (T ⊠ S)} → p1 ≅ᵗᵐ p2 → ssnd p1 ≅ᵗᵐ ssnd p2
ssnd-cong ep = snd-cong (ι⁻¹-cong ep)

sprod-β-fst : (t : SimpleTm Γ T) (s : SimpleTm Γ S) → sfst (spair t s) ≅ᵗᵐ t
sprod-β-fst t s = record { eq = λ _ → refl }

sprod-β-snd : (t : SimpleTm Γ T) (s : SimpleTm Γ S) → ssnd (spair t s) ≅ᵗᵐ s
sprod-β-snd t s = record { eq = λ _ → refl }

sprod-η : (p : SimpleTm Γ (T ⊠ S)) → p ≅ᵗᵐ spair (sfst p) (ssnd p)
sprod-η p = record { eq = λ _ → refl }
