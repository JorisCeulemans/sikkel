--------------------------------------------------
-- Lob induction and its properties
--------------------------------------------------

module Applications.GuardedRecursion.Model.Lob where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Unit
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Type.Function
open import Model.DRA
open import Applications.GuardedRecursion.Model.Modalities.Later

private
  variable
    m n : ℕ
    Γ Δ Θ : Ctx ω


--------------------------------------------------
-- Definition of Löb induction and proofs of some of its properties

löb : (T : Ty Γ) → Tm Γ (▻' T ⇛ T) → Tm Γ T
löb {Γ = Γ} T f = MkTm tm nat
  where
    tm : (n : ℕ) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
    tm zero    γ = f €⟨ zero , γ ⟩ tt
    tm (suc n) γ = f €⟨ suc n , γ ⟩ tm n (Γ ⟪ n≤1+n n ⟫ γ)

    open ≡-Reasoning
    nat : ∀ {m n} {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} (m≤n : m ≤ n) (eγ : Γ ⟪ m≤n ⟫ γn ≡ γm) →
          T ⟪ m≤n , eγ ⟫ tm n γn ≡ tm m γm
    nat {m = .zero} {n = zero}  z≤n _ = €-natural f
    nat {m = .zero} {n = suc n} z≤n _ = €-natural f
    nat {m = suc m} {n = suc n} {γ} {γ'} (s≤s m≤n) eγ =
      begin
        T ⟪ s≤s m≤n , eγ ⟫ f €⟨ suc n , γ ⟩ (tm n (Γ ⟪ n≤1+n n ⟫ γ))
      ≡⟨ €-natural f ⟩
        f €⟨ suc m , γ' ⟩ (T ⟪ m≤n , _ ⟫ (tm n (Γ ⟪ n≤1+n n ⟫ γ)))
      ≡⟨ cong (f €⟨ _ , _ ⟩_) (nat m≤n _) ⟩
        f €⟨ suc m , γ' ⟩ (tm m (Γ ⟪ n≤1+n m ⟫ γ')) ∎

löb' : (T : Ty Γ) → Tm (Γ ,, ▻' T) (T [ π ]) → Tm Γ T
löb' T f = löb T (lam (▻' T) f)

löb-is-fixpoint : {T : Ty Γ} (f : Tm Γ (▻' T ⇛ T)) →
                  app f (next' (löb T f)) ≅ᵗᵐ löb T f
eq (löb-is-fixpoint f) {zero}  γ = refl
eq (löb-is-fixpoint f) {suc n} γ = refl

fixpoint-unique : {T : Ty Γ} (f  : Tm Γ (▻' T ⇛ T)) (t s : Tm Γ T) →
                  app f (next' t) ≅ᵗᵐ t → app f (next' s) ≅ᵗᵐ s → t ≅ᵗᵐ s
eq (fixpoint-unique f t s t-fix s-fix) {x = zero}  γ =
  begin
    t ⟨ zero , γ ⟩'
  ≡⟨ eq t-fix γ ⟨
    f €⟨ zero , γ ⟩ tt
  ≡⟨ eq s-fix γ ⟩
    s ⟨ zero , γ ⟩' ∎
  where open ≡-Reasoning
eq (fixpoint-unique f t s t-fix s-fix) {x = suc n} γ =
  begin
    t ⟨ suc n , γ ⟩'
  ≡⟨ eq t-fix γ ⟨
    f €⟨ suc n , γ ⟩ (t ⟨ n , _ ⟩')
  ≡⟨ cong (f €⟨ suc n , γ ⟩_) (eq (fixpoint-unique f t s t-fix s-fix) {x = n}  _) ⟩
    f €⟨ suc n , γ ⟩ (s ⟨ n , _ ⟩')
  ≡⟨ eq s-fix γ ⟩
    s ⟨ suc n , γ ⟩' ∎
  where open ≡-Reasoning

löb'-β : {T : Ty Γ} {t : Tm (Γ ,, ▻' T) (T [ π ])} →
         ι⁻¹[ ty-weaken-subst _ ] (t [ next' (löb' T t) /v ]') ≅ᵗᵐ löb' T t
löb'-β {T = T} {t = t} =
  begin
    ι⁻¹[ ty-weaken-subst _ ] (t [ next' (löb' T t) /v ]')
  ≅⟨ ⇛-β t _ ⟨
    app (lam (▻' T) t) (next' (löb' T t))
  ≅⟨ löb-is-fixpoint _ ⟩
    löb' T t ∎
  where open ≅ᵗᵐ-Reasoning

löb-cong : (T : Ty Γ) {f f' : Tm Γ (▻' T ⇛ T)} → f ≅ᵗᵐ f' → löb T f ≅ᵗᵐ löb T f'
eq (löb-cong T f=f') {zero} γ = cong (_$⟨ z≤n , _ ⟩ tt) (eq f=f' γ)
eq (löb-cong T f=f') {suc n} _ = €-cong f=f' (eq (löb-cong T f=f') {n} _)

löb-ι : {T : Ty Γ} {T' : Ty Γ} {T=T' : T ≅ᵗʸ T'} (f : Tm Γ (▻' T' ⇛ T')) →
        ι[ T=T' ] (löb T' f) ≅ᵗᵐ löb T (ι[ ⇛-cong (▻'-cong T=T') T=T' ] f)
eq (löb-ι f) {zero} _ = refl
eq (löb-ι {Γ = Γ}{T = T}{T' = T'}{T=T' = T=T'} f) {suc n} γ = cong (func (to T=T')) (€-cong (reflᵗᵐ {t = f}) (
  begin
    löb T' f ⟨ n , _ ⟩'
  ≡⟨ eq (isoʳ T=T') _ ⟨
    func (from T=T') (func (to T=T') (löb T' f ⟨ n , _ ⟩'))
  ≡⟨ cong (func (from T=T')) (eq (löb-ι f) {n} _) ⟩
    func (from T=T') (löb T g ⟨ n , _ ⟩') ∎))
  where
    open ≡-Reasoning
    g : Tm Γ (▻' T ⇛ T)
    g = ι[ ⇛-cong (▻'-cong T=T') T=T' ] f

löb-natural : (σ : Δ ⇒ Γ) {T : Ty Γ} (f : Tm Γ (▻' T ⇛ T)) →
              (löb T f) [ σ ]' ≅ᵗᵐ löb (T [ σ ]) (ι⁻¹[ ⇛-cong (▻'-natural σ) reflᵗʸ ] (ι⁻¹[ ⇛-natural σ ] (f [ σ ]')))
eq (löb-natural σ f) {zero} δ = $-cong (f ⟨ 0 , func σ δ ⟩') refl
eq (löb-natural {Δ = Δ} {Γ = Γ} σ {T} f) {suc n} δ =
  begin
    f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , ctx-id Γ ⟩ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ (func σ δ) ⟩')
  ≡⟨ $-cong (f ⟨ suc n , func σ δ ⟩') refl ⟩
    f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩ (löb T f ⟨ n , Γ ⟪ n≤1+n n ⟫ (func σ δ) ⟩')
  ≡⟨ cong (f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩_) (Tm.naturality (löb T f) ≤-refl β) ⟨
    f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩ (T ⟪ ≤-refl , β ⟫ ((löb T f) [ σ ]' ⟨ n , Δ ⟪ n≤1+n n ⟫ δ ⟩'))
  ≡⟨ cong (f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩_ ∘ T ⟪ ≤-refl , β ⟫_) (eq (löb-natural σ f) {n} (Δ ⟪ n≤1+n n ⟫ δ)) ⟩
    f ⟨ suc n , func σ δ ⟩' $⟨ s≤s ≤-refl , α ⟩ (T ⟪ ≤-refl , β ⟫ (löb (T [ σ ]) g ⟨ n , Δ ⟪ n≤1+n n ⟫ δ ⟩')) ∎
  where
    open ≡-Reasoning
    α = _
    β = _
    g : Tm Δ (▻' (T [ σ ]) ⇛ (T [ σ ]))
    g = ι⁻¹[ ⇛-cong (▻'-natural σ) reflᵗʸ ] (ι⁻¹[ ⇛-natural σ ] (f [ σ ]'))


--------------------------------------------------
-- Löb induction with closed types

module _ {A : ClosedTy ω} (clA : IsClosedNatural A) where
  löb-cl : Tm (Γ ,, ▻ A) A → Tm Γ A
  löb-cl a = löb' A (ι[ transᵗʸ (closed-natural clA _) (symᵗʸ (closed-natural clA _)) ]
                    (ιc[ ,,-cong (▻-cong (closed-natural clA _)) ]' a))

  next-cl : Tm Γ A → Tm Γ (▻ A)
  next-cl a = ι⁻¹[ ▻-cong (closed-natural clA _) ] next' a

  löb-cl-β : (a : Tm (Γ ,, ▻ A) A) → löb-cl a ≅ᵗᵐ a [ clA ∣ next-cl (löb-cl a) /cl⟨ dra-closed later clA ⟩ ]cl
  löb-cl-β a =
    begin
      löb' A (ι[ transᵗʸ (closed-natural clA π) (symᵗʸ (closed-natural clA _))]
             (ιc[ ,,-cong (▻-cong (closed-natural clA (from-earlier _))) ]' a))
    ≅⟨ löb'-β ⟨
      ι⁻¹[ ty-weaken-subst _ ]
          ((ι[ transᵗʸ (closed-natural clA π) (symᵗʸ (closed-natural clA _)) ]
           (ιc[ ,,-cong (▻-cong (closed-natural clA (from-earlier _))) ]' a))
        [ next' (löb-cl a) /v ]')
    ≅⟨ ι⁻¹-cong ι-subst-commute ⟨
      ι⁻¹[ ty-weaken-subst _ ]
          (ι[ ty-subst-cong-ty (next' (löb-cl a) /v) (transᵗʸ (closed-natural clA π)
                                                              (symᵗʸ (closed-natural clA _))) ]
          ((ιc[ ,,-cong (▻-cong (closed-natural clA (from-earlier _))) ]' a)
          [ next' (löb-cl a) /v ]'))
    ≅⟨ ι⁻¹-cong (ι-cong (tm-subst-cong-subst-2-1 a (,,-cong-/v (▻-cong (closed-natural clA _)) _))) ⟩
      ι⁻¹[ ty-weaken-subst _ ]
      (ι[ ty-subst-cong-ty (next' (löb-cl a) /v) (transᵗʸ (closed-natural clA π)
                                                          (symᵗʸ (closed-natural clA _))) ]
      (ι[ ty-subst-cong-subst-2-1 A (,,-cong-/v (▻-cong (closed-natural clA (from-earlier _))) (next' (löb-cl a))) ]
      (a [ next-cl (löb-cl a) /v ]')))
    ≅⟨ ι⁻¹-cong (transᵗᵐ (transᵗᵐ (ι-congᵉ ty-subst-cong-ty-trans) ι-trans) (ι-cong (ι-congᵉ-2-2
       (transᵉ (transᵗʸ-congˡ ty-subst-cong-ty-sym) (move-symᵗʸ-out (symᵉ (closed-substs-eq-2-1 clA _))))))) ⟩
      ι⁻¹[ ty-weaken-subst _ ]
      (ι[ ty-subst-cong-ty (next' (löb-cl a) /v) (closed-natural clA π) ]
      (ι[ closed-natural clA (next' (löb-cl a) /v) ]
      (ι⁻¹[ closed-natural clA (next-cl (löb-cl a) /v) ]
      (a [ next-cl (löb-cl a) /v ]'))))
    ≅⟨ ι⁻¹-cong (ι-congᵉ-2-2 (closed-⊚ clA _ _)) ⟩
      ι⁻¹[ ty-weaken-subst (next' (löb-cl a)) ]
      (ι[ ty-subst-comp A π (next' (löb-cl a) /v) ]
      (ι[ closed-natural clA (π ⊚ (next' (löb-cl a) /v)) ]
      (ι⁻¹[ closed-natural clA (next-cl (löb-cl a) /v) ]
      (a [ next-cl (löb-cl a) /v ]'))))
    ≅⟨ transᵗᵐ ι⁻¹-trans (ι⁻¹-cong (transᵗᵐ ι⁻¹-trans (ι⁻¹-cong ι-symˡ))) ⟩
      ι⁻¹[ ty-subst-id A ]
      (ι⁻¹[ ty-subst-cong-subst (ctx-ext-subst-β₁ (id-subst _) (next' (löb-cl a) [ id-subst _ ]')) A ]
      (ι[ closed-natural clA (π ⊚ (next' (löb-cl a) /v)) ]
      (ι⁻¹[ closed-natural clA (next-cl (löb-cl a) /v) ]
      (a [ next-cl (löb-cl a) /v ]'))))
    ≅⟨ ι⁻¹-cong (transᵗᵐ (ι-congᵉ (symᵉ ty-subst-cong-subst-sym)) (ι-congᵉ-2-1 (closed-subst-eq clA _))) ⟩
      ι⁻¹[ ty-subst-id A ]
      (ι[ closed-natural clA (id-subst _) ]
      (ι⁻¹[ closed-natural clA (next-cl (löb-cl a) /v) ]
      (a [ next-cl (löb-cl a) /v ]')))
    ≅⟨ ι-congᵉ-2-0 (transᵉ (transᵗʸ-congʳ (closed-id clA)) symᵗʸ-invˡ) ⟩
      ι⁻¹[ closed-natural clA (next-cl (löb-cl a) /v) ]
      (a [ next-cl (löb-cl a) /v ]')
    ≅⟨⟩
      a [ clA ∣ next-cl (löb-cl a) /v ]cl
    ≅⟨ cl-tm-subst-cong-subst clA (/v-/cl (dra-closed later clA) (next-cl (löb-cl a))) ⟩
      a [ clA ∣ next-cl (löb-cl a) /cl⟨ dra-closed later clA ⟩ ]cl ∎
    where open ≅ᵗᵐ-Reasoning
