module Applications.GuardedRecursion.Model.Modalities.Later.Closed where

open import Model.BaseCategory
open import Model.CwF-Structure
open import Applications.GuardedRecursion.Model.Modalities.Later
open import Applications.GuardedRecursion.Model.Modalities.Bundles
open import Model.DRA

private variable
  Γ : Ctx ω


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
