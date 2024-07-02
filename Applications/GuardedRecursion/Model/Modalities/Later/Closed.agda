--------------------------------------------------
-- Behaviour of ▻ and ▻' with respect to closed types
--------------------------------------------------

module Applications.GuardedRecursion.Model.Modalities.Later.Closed where

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.DRA
open import Applications.GuardedRecursion.Model.Modalities.Later.Base
open import Applications.GuardedRecursion.Model.Modalities.Later.NoLock

private variable
  Γ Δ : Ctx ω


module _ {A : ClosedTy ω} (clA : IsClosedNatural A) where
  ▻'-closed-id : {Γ : Ctx ω} →
                 transᵗʸ (▻'-natural (id-subst Γ)) (▻'-cong (closed-natural clA (id-subst Γ))) ≅ᵉ ty-subst-id (▻' A)
  ▻'-closed-id =
    transᵉ (transᵗʸ-congʳ (▻'-cong-cong (closed-id clA))) (
    transᵉ (transᵉ transᵗʸ-assoc (transᵗʸ-congʳ (
            transᵉ (symᵉ (dra-cong-trans later))
                   (dra-cong-cong later (transᵗʸ-congʳ (ty-subst-cong-ty-cong (symᵉ (transᵉ (transᵗʸ-congˡ ty-subst-cong-subst-refl) reflᵗʸ-unitˡ)) _)))))) (
    transᵉ (transᵗʸ-congʳ (dra-cong-cong later (ty-subst-ctx-transf-id (transf 𝟙≤later)))) (
    dra-natural-id later)))

  ▻'-closed-⊚ : {Γ Δ Θ : Ctx ω} (σ : Δ ⇒ Θ) (τ : Γ ⇒ Δ) →
                transᵗʸ (ty-subst-cong-ty τ (transᵗʸ (▻'-natural σ) (▻'-cong (closed-natural clA σ))))
                        (transᵗʸ (▻'-natural τ) (▻'-cong (closed-natural clA τ)))
                  ≅ᵉ
                transᵗʸ (ty-subst-comp (▻' A) σ τ)
                        (transᵗʸ (▻'-natural (σ ⊚ τ)) (▻'-cong (closed-natural clA (σ ⊚ τ))))
  ▻'-closed-⊚ σ τ =
      transᵉ (transᵗʸ-congˡ (ty-subst-cong-ty-cong (transᵉ transᵗʸ-assoc (transᵗʸ-congʳ (symᵉ (dra-cong-trans later)))) _)) (
      transᵉ (transᵗʸ-congˡ ty-subst-cong-ty-trans) (
      transᵉ transᵗʸ-assoc (
      transᵉ (transᵗʸ-congʳ (transᵉ (transᵗʸ-congʳ transᵗʸ-assoc) (symᵉ transᵗʸ-assoc))) (
    transᵉ (transᵗʸ-congʳ (transᵗʸ-congˡ (symᵉ (dra-natural-ty-eq later τ _)))) (
      transᵉ (transᵗʸ-congʳ (transᵉ (transᵗʸ-congˡ (transᵉ (transᵗʸ-congʳ (transᵉ (dra-cong-cong later ty-subst-cong-ty-trans) (dra-cong-trans later))) (symᵉ transᵗʸ-assoc))) (
                            transᵉ transᵗʸ-assoc (transᵗʸ-congʳ (transᵉ (symᵉ transᵗʸ-assoc) (
                            transᵗʸ-congˡ (transᵉ (symᵉ (dra-cong-trans later)) (dra-cong-cong later (
             symᵉ (ty-subst-cong-subst-2-2-natural _ _)))))))))) (
      transᵉ (transᵗʸ-congʳ (transᵗʸ-congʳ (transᵉ (transᵗʸ-congˡ (dra-cong-trans later)) (transᵉ transᵗʸ-assoc (transᵗʸ-congʳ (transᵉ (symᵉ ▻'-cong-trans) (
    transᵉ (▻'-cong-cong (closed-⊚ clA σ τ)) ▻'-cong-trans))))))) (
      transᵉ (transᵉ (transᵗʸ-congʳ (transᵉ transᵗʸ-assoc (transᵗʸ-congʳ (transᵉ (transᵗʸ-congʳ (symᵉ transᵗʸ-assoc)) (symᵉ transᵗʸ-assoc))))) (
              transᵉ (transᵗʸ-congʳ (transᵗʸ-congʳ (transᵗʸ-congˡ (transᵗʸ-congʳ (transᵗʸ-congʳ (dra-cong-cong later (symᵉ (ty-subst-cong-ty-cong (
                     transᵉ (transᵗʸ-congʳ (transᵉ ty-subst-cong-subst-sym (transᵉ (symᵗʸ-cong ty-subst-cong-subst-refl) symᵗʸ-reflᵗʸ))) reflᵗʸ-unitʳ) _)))))))) (
              transᵗʸ-congʳ (transᵗʸ-congʳ (transᵗʸ-congˡ (transᵉ (transᵗʸ-congʳ (symᵉ (dra-cong-trans later))) (symᵉ (dra-cong-trans later)))))))) (
    transᵉ (transᵗʸ-congʳ (transᵗʸ-congʳ (transᵗʸ-congˡ (dra-cong-cong later (ty-subst-ctx-transf-⊚ (transf 𝟙≤later)))))) (
      transᵉ (transᵉ (transᵗʸ-congʳ (transᵉ (transᵗʸ-congʳ (transᵗʸ-congˡ (dra-cong-trans later))) (transᵉ (transᵗʸ-congʳ transᵗʸ-assoc) (symᵉ transᵗʸ-assoc)))) (symᵉ transᵗʸ-assoc)) (
    transᵉ (transᵗʸ-congˡ (dra-natural-⊚ later σ τ)) (
      transᵉ transᵗʸ-assoc (
      transᵗʸ-congʳ (transᵉ (symᵉ transᵗʸ-assoc) (transᵗʸ-congˡ (
      transᵉ transᵗʸ-assoc (transᵗʸ-congʳ (
      transᵉ (symᵉ (dra-cong-trans later)) (dra-cong-cong later (
      transᵉ (symᵉ transᵗʸ-assoc) (
      transᵉ (transᵗʸ-congˡ (transᵗʸ-congʳ ty-subst-cong-subst-sym))
      transᵗʸ-cancelˡ-symʳ))))))))))))))))))))

  ▻'-closed-subst-eq : {Γ Δ : Ctx ω} {σ τ : Γ ⇒ Δ} (ε : σ ≅ˢ τ) →
                       transᵗʸ (ty-subst-cong-subst ε (▻' A)) (
                       transᵗʸ (▻'-natural τ) (
                       ▻'-cong (closed-natural clA τ)))
                         ≅ᵉ
                       transᵗʸ (▻'-natural σ) (▻'-cong (closed-natural clA σ))
  ▻'-closed-subst-eq ε =
      transᵉ (transᵉ (transᵗʸ-congʳ transᵗʸ-assoc) (symᵉ transᵗʸ-assoc)) (
    transᵉ (transᵗʸ-congˡ (dra-natural-subst-eq later ε)) (
      transᵉ (transᵉ (symᵉ transᵗʸ-assoc) (transᵗʸ-congˡ (transᵉ transᵗʸ-assoc (transᵗʸ-congʳ (symᵉ (dra-cong-trans later)))))) (
    transᵉ (transᵗʸ-congˡ (transᵗʸ-congʳ (dra-cong-cong later (ty-subst-ctx-transf-subst-eq (transf 𝟙≤later))))) (
      transᵉ (transᵉ (transᵗʸ-congˡ (transᵉ (transᵗʸ-congʳ (dra-cong-trans later)) (symᵉ transᵗʸ-assoc))) (
             transᵉ transᵗʸ-assoc (transᵗʸ-congʳ (transᵉ (symᵉ (dra-cong-trans later)) (dra-cong-cong later (symᵉ ty-subst-cong-ty-trans)))))) (
    transᵗʸ-congʳ (dra-cong-cong later (ty-subst-cong-ty-cong (closed-subst-eq clA ε) _)))))))

  ▻'-closed : IsClosedNatural (▻' A)
  closed-natural ▻'-closed σ = transᵗʸ (▻'-natural σ) (▻'-cong (closed-natural clA σ))
  closed-id ▻'-closed = ▻'-closed-id
  closed-⊚ ▻'-closed σ τ = ▻'-closed-⊚ σ τ
  closed-subst-eq ▻'-closed ε = ▻'-closed-subst-eq ε

cl-▻'-▻ : {A : ClosedTy ω} (clA : IsClosedNatural A) → ▻'-closed clA ≅ᶜᵗʸ dra-closed later clA
closed-ty-eq (cl-▻'-▻ clA) = dra-cong later (closed-natural clA (from-earlier _))
closed-ty-eq-natural (cl-▻'-▻ clA) σ =
    transᵉ (symᵉ transᵗʸ-assoc) (
  transᵉ (transᵗʸ-congˡ (symᵉ (dra-natural-ty-eq later σ _))) (
    transᵉ (transᵉ transᵗʸ-assoc (transᵗʸ-congʳ (symᵉ (dra-cong-trans later)))) (
  transᵉ (transᵗʸ-congʳ (dra-cong-cong later (closed-⊚ clA _ _))) (
  transᵉ (transᵗʸ-congʳ (dra-cong-cong later (transᵗʸ-congʳ (symᵉ (closed-subst-eq clA (key-subst-natural 𝟙≤later)))))) (
    transᵉ (transᵗʸ-congʳ (dra-cong-cong later (transᵗʸ-congʳ (transᵉ (transᵗʸ-congʳ (symᵉ transᵗʸ-cancelˡ-symˡ)) (transᵗʸ-congʳ transᵗʸ-assoc))))) (
  transᵉ (transᵗʸ-congʳ (dra-cong-cong later (transᵗʸ-congʳ (transᵗʸ-congʳ (transᵗʸ-congʳ (symᵉ (closed-⊚ clA _ _))))))) (
    transᵉ (transᵗʸ-congʳ (transᵉ (dra-cong-cong later (transᵉ (transᵗʸ-congʳ (symᵉ transᵗʸ-assoc)) (symᵉ transᵗʸ-assoc))) (dra-cong-trans later))) (
    transᵉ (symᵉ transᵗʸ-assoc) (transᵉ (transᵗʸ-congʳ (dra-cong-trans later)) (symᵉ transᵗʸ-assoc))))))))))

next-cl : {A : ClosedTy ω} (clA : IsClosedNatural A) → Tm Γ A → Tm Γ (▻ A)
next-cl clA a = ι⁻¹[ closed-ty-eq (cl-▻'-▻ clA) ] next' a
