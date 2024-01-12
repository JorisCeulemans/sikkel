--------------------------------------------------
-- Properties of DRAs with respect to limits (i.e. products, unit).
--   Althought they are not limits, we also consider DRA behaviour with respect to function types.
--------------------------------------------------

module Model.DRA.Limits where

open import Model.DRA.Basics

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Type.Function
open import Model.Type.Product
open import Model.Type.Constant

private
  variable
    C D E : BaseCategory


module _ (μ : DRA C D) {Γ : Ctx D} where

  module _ {T S : Ty (Γ ,lock⟨ μ ⟩)} where

    -- A DRA is a functor (at the term level, i.e. similar to a Haskell functor).
    dra-tm-map : Tm (Γ ,lock⟨ μ ⟩) (T ⇛ S) → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ μ ∣ S ⟩
    dra-tm-map f t = dra-intro μ (f $ dra-elim μ t)

    infixl 12 dra-tm-map
    syntax dra-tm-map μ f t = f ⟨$- μ ⟩ t

    -- A DRA is also an applicative functor.
    dra-⊛ : Tm Γ ⟨ μ ∣ T ⇛ S ⟩ → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ μ ∣ S ⟩
    dra-⊛ f t = dra-intro μ (dra-elim μ f $ dra-elim μ t)

    infixl 12 dra-⊛
    syntax dra-⊛ μ f t = f ⊛⟨ μ ⟩ t

    -- DRAs preserve products (up to isomorphism).
    from-dra-⊠ : Tm Γ ⟨ μ ∣ T ⊠ S ⟩ → Tm Γ (⟨ μ ∣ T ⟩ ⊠ ⟨ μ ∣ S ⟩)
    from-dra-⊠ p = pair (dra-intro μ (fst (dra-elim μ p))) (dra-intro μ (snd (dra-elim μ p)))

    to-dra-⊠ : Tm Γ (⟨ μ ∣ T ⟩ ⊠ ⟨ μ ∣ S ⟩) → Tm Γ ⟨ μ ∣ T ⊠ S ⟩
    to-dra-⊠ p = dra-intro μ (pair (dra-elim μ (fst p)) (dra-elim μ (snd p)))

    from-to-dra-⊠ : (p : Tm Γ (⟨ μ ∣ T ⟩ ⊠ ⟨ μ ∣ S ⟩)) → from-dra-⊠ (to-dra-⊠ p) ≅ᵗᵐ p
    from-to-dra-⊠ p = let p' = pair (dra-elim μ (fst p)) (dra-elim μ (snd p)) in
      begin
        pair (dra-intro μ (fst (dra-elim μ (dra-intro μ p'))))
             (dra-intro μ (snd (dra-elim μ (dra-intro μ p'))))
      ≅⟨ pair-cong (dra-intro-cong μ (fst-cong (dra-β μ p')))
                   (dra-intro-cong μ (snd-cong (dra-β μ p'))) ⟩
        pair (dra-intro μ (fst p'))
             (dra-intro μ (snd p'))
      ≅⟨ pair-cong (dra-intro-cong μ (β-⊠-fst _ (dra-elim μ (snd p))))
                   (dra-intro-cong μ (β-⊠-snd (dra-elim μ (fst p)) _)) ⟩
        pair (dra-intro μ (dra-elim μ (fst p)))
             (dra-intro μ (dra-elim μ (snd p)))
      ≅⟨ pair-cong (dra-η μ (fst p)) (dra-η μ (snd p)) ⟩
        pair (fst p)
             (snd p)
      ≅⟨ η-⊠ p ⟨
        p ∎
      where open ≅ᵗᵐ-Reasoning

    to-from-dra-⊠ : (p : Tm Γ ⟨ μ ∣ T ⊠ S ⟩) → to-dra-⊠ (from-dra-⊠ p) ≅ᵗᵐ p
    to-from-dra-⊠ p =
      let t = dra-intro μ (fst (dra-elim μ p))
          s = dra-intro μ (snd (dra-elim μ p))
      in begin
        dra-intro μ (pair (dra-elim μ (fst (pair t s)))
                          (dra-elim μ (snd (pair t s))))
      ≅⟨ dra-intro-cong μ (pair-cong (dra-elim-cong μ (β-⊠-fst t s))
                                     (dra-elim-cong μ (β-⊠-snd t s))) ⟩
        dra-intro μ (pair (dra-elim μ t)
                          (dra-elim μ s))
      ≅⟨ dra-intro-cong μ (pair-cong (dra-β μ _) (dra-β μ _)) ⟩
        dra-intro μ (pair (fst (dra-elim μ p))
                          (snd (dra-elim μ p)))
      ≅⟨ dra-intro-cong μ (η-⊠ (dra-elim μ p)) ⟨
        dra-intro μ (dra-elim μ p)
      ≅⟨ dra-η μ p ⟩
        p ∎
      where open ≅ᵗᵐ-Reasoning

  -- DRAs preserve the unit type (up to isomorphism).
  dra-unit' : Tm Γ ⟨ μ ∣ Unit' ⟩
  dra-unit' = dra-intro μ tt'

  dra-unit'-η : (t : Tm Γ ⟨ μ ∣ Unit' ⟩) → t ≅ᵗᵐ dra-unit'
  dra-unit'-η t =
    begin
      t
    ≅⟨ dra-η μ t ⟨
      dra-intro μ (dra-elim μ t)
    ≅⟨ dra-intro-cong μ (η-unit (dra-elim μ t)) ⟩
      dra-intro μ tt' ∎
    where open ≅ᵗᵐ-Reasoning
