--------------------------------------------------
-- Some instances for the naturality solver to work with guarded recursion
--------------------------------------------------

module GuardedRecursion.Modalities.Instances where

open import Categories
open import CwF-Structure
open import Reflection.Naturality.TypeOperations
open import GuardedRecursion.Modalities.Later
open import GuardedRecursion.Modalities.Timeless
open import GuardedRecursion.Modalities.AllNow


instance
  ▻'-un : IsUnaryNatural ▻'
  natural-un {{▻'-un}} = ▻'-natural
  cong-un {{▻'-un}} = ▻'-cong

  ◄-functor : IsCtxFunctor ◄
  ctx-map {{◄-functor}} = ◄-subst
  ctx-map-cong {{◄-functor}} = ◄-subst-cong
  ctx-map-id {{◄-functor}} = ◄-subst-id
  ctx-map-⊚ {{◄-functor}} = ◄-subst-⊚

  ▻-un : IsUnaryNatural ▻
  natural-un {{▻-un}} = ▻-natural
  cong-un {{▻-un}} = ▻-cong

  now-functor : IsCtxFunctor now
  ctx-map {{now-functor}} = now-subst
  ctx-map-cong {{now-functor}} = now-subst-cong
  ctx-map-id {{now-functor}} = now-subst-id
  ctx-map-⊚ {{now-functor}} = now-subst-⊚

  timeless-ty-un : IsUnaryNatural timeless-ty
  IsUnaryNatural.natural-un timeless-ty-un = λ σ → timeless-ty-natural σ
  IsUnaryNatural.cong-un timeless-ty-un = timeless-ty-cong

  timeless-ctx-functor : IsCtxFunctor timeless-ctx
  ctx-map {{timeless-ctx-functor}} = timeless-subst
  ctx-map-cong {{timeless-ctx-functor}} = timeless-subst-cong
  ctx-map-id {{timeless-ctx-functor}} = timeless-subst-id
  ctx-map-⊚ {{timeless-ctx-functor}} = timeless-subst-⊚

  allnow-ty-un : IsUnaryNatural allnow-ty
  IsUnaryNatural.natural-un allnow-ty-un = λ σ → allnow-ty-natural σ
  IsUnaryNatural.cong-un allnow-ty-un = allnow-ty-cong

instance
  ▻'-closed : {A : ClosedType ω} {{_ : IsClosedNatural A}} → IsClosedNatural (▻' A)
  closed-natural {{▻'-closed}} σ = ≅ᵗʸ-trans (▻'-natural σ) (▻'-cong (closed-natural σ))

  ▻-closed : {A : ClosedType ω} {{_ : IsClosedNatural A}} → IsClosedNatural (▻ A)
  closed-natural {{▻-closed}} σ = ≅ᵗʸ-trans (▻-natural σ) (▻-cong (closed-natural (◄-subst σ)))

  timeless-closed : {A : ClosedType ★} {{_ : IsClosedNatural A}} → IsClosedNatural (timeless-ty A)
  closed-natural {{timeless-closed}} σ = ≅ᵗʸ-trans (timeless-ty-natural σ) (timeless-ty-cong (closed-natural (now-subst σ)))

  allnow-closed : {A : ClosedType ω} {{_ : IsClosedNatural A}} → IsClosedNatural (allnow-ty A)
  closed-natural {{allnow-closed}} σ = ≅ᵗʸ-trans (allnow-ty-natural σ) (allnow-ty-cong (closed-natural (timeless-subst σ)))
