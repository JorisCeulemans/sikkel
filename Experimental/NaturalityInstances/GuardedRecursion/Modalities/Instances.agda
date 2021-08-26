--------------------------------------------------
-- Some instances for the naturality solver to work with guarded recursion
--------------------------------------------------

module Experimental.NaturalityInstances.GuardedRecursion.Modalities.Instances where

open import Categories
open import CwF-Structure
open import Reflection.Naturality.TypeOperations
open import Experimental.NaturalityInstances.GuardedRecursion.Modalities.Later
open import GuardedRecursion.Modalities.Timeless
open import GuardedRecursion.Modalities.AllNow


instance
  ▻'-un : IsUnaryNatural ▻'
  natural-un {{▻'-un}} = ▻'-natural
  cong-un {{▻'-un}} = ▻'-cong

  ◄-is-functor : IsCtxFunctor ◄
  ctx-map {{◄-is-functor}} = ◄-subst
  ctx-map-cong {{◄-is-functor}} = ◄-subst-cong
  ctx-map-id {{◄-is-functor}} = ◄-subst-id
  ctx-map-⊚ {{◄-is-functor}} = ◄-subst-⊚

  ▻-un : IsUnaryNatural ▻
  natural-un {{▻-un}} = ▻-natural
  cong-un {{▻-un}} = ▻-cong

  now-is-functor : IsCtxFunctor now
  IsCtxFunctor.ctx-map now-is-functor = now-subst
  IsCtxFunctor.ctx-map-cong now-is-functor = now-subst-cong
  IsCtxFunctor.ctx-map-id now-is-functor = now-subst-id
  IsCtxFunctor.ctx-map-⊚ now-is-functor = now-subst-⊚

  timeless-ty-un : IsUnaryNatural timeless-ty
  IsUnaryNatural.natural-un timeless-ty-un = λ σ → timeless-ty-natural σ
  IsUnaryNatural.cong-un timeless-ty-un = timeless-ty-cong

  timeless-ctx-is-functor : IsCtxFunctor timeless-ctx
  IsCtxFunctor.ctx-map timeless-ctx-is-functor = timeless-subst
  IsCtxFunctor.ctx-map-cong timeless-ctx-is-functor = timeless-subst-cong
  IsCtxFunctor.ctx-map-id timeless-ctx-is-functor = timeless-subst-id
  IsCtxFunctor.ctx-map-⊚ timeless-ctx-is-functor = timeless-subst-⊚

  allnow-ty-un : IsUnaryNatural allnow-ty
  IsUnaryNatural.natural-un allnow-ty-un = λ σ → allnow-ty-natural σ
  IsUnaryNatural.cong-un allnow-ty-un = allnow-ty-cong

  ▻'-closed : {A : ClosedType ω} → {{IsClosedNatural A}} → IsClosedNatural (▻' A)
  closed-natural {{▻'-closed}} σ = ≅ᵗʸ-trans (▻'-natural σ) (▻'-cong (closed-natural σ))

  timeless-closed : {A : ClosedType ★} → {{IsClosedNatural A}} → IsClosedNatural (timeless-ty A)
  closed-natural {{timeless-closed}} σ = ≅ᵗʸ-trans (timeless-ty-natural σ) (timeless-ty-cong (closed-natural (now-subst σ)))

  allnow-closed : {A : ClosedType ω} → {{IsClosedNatural A}} → IsClosedNatural (allnow-ty A)
  closed-natural {{allnow-closed}} σ = ≅ᵗʸ-trans (allnow-ty-natural σ) (allnow-ty-cong (closed-natural (timeless-subst σ)))
