--------------------------------------------------
-- Some instances for the naturality solver to work with guarded recursion
--------------------------------------------------

module GuardedRecursion.Modalities.Instances where

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
  ctx-map-id {{◄-functor}} = ◄-subst-id
  ctx-map-⊚ {{◄-functor}} = ◄-subst-⊚

  ▻-un : IsUnaryNatural ▻
  natural-un {{▻-un}} = ▻-natural
  cong-un {{▻-un}} = ▻-cong

  now-functor : IsCtxFunctor now
  IsCtxFunctor.ctx-map now-functor = now-subst
  IsCtxFunctor.ctx-map-id now-functor = now-subst-id
  IsCtxFunctor.ctx-map-⊚ now-functor = now-subst-⊚

  timeless-ty-un : IsUnaryNatural timeless-ty
  IsUnaryNatural.natural-un timeless-ty-un = λ σ → timeless-ty-natural σ
  IsUnaryNatural.cong-un timeless-ty-un = timeless-ty-cong

  timeless-ctx-functor : IsCtxFunctor timeless-ctx
  IsCtxFunctor.ctx-map timeless-ctx-functor = timeless-subst
  IsCtxFunctor.ctx-map-id timeless-ctx-functor = timeless-subst-id
  IsCtxFunctor.ctx-map-⊚ timeless-ctx-functor = timeless-subst-⊚

  allnow-ty-un : IsUnaryNatural allnow-ty
  IsUnaryNatural.natural-un allnow-ty-un = λ σ → allnow-ty-natural σ
  IsUnaryNatural.cong-un allnow-ty-un = allnow-ty-cong
