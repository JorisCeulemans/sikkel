{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- Some instances for the naturality solver to work with guarded recursion
--
-- Note: The option omega-in-omega is used here in order to work with
-- Setω as a valid sort (which is not possible in Agda 2.6.1 without
-- this option). This code should typecheck without this option in Agda 2.6.2
-- once released.
-- Note 2: The instances defined in this file will eventually be moved
-- to the files in which the respective type operations are defined.
-- However, we do not want to use the option omega-in-omega there.
--------------------------------------------------

module Reflection.Naturality.GuardedRecursion.Instances where

open import Reflection.Naturality
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
  IsUnaryNatural.natural-un timeless-ty-un = λ σ → timeless-ty-natural σ _
  IsUnaryNatural.cong-un timeless-ty-un = timeless-ty-cong

  timeless-ctx-functor : IsCtxFunctor timeless-ctx
  IsCtxFunctor.ctx-map timeless-ctx-functor = timeless-subst
  IsCtxFunctor.ctx-map-id timeless-ctx-functor = timeless-subst-id
  IsCtxFunctor.ctx-map-⊚ timeless-ctx-functor = timeless-subst-⊚

  allnow-ty-un : IsUnaryNatural allnow-ty
  IsUnaryNatural.natural-un allnow-ty-un = λ σ → allnow-ty-natural σ _
  IsUnaryNatural.cong-un allnow-ty-un = allnow-ty-cong
