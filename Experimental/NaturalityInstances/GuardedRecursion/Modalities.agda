--------------------------------------------------
-- This module reexports everything that is related
-- to the different modalities for working with
-- guarded recursion. Moreover, it establishes the
-- 3 modalities as elements of the type Modality.
--------------------------------------------------

module Experimental.NaturalityInstances.GuardedRecursion.Modalities where

open import Experimental.NaturalityInstances.GuardedRecursion.Modalities.Later public
open import GuardedRecursion.Modalities.Timeless public
open import GuardedRecursion.Modalities.AllNow public
open import GuardedRecursion.Modalities.Interaction public
open import Experimental.NaturalityInstances.GuardedRecursion.Modalities.Instances public

open import Categories
open import CwF-Structure.ContextFunctors
open import Modalities

earlier-functor : CtxFunctor ω ω
ctx-op earlier-functor = ◄
is-functor earlier-functor = ◄-is-functor

later : Modality ω ω
ctx-functor later = earlier-functor
⟨_∣_⟩ later = ▻
mod-cong later = ▻-cong
mod-natural later = ▻-natural
mod-intro later = next
mod-intro-cong later = next-cong
mod-intro-natural later = next-natural
mod-intro-ι later = next-ι
mod-elim later = prev
mod-elim-cong later = prev-cong
mod-β later = prev-next
mod-η later = next-prev

now-functor : CtxFunctor ω ★
ctx-op now-functor = now
is-functor now-functor = now-is-functor

timeless : Modality ★ ω
ctx-functor timeless = now-functor
⟨_∣_⟩ timeless = timeless-ty
mod-cong timeless = timeless-ty-cong
mod-natural timeless = timeless-ty-natural
mod-intro timeless = timeless-tm
mod-intro-cong timeless = timeless-tm-cong
mod-intro-natural timeless = timeless-tm-natural
mod-intro-ι timeless = timeless-tm-ι
mod-elim timeless = untimeless-tm
mod-elim-cong timeless = untimeless-tm-cong
mod-β timeless = timeless-ty-β
mod-η timeless = timeless-ty-η

timeless-ctx-functor : CtxFunctor ★ ω
ctx-op timeless-ctx-functor = timeless-ctx
is-functor timeless-ctx-functor = timeless-ctx-is-functor

allnow : Modality ω ★
ctx-functor allnow = timeless-ctx-functor
⟨_∣_⟩ allnow = allnow-ty
mod-cong allnow = allnow-ty-cong
mod-natural allnow = allnow-ty-natural
mod-intro allnow = allnow-tm
mod-intro-cong allnow = allnow-tm-cong
mod-intro-natural allnow = allnow-tm-natural
mod-intro-ι allnow = allnow-tm-ι
mod-elim allnow = unallnow-tm
mod-elim-cong allnow = unallnow-tm-cong
mod-β allnow = allnow-ty-β
mod-η allnow = allnow-ty-η
