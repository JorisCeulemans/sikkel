module Applications.GuardedRecursion.Model.Modalities.Bundles where

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Modality
open import Applications.GuardedRecursion.Model.Modalities.Later
open import Applications.GuardedRecursion.Model.Modalities.Constantly
open import Applications.GuardedRecursion.Model.Modalities.Forever

earlier-functor : CtxFunctor ω ω
ctx-op earlier-functor = ◄
is-functor earlier-functor = ◄-is-functor

later : Modality ω ω
ctx-functor later = earlier-functor
⟨_∣_⟩ later = ▻
mod-map later = ▻-map
mod-map-cong later = ▻-map-cong
mod-map-id later = ▻-map-id
mod-map-⊙ later = ▻-map-comp
mod-natural later = ▻-natural
mod-natural-map later = later-natural-map
mod-natural-id-map later = later-natural-id-map
mod-natural-⊚-map later = later-natural-⊚-map
mod-natural-subst-eq-map later = later-natural-subst-eq-map
mod-intro later = next
mod-intro-cong later = next-cong
mod-intro-natural later = next-natural
mod-intro-convert later = next-convert
mod-elim later = prev
mod-elim-cong later = prev-cong
mod-β later = prev-next
mod-η later = next-prev

now-functor : CtxFunctor ω ★
ctx-op now-functor = now
is-functor now-functor = now-is-functor

constantly : Modality ★ ω
ctx-functor constantly = now-functor
⟨_∣_⟩ constantly = constantly-ty
mod-map constantly = constantly-ty-map
mod-map-cong constantly = constantly-ty-map-cong
mod-map-id constantly = constantly-ty-map-id
mod-map-⊙ constantly = constantly-ty-map-⊙
mod-natural constantly = constantly-ty-natural
mod-natural-map constantly = constantly-ty-natural-map
mod-natural-id-map constantly = constantly-ty-natural-id-map
mod-natural-⊚-map constantly = constantly-ty-natural-⊚-map
mod-natural-subst-eq-map constantly = constantly-ty-natural-subst-eq-map
mod-intro constantly = constantly-tm
mod-intro-cong constantly = constantly-tm-cong
mod-intro-natural constantly = constantly-tm-natural
mod-intro-convert constantly = constantly-tm-convert
mod-elim constantly = unconstantly-tm
mod-elim-cong constantly = unconstantly-tm-cong
mod-β constantly = constantly-ty-β
mod-η constantly = constantly-ty-η

constantly-ctx-functor : CtxFunctor ★ ω
ctx-op constantly-ctx-functor = constantly-ctx
is-functor constantly-ctx-functor = constantly-ctx-is-functor

forever : Modality ω ★
ctx-functor forever = constantly-ctx-functor
⟨_∣_⟩ forever = forever-ty
mod-map forever = forever-ty-map
mod-map-cong forever = forever-ty-map-cong
mod-map-id forever = forever-ty-map-id
mod-map-⊙ forever = forever-ty-map-⊙
mod-natural forever = forever-ty-natural
mod-natural-map forever = forever-ty-natural-map
mod-natural-id-map forever = forever-ty-natural-id-map
mod-natural-⊚-map forever = forever-ty-natural-⊚-map
mod-natural-subst-eq-map forever = forever-ty-natural-subst-eq-map
mod-intro forever = forever-tm
mod-intro-cong forever = forever-tm-cong
mod-intro-natural forever = forever-tm-natural
mod-intro-convert forever = forever-convert-tm
mod-elim forever = unforever-tm
mod-elim-cong forever = unforever-tm-cong
mod-β forever = forever-ty-β
mod-η forever = forever-ty-η
