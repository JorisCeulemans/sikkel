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

later : DRA ω ω
ctx-functor later = earlier-functor
⟨_∣_⟩ later = ▻
dra-map later = ▻-map
dra-map-cong later = ▻-map-cong
dra-map-id later = ▻-map-id
dra-map-⊙ later = ▻-map-comp
dra-natural later = ▻-natural
dra-natural-map later = later-natural-map
dra-natural-id-map later = later-natural-id-map
dra-natural-⊚-map later = later-natural-⊚-map
dra-natural-subst-eq-map later = later-natural-subst-eq-map
dra-intro later = next
dra-intro-cong later = next-cong
dra-intro-natural later = next-natural
dra-intro-convert later = next-convert
dra-elim later = prev
dra-elim-cong later = prev-cong
dra-β later = prev-next
dra-η later = next-prev

now-functor : CtxFunctor ω ★
ctx-op now-functor = now
is-functor now-functor = now-is-functor

constantly : DRA ★ ω
ctx-functor constantly = now-functor
⟨_∣_⟩ constantly = constantly-ty
dra-map constantly = constantly-ty-map
dra-map-cong constantly = constantly-ty-map-cong
dra-map-id constantly = constantly-ty-map-id
dra-map-⊙ constantly = constantly-ty-map-⊙
dra-natural constantly = constantly-ty-natural
dra-natural-map constantly = constantly-ty-natural-map
dra-natural-id-map constantly = constantly-ty-natural-id-map
dra-natural-⊚-map constantly = constantly-ty-natural-⊚-map
dra-natural-subst-eq-map constantly = constantly-ty-natural-subst-eq-map
dra-intro constantly = constantly-tm
dra-intro-cong constantly = constantly-tm-cong
dra-intro-natural constantly = constantly-tm-natural
dra-intro-convert constantly = constantly-tm-convert
dra-elim constantly = unconstantly-tm
dra-elim-cong constantly = unconstantly-tm-cong
dra-β constantly = constantly-ty-β
dra-η constantly = constantly-ty-η

constantly-ctx-functor : CtxFunctor ★ ω
ctx-op constantly-ctx-functor = constantly-ctx
is-functor constantly-ctx-functor = constantly-ctx-is-functor

forever : DRA ω ★
ctx-functor forever = constantly-ctx-functor
⟨_∣_⟩ forever = forever-ty
dra-map forever = forever-ty-map
dra-map-cong forever = forever-ty-map-cong
dra-map-id forever = forever-ty-map-id
dra-map-⊙ forever = forever-ty-map-⊙
dra-natural forever = forever-ty-natural
dra-natural-map forever = forever-ty-natural-map
dra-natural-id-map forever = forever-ty-natural-id-map
dra-natural-⊚-map forever = forever-ty-natural-⊚-map
dra-natural-subst-eq-map forever = forever-ty-natural-subst-eq-map
dra-intro forever = forever-tm
dra-intro-cong forever = forever-tm-cong
dra-intro-natural forever = forever-tm-natural
dra-intro-convert forever = forever-convert-tm
dra-elim forever = unforever-tm
dra-elim-cong forever = unforever-tm-cong
dra-β forever = forever-ty-β
dra-η forever = forever-ty-η
