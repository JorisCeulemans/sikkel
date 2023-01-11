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
mod-cong later = ▻-cong
mod-cong-refl later = ▻-cong-refl
mod-cong-sym later = ▻-cong-sym
mod-cong-trans later = ▻-cong-trans
mod-cong-cong later = ▻-cong-cong
mod-natural later = ▻-natural
mod-natural-ty-eq later = later-natural-ty-eq
mod-natural-id later = later-natural-id
mod-natural-⊚ later = later-natural-⊚
mod-natural-subst-eq later = later-natural-subst-eq
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

constantly : Modality ★ ω
ctx-functor constantly = now-functor
⟨_∣_⟩ constantly = constantly-ty
mod-cong constantly = constantly-ty-cong
mod-cong-refl constantly = constantly-ty-cong-refl
mod-cong-sym constantly = constantly-ty-cong-sym
mod-cong-trans constantly = constantly-ty-cong-trans
mod-cong-cong constantly = constantly-ty-cong-cong
mod-natural constantly = constantly-ty-natural
mod-natural-ty-eq constantly = constantly-ty-natural-ty-eq
mod-natural-id constantly = constantly-ty-natural-id
mod-natural-⊚ constantly = constantly-ty-natural-⊚
mod-natural-subst-eq constantly = constantly-ty-natural-subst-eq
mod-intro constantly = constantly-tm
mod-intro-cong constantly = constantly-tm-cong
mod-intro-natural constantly = constantly-tm-natural
mod-intro-ι constantly = constantly-tm-ι
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
mod-cong forever = forever-ty-cong
mod-cong-refl forever = forever-ty-cong-refl
mod-cong-sym forever = forever-ty-cong-sym
mod-cong-trans forever = forever-ty-cong-trans
mod-cong-cong forever = forever-ty-cong-cong
mod-natural forever = forever-ty-natural
mod-natural-ty-eq forever = forever-ty-natural-ty-eq
mod-natural-id forever = forever-ty-natural-id
mod-natural-⊚ forever = forever-ty-natural-⊚
mod-natural-subst-eq forever = forever-ty-natural-subst-eq
mod-intro forever = forever-tm
mod-intro-cong forever = forever-tm-cong
mod-intro-natural forever = forever-tm-natural
mod-intro-ι forever = forever-tm-ι
mod-elim forever = unforever-tm
mod-elim-cong forever = unforever-tm-cong
mod-β forever = forever-ty-β
mod-η forever = forever-ty-η
