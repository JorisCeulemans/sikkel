module GuardedRecursion.Modalities.Bundles where

open import Categories
open import Modalities
open import GuardedRecursion.Modalities.Later
open import GuardedRecursion.Modalities.Timeless
open import GuardedRecursion.Modalities.AllNow
open import GuardedRecursion.Modalities.Instances

later : Modality ω ω
later = record
  { ctx-op = ◄
  ; mod = ▻
  ; mod-cong = ▻-cong
  ; mod-natural = ▻-natural
  ; mod-intro = next
  ; mod-intro-cong = next-cong
  ; mod-intro-natural = next-natural
  ; mod-intro-ι = next-ι
  ; mod-elim = prev
  ; mod-elim-cong = prev-cong
  ; mod-β = prev-next
  ; mod-η = next-prev
  }

timeless : Modality ★ ω
timeless = record
  { ctx-op = now
  ; mod = timeless-ty
  ; mod-cong = timeless-ty-cong
  ; mod-natural = timeless-ty-natural
  ; mod-intro = timeless-tm
  ; mod-intro-cong = timeless-tm-cong
  ; mod-intro-natural = timeless-tm-natural
  ; mod-intro-ι = timeless-tm-ι
  ; mod-elim = untimeless-tm
  ; mod-elim-cong = untimeless-tm-cong
  ; mod-β = timeless-ty-β
  ; mod-η = timeless-ty-η
  }

allnow : Modality ω ★
allnow = record
  { ctx-op = timeless-ctx
  ; mod = allnow-ty
  ; mod-cong = allnow-ty-cong
  ; mod-natural = allnow-ty-natural
  ; mod-intro = allnow-tm
  ; mod-intro-cong = allnow-tm-cong
  ; mod-intro-natural = allnow-tm-natural
  ; mod-intro-ι = allnow-tm-ι
  ; mod-elim = unallnow-tm
  ; mod-elim-cong = unallnow-tm-cong
  ; mod-β = allnow-ty-β
  ; mod-η = allnow-ty-η
  }
