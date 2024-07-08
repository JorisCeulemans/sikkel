module Experimental.LogicalFramework.Instances.GuardedRecursion.MSTT where

import Data.Vec as Vec
import Data.Vec.Properties as Vec
open import Function
open import Function.Construct.Composition
open import Relation.Binary.PropositionalEquality

open import Preliminaries
import Model.CwF-Structure as M
open import Applications.GuardedRecursion.Model.Modalities.Forever as M using (ω-lim; OmegaLimit; to-ω-limit-eq)
open OmegaLimit using (limit; limit-natural)
open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter

import Experimental.LogicalFramework.Instances.GuardedRecursion.ModeTheory as GMT
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TypeExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TermExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.Normalization

open GMT
  using (ω; later; constantly; forever; guarded-mt; ltrⓜcst; ltr; 𝟙≤ltr; ltrⓜcstⓜfrv; cstⓜfrv≤𝟙; cstⓜfrv≤ltr)
  public
open ModeTheory guarded-mt public

guarded-mstt : MSTT-Parameter
MSTT-Parameter.ℳ guarded-mstt = guarded-mt
MSTT-Parameter.𝒯 guarded-mstt = guarded-ty-ext
MSTT-Parameter.𝓉 guarded-mstt = guarded-tm-ext
MSTT-Parameter.⟦𝓉⟧ guarded-mstt = guarded-tm-ext-sem
MSTT-Parameter.𝓉-norm guarded-mstt = guarded-tm-ext-norm


open import Experimental.LogicalFramework.MSTT guarded-mstt public
open import Experimental.LogicalFramework.Instances.GuardedRecursion.MSTT.Syntax public
  -- ^ Reexporting the notation for the type and term extension


open import Data.Unit
open GrowingVec
omega-limit-gstream-growvec-iso : (A : Ty ★) {{_ : ExtractableTy A}} →
                                  OmegaLimit (⟦ GStream A ⟧ty {M.constantly-ctx M.◇}) tt ↔ GrowingVec (extract-ty A)
omega-limit-gstream-growvec-iso A = mk↔ₛ′
  (λ ωl → growing-vec (λ n → Vec.map (Inverse.to (extract-ty-iso {A})) (limit ωl n))
                      (λ m≤n → trans (sym map-first-≤) (cong (Vec.map _) (
                               trans (sym (trans (Vec.map-cong (λ _ → M.strong-ty-id ⟦ A ⟧ty) _) (Vec.map-id _))) (
                               limit-natural ωl m≤n)))))
  (λ gv → ω-lim (λ n → Vec.map (Inverse.from (extract-ty-iso {A})) (vec gv n))
                (λ m≤n → trans (Vec.map-cong (λ _ → M.strong-ty-id ⟦ A ⟧ty) _) (
                         trans (Vec.map-id _) (
                         trans (sym map-first-≤) (
                         cong (Vec.map _) (vec-natural gv m≤n))))))
  (λ gv → to-growing-vec-eq (λ n → trans (sym (Vec.map-∘ _ _ _)) (
                                   trans (Vec.map-cong (Inverse.strictlyInverseˡ (extract-ty-iso {A})) _) (
                                   Vec.map-id _))))
  (λ ωl → to-ω-limit-eq (λ n → trans (sym (Vec.map-∘ _ _ _)) (
                               trans (Vec.map-cong (Inverse.strictlyInverseʳ (extract-ty-iso {A})) _) (
                               Vec.map-id _))))

instance
  stream-extractable : {A : Ty ★} → {{ExtractableTy A}} →
                       ExtractableTy ⟨ forever ∣ GStream A ⟩
  AgdaTy {{stream-extractable {A}}} = Stream (extract-ty A)
  extract-ty-iso-◇ {{stream-extractable {A}}} =
    growvec-stream-iso ↔-∘ omega-limit-gstream-growvec-iso A
