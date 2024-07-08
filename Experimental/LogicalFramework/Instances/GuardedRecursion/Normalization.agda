module Experimental.LogicalFramework.Instances.GuardedRecursion.Normalization where

open import Data.Maybe
open import Data.Product hiding (_<*>_)
import Relation.Binary.PropositionalEquality as Ag

import Model.CwF-Structure as M
import Model.DRA as DRA
import Applications.GuardedRecursion.Model.Modalities as M
import Applications.GuardedRecursion.Model.Lob as M
import Applications.GuardedRecursion.Model.Streams.Guarded as M

open import Experimental.LogicalFramework.MSTT.Normalization.Helpers

open import Experimental.LogicalFramework.Instances.GuardedRecursion.ModeTheory
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TypeExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TermExtension
open import Experimental.LogicalFramework.Instances.GuardedRecursion.MSTT.Syntax

open import Experimental.LogicalFramework.MSTT.Syntax.Terms guarded-mt guarded-ty-ext guarded-tm-ext
open import Experimental.LogicalFramework.MSTT.Interpretation guarded-mt guarded-ty-ext guarded-tm-ext guarded-tm-ext-sem
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionNormalization guarded-mt guarded-ty-ext guarded-tm-ext guarded-tm-ext-sem



guarded-tm-ext-norm : TmExtNormalization
TmExtNormalization.normalize-tm-code guarded-tm-ext-norm rec-norm (löb-code A) {(_ , x) , _} (t , _) =
  normalize-löb <$> rec-norm t
  where
    normalize-löb : NormalizeResult t → NormalizeResult (löb[later∣ x ∈ A ] t)
    normalize-löb (normres nt et) = normres (löb[later∣ x ∈ A ] nt)
                                            (M.löb-cl-cong (ty-closed-natural A) (M.cl-tm-subst-cong-tm (ty-closed-natural A) et))
TmExtNormalization.normalize-tm-code guarded-tm-ext-norm rec-norm (g-cons-code A) (h , t , _) =
  normalize-g-cons <$> rec-norm h <*> rec-norm t
  where
    normalize-g-cons : NormalizeResult h → NormalizeResult t → NormalizeResult (g-cons h t)
    normalize-g-cons (normres nh eh) (normres nt et) =
      normres (g-cons nh nt)
              (M.g-cl-cons-cong (ty-closed-natural A) (DRA.dra-intro-cong M.constantly (M.cl-tm-subst-cong-tm (ty-closed-natural A) eh))
                                                      (DRA.dra-intro-cong M.later (M.cl-tm-subst-cong-tm (ty-closed-natural (GStream A)) et)))
TmExtNormalization.normalize-tm-code guarded-tm-ext-norm rec-norm (g-head-code A) (s , _) =
  normalize-g-head <$> rec-norm s
  where
    normalize-g-head : NormalizeResult s → NormalizeResult (g-head s)
    normalize-g-head (normres (g-cons nh nt) es) = normres (mod⟨ constantly ⟩ nh) (
      M.transᵗᵐ (M.g-head-cong (M.transᵗᵐ (M.cl-tm-subst-id (ty-closed-natural (GStream A)) _) es)) (
      M.transᵗᵐ (M.gstream-cl-β-head (ty-closed-natural A)) (
      DRA.dra-intro-cong M.constantly (M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural A) (DRA.lock-fmap-id M.constantly))
                                                 (M.cl-tm-subst-id (ty-closed-natural A) _)))))
    normalize-g-head (normres ns             es) = normres (g-head ns) (M.g-head-cong (M.cl-tm-subst-cong-tm (ty-closed-natural (GStream A)) es))
TmExtNormalization.normalize-tm-code guarded-tm-ext-norm rec-norm (g-tail-code A) (s , _) =
  normalize-g-tail <$> rec-norm s
  where
    normalize-g-tail : NormalizeResult s → NormalizeResult (g-tail s)
    normalize-g-tail (normres (g-cons nh nt) es) = normres (mod⟨ later ⟩ nt) (
      M.transᵗᵐ (M.g-cl-tail-cong (ty-closed-natural A) (M.transᵗᵐ (M.cl-tm-subst-id (ty-closed-natural (GStream A)) _) es)) (
      M.transᵗᵐ (M.gstream-cl-β-tail (ty-closed-natural A)) (
      DRA.dra-intro-cong M.later (M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural (GStream A)) (DRA.lock-fmap-id M.later))
                                            (M.cl-tm-subst-id (ty-closed-natural (GStream A)) _)))))
    normalize-g-tail (normres ns             es) =
      normres (g-tail ns) (M.g-cl-tail-cong (ty-closed-natural A) (M.cl-tm-subst-cong-tm (ty-closed-natural (GStream A)) es))
