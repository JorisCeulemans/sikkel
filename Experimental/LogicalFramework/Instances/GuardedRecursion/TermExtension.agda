module Experimental.LogicalFramework.Instances.GuardedRecursion.TermExtension where

open import Data.List
open import Data.Product using (_,_)
open import Data.String as Str
open import Data.Unit
open import Relation.Binary.PropositionalEquality

import Model.CwF-Structure as M
import Model.Type.Function as M
import Model.Modality as M
import Applications.GuardedRecursion.Model.Streams.Guarded as M
import Applications.GuardedRecursion.Model.Modalities as M

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics
open import Experimental.LogicalFramework.MSTT.AlphaEquivalence.TermExtension

open import Experimental.LogicalFramework.Proof.CheckingMonad

import Experimental.LogicalFramework.Instances.GuardedRecursion.ModeTheory as GMT
open GMT using (guarded-mt; ω; ★; constantly; later; forever)
open ModeTheory guarded-mt
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TypeExtension

open import Experimental.LogicalFramework.MSTT.Syntax.Types guarded-mt guarded-ty-ext
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts guarded-mt guarded-ty-ext
open import Experimental.LogicalFramework.MSTT.Interpretation.TypeContext guarded-mt guarded-ty-ext

private variable
  m n : Mode


private
  GStream : Ty ★ → Ty ω
  GStream A = Ext GStream-code (A , tt)

data TmExtCode : Mode → Set where
  löb-code : String → Ty ω → TmExtCode ω
  g-cons-code g-head-code g-tail-code : Ty ★ → TmExtCode ω

_≟tm-code_ : (c1 c2 : TmExtCode m) → PCM (c1 ≡ c2)
löb-code x A ≟tm-code löb-code y B =
  cong₂ löb-code <$> from-dec "term codes are not equal" (x Str.≟ y) <*> (A ≟ty B)
g-cons-code A ≟tm-code g-cons-code B = cong g-cons-code <$> (A ≟ty B)
g-head-code A ≟tm-code g-head-code B = cong g-head-code <$> (A ≟ty B)
g-tail-code A ≟tm-code g-tail-code B = cong g-tail-code <$> (A ≟ty B)
_ ≟tm-code _ = throw-error "term codes are not equal"

tm-code-ty : TmExtCode m → Ty m
tm-code-ty (löb-code x A) = A
tm-code-ty (g-cons-code A) = GStream A
tm-code-ty (g-head-code A) = ⟨ constantly ∣ A ⟩
tm-code-ty (g-tail-code A) = ⟨ later ∣ GStream A ⟩

tm-code-arginfos : TmExtCode m → List (TmArgInfo guarded-mt guarded-ty-ext String m)
tm-code-arginfos (löb-code x A) = tmarginfo (◇ ,, later ∣ x ∈ A) A ∷ []
tm-code-arginfos (g-cons-code A) =
  tmarginfo (◇ ,lock⟨ constantly ⟩) A ∷
  tmarginfo (◇ ,lock⟨ later ⟩) (GStream A) ∷
  []
tm-code-arginfos (g-head-code A) = tmarginfo ◇ (GStream A) ∷ []
tm-code-arginfos (g-tail-code A) = tmarginfo ◇ (GStream A) ∷ []

guarded-tm-ext : TmExt guarded-mt guarded-ty-ext String
TmExt.TmExtCode guarded-tm-ext = TmExtCode
TmExt._≟tm-code_ guarded-tm-ext = _≟tm-code_
TmExt.tm-code-ty guarded-tm-ext = tm-code-ty
TmExt.tm-code-arginfos guarded-tm-ext = tm-code-arginfos


guarded-tm-ext-sem : TmExtSem guarded-mt guarded-ty-ext (erase-names-tmext guarded-mt guarded-ty-ext guarded-tm-ext)
TmExtSem.⟦_⟧tm-code guarded-tm-ext-sem (löb-code x A) =
  λ t → M.löb' ⟦ A ⟧ty (M.ι[ M.transᵗʸ (ty-natural A) (M.symᵗʸ (ty-natural A)) ]
                         (M.ιc[ M.,,-cong (M.▻-cong (ty-natural A)) ]' t))
TmExtSem.⟦_⟧tm-code guarded-tm-ext-sem (g-cons-code A) =
  λ h t → M.app (M.app M.g-cons (M.mod-intro ⟦ constantly ⟧mod h))
                (M.ι[ M.▻-cong (ty-natural (GStream A)) ] M.mod-intro ⟦ later ⟧mod t)
TmExtSem.⟦_⟧tm-code guarded-tm-ext-sem (g-head-code A) =
  λ s → M.app M.g-head s
TmExtSem.⟦_⟧tm-code guarded-tm-ext-sem (g-tail-code A) =
  λ s → M.ι⁻¹[ M.▻-cong (ty-natural (GStream A)) ] M.app M.g-tail s
