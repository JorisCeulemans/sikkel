module Experimental.LogicalFramework.Instances.GuardedRecursion.TermExtension where

open import Data.List
open import Data.Maybe as Maybe
open import Data.Product using (_,_)
import Data.String as Str
open import Data.Unit
open import Relation.Binary.PropositionalEquality as Ag

import Model.CwF-Structure as M
import Model.Type.Function as M
open import Model.DRA as DRA
  using (dra-intro; dra-intro-cl-natural; dra-intro-cong)
import Applications.GuardedRecursion.Model.Streams.Guarded as M
import Applications.GuardedRecursion.Model.Modalities as M
import Applications.GuardedRecursion.Model.Lob as M

open import Experimental.LogicalFramework.Proof.CheckingMonad

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
import Experimental.LogicalFramework.Instances.GuardedRecursion.ModeTheory as GMT
open GMT using (guarded-mt; ω; constantly; later; forever)
open ModeTheory guarded-mt
open import Experimental.LogicalFramework.Instances.GuardedRecursion.TypeExtension

open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension guarded-mt guarded-ty-ext
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics guarded-mt guarded-ty-ext

open import Experimental.LogicalFramework.MSTT.Syntax.Types guarded-mt guarded-ty-ext
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts guarded-mt guarded-ty-ext
open import Experimental.LogicalFramework.MSTT.Interpretation.TypeContext guarded-mt guarded-ty-ext

private variable
  m n : Mode


private
  GStream : Ty ★ → Ty ω
  GStream A = Ext GStream-code (A , tt)

data TmExtCode : Mode → Set where
  löb-code : Ty ω → TmExtCode ω
  g-cons-code g-head-code g-tail-code : Ty ★ → TmExtCode ω

_≟tm-code_ : (c1 c2 : TmExtCode m) → PCM (c1 ≡ c2)
löb-code A ≟tm-code löb-code B =
  cong löb-code <$> (A ≟ty B)
g-cons-code A ≟tm-code g-cons-code B = cong g-cons-code <$> (A ≟ty B)
g-head-code A ≟tm-code g-head-code B = cong g-head-code <$> (A ≟ty B)
g-tail-code A ≟tm-code g-tail-code B = cong g-tail-code <$> (A ≟ty B)
_ ≟tm-code _ = throw-error "term codes are not equal"

tm-code-ty : TmExtCode m → Ty m
tm-code-ty (löb-code A) = A
tm-code-ty (g-cons-code A) = GStream A
tm-code-ty (g-head-code A) = ⟨ constantly ∣ A ⟩
tm-code-ty (g-tail-code A) = ⟨ later ∣ GStream A ⟩

tm-code-arginfos : TmExtCode m → List (TmArgInfo m)
tm-code-arginfos (löb-code A) = tmarg-info (◇ ,, later ∣ A) A ∷ []
tm-code-arginfos (g-cons-code A) =
  tmarg-info (◇ ,lock⟨ constantly ⟩) A ∷
  tmarg-info (◇ ,lock⟨ later ⟩) (GStream A) ∷
  []
tm-code-arginfos (g-head-code A) = tmarg-info ◇ (GStream A) ∷ []
tm-code-arginfos (g-tail-code A) = tmarg-info ◇ (GStream A) ∷ []

guarded-tm-ext : TmExt
TmExt.TmExtCode guarded-tm-ext = TmExtCode
TmExt._≟tm-code_ guarded-tm-ext = _≟tm-code_
TmExt.tm-code-ty guarded-tm-ext = tm-code-ty
TmExt.tm-code-arginfos guarded-tm-ext = tm-code-arginfos


⟦_⟧tm-code : (c : TmExtCode m) → SemTmConstructor (tm-code-arginfos c) (tm-code-ty c)
⟦ löb-code A    ⟧tm-code = λ a → M.löb-cl (ty-closed-natural A) a
⟦ g-cons-code A ⟧tm-code = λ h t → M.g-cl-cons (ty-closed-natural A) (dra-intro ⟦ constantly ⟧mod h) (dra-intro ⟦ later ⟧mod t)
⟦ g-head-code A ⟧tm-code = λ s → M.g-head s
⟦ g-tail-code A ⟧tm-code = λ s → M.g-cl-tail (ty-closed-natural A) s

⟦⟧tm-code-natural : (c : TmExtCode m) → SemTmConstructorNatural ⟦ c ⟧tm-code
⟦⟧tm-code-natural (löb-code A) σ a = M.löb-cl-natural (ty-closed-natural A) a σ
⟦⟧tm-code-natural (g-cons-code A) σ h t =
  M.transᵗᵐ (M.g-cons-cl-natural (ty-closed-natural A) σ)
            (M.g-cl-cons-cong (ty-closed-natural A)
                              (dra-intro-cl-natural ⟦ constantly ⟧mod (ty-closed-natural A) h)
                              (dra-intro-cl-natural ⟦ later ⟧mod (ty-closed-natural (GStream A)) t))
⟦⟧tm-code-natural (g-head-code A) σ s = M.g-head-cl-natural (ty-closed-natural A) σ
⟦⟧tm-code-natural (g-tail-code A) σ s = M.g-tail-cl-natural (ty-closed-natural A) σ

⟦⟧tm-code-cong : (c : TmExtCode m) → SemTmConstructorCong ⟦ c ⟧tm-code
⟦⟧tm-code-cong (löb-code A) = M.löb-cl-cong (ty-closed-natural A)
⟦⟧tm-code-cong (g-cons-code A) eh et =
  M.g-cl-cons-cong (ty-closed-natural A) (dra-intro-cong ⟦ constantly ⟧mod eh) (dra-intro-cong ⟦ later ⟧mod et)
⟦⟧tm-code-cong (g-head-code A) = M.g-head-cong
⟦⟧tm-code-cong (g-tail-code A) = M.g-cl-tail-cong (ty-closed-natural A)

guarded-tm-ext-sem : TmExtSem guarded-tm-ext
TmExtSem.⟦_⟧tm-code guarded-tm-ext-sem c = ⟦ c ⟧tm-code
TmExtSem.⟦⟧tm-code-natural guarded-tm-ext-sem = ⟦⟧tm-code-natural
TmExtSem.⟦⟧tm-code-cong guarded-tm-ext-sem = ⟦⟧tm-code-cong
