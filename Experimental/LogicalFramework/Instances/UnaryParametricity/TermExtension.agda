--------------------------------------------------
-- Specification of new term constructors for parametricity
--------------------------------------------------

module Experimental.LogicalFramework.Instances.UnaryParametricity.TermExtension where

open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Unit
open import Relation.Binary.PropositionalEquality as Ag
open import Relation.Unary

import Model.CwF-Structure as M
import Model.Type.Function as M
open import Model.DRA as DRA

import Applications.UnaryParametricity.Model as M

open import Experimental.LogicalFramework.Proof.CheckingMonad

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
import Experimental.LogicalFramework.Instances.UnaryParametricity.ModeTheory as UPMT
open UPMT using (unary-param-mt; ↑)
open ModeTheory unary-param-mt
open import Experimental.LogicalFramework.Instances.UnaryParametricity.TypeExtension

open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension unary-param-mt unary-param-ty-ext
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionSemantics unary-param-mt unary-param-ty-ext
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtensionNormalization unary-param-mt unary-param-ty-ext

open import Experimental.LogicalFramework.MSTT.Syntax.Types unary-param-mt unary-param-ty-ext
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts unary-param-mt unary-param-ty-ext
open import Experimental.LogicalFramework.MSTT.Interpretation.TypeContext unary-param-mt unary-param-ty-ext

private variable
  m n : Mode


private
  BinaryBool : Ty ↑
  BinaryBool = Ext BinaryBool-code tt

data TmExtCode : Mode → Set where
  true-code false-code and-code not-code : TmExtCode ↑

_≟tm-code_ : (c1 c2 : TmExtCode m) → PCM (c1 ≡ c2)
true-code ≟tm-code true-code = return refl
false-code ≟tm-code false-code = return refl
and-code ≟tm-code and-code = return refl
not-code ≟tm-code not-code = return refl
c1 ≟tm-code c2 = throw-error "Terms are not equal."

tm-code-ty : TmExtCode m → Ty m
tm-code-ty true-code = BinaryBool
tm-code-ty false-code = BinaryBool
tm-code-ty and-code = BinaryBool ⇛ BinaryBool ⇛ BinaryBool
tm-code-ty not-code = BinaryBool ⇛ BinaryBool

tm-code-arginfos : TmExtCode m → List (TmArgInfo m)
tm-code-arginfos true-code = []
tm-code-arginfos false-code = []
tm-code-arginfos and-code = []
tm-code-arginfos not-code = []

unary-param-tm-ext : TmExt
TmExt.TmExtCode unary-param-tm-ext = TmExtCode
TmExt._≟tm-code_ unary-param-tm-ext = _≟tm-code_
TmExt.tm-code-ty unary-param-tm-ext = tm-code-ty
TmExt.tm-code-arginfos unary-param-tm-ext = tm-code-arginfos


⟦_⟧tm-code : (c : TmExtCode m) → SemTmConstructor (tm-code-arginfos c) (tm-code-ty c)
⟦ true-code ⟧tm-code = M.from-pred 1 M.1-bit
⟦ false-code ⟧tm-code = M.from-pred 0 M.0-bit
⟦ and-code ⟧tm-code = M.lamcl (ty-closed-natural (BinaryBool ⇛ BinaryBool)) (M.lamcl (ty-closed-natural BinaryBool)
                              (M.from-pred2 _⊓_ M.⊓-preserves-bitness))
⟦ not-code ⟧tm-code = M.lamcl (ty-closed-natural BinaryBool) (M.from-pred1 (1 ∸_) M.1∸-preserves-bitness)

⟦⟧tm-code-natural : (c : TmExtCode m) → SemTmConstructorNatural ⟦ c ⟧tm-code
⟦⟧tm-code-natural true-code σ = M.from-pred-tm-natural σ
⟦⟧tm-code-natural false-code σ = M.from-pred-tm-natural σ
⟦⟧tm-code-natural and-code σ =
  M.transᵗᵐ (M.transᵗᵐ (M.cl-tm-subst-cong-tm (ty-closed-natural (BinaryBool ⇛ BinaryBool ⇛ BinaryBool)) (
              M.lamcl-cong-cl {A = M.BinaryBool} (M.fun-closed-congᶜⁿ (𝟙-preserves-cl (ty-closed-natural BinaryBool)) (M.reflᶜⁿ (ty-closed-natural BinaryBool)))
                                                 (M.lamcl M.frompred-natural (M.from-pred2 _⊓_ M.⊓-preserves-bitness)))) (
            M.cl-tm-subst-cong-cl (M.fun-closed-congᶜⁿ (DRA.𝟙-preserves-cl M.frompred-natural)
                                  (M.fun-closed-congᶜⁿ (DRA.𝟙-preserves-cl M.frompred-natural) (M.reflᶜⁿ M.frompred-natural))))) (
  M.transᵗᵐ (M.from-pred2-tm-natural _⊓_ M.⊓-preserves-bitness σ)
  (M.symᵗᵐ (M.lamcl-cong-cl {A = M.BinaryBool} (M.fun-closed-congᶜⁿ (𝟙-preserves-cl (ty-closed-natural BinaryBool)) (M.reflᶜⁿ (ty-closed-natural BinaryBool)))
                                               (M.lamcl M.frompred-natural (M.from-pred2 _⊓_ M.⊓-preserves-bitness)))))
⟦⟧tm-code-natural not-code σ =
  M.transᵗᵐ (M.cl-tm-subst-cong-cl (M.fun-closed-congᶜⁿ (DRA.𝟙-preserves-cl M.frompred-natural) (M.reflᶜⁿ M.frompred-natural))) (
  M.from-pred1-tm-natural (1 ∸_) M.1∸-preserves-bitness σ)

⟦⟧tm-code-cong : (c : TmExtCode m) → SemTmConstructorCong ⟦ c ⟧tm-code
⟦⟧tm-code-cong true-code = M.reflᵗᵐ
⟦⟧tm-code-cong false-code = M.reflᵗᵐ
⟦⟧tm-code-cong and-code = M.reflᵗᵐ
⟦⟧tm-code-cong not-code = M.reflᵗᵐ

unary-param-tm-ext-sem : TmExtSem unary-param-tm-ext
TmExtSem.⟦_⟧tm-code unary-param-tm-ext-sem c = ⟦ c ⟧tm-code
TmExtSem.⟦⟧tm-code-natural unary-param-tm-ext-sem = ⟦⟧tm-code-natural
TmExtSem.⟦⟧tm-code-cong unary-param-tm-ext-sem = ⟦⟧tm-code-cong


open import Experimental.LogicalFramework.MSTT.Syntax.Terms unary-param-mt unary-param-ty-ext unary-param-tm-ext

unary-param-tm-ext-norm : TmExtNormalization unary-param-tm-ext unary-param-tm-ext-sem
TmExtNormalization.normalize-tm-code unary-param-tm-ext-norm _ c {bound-names} tmargs =
  just (normres (ext c bound-names tmargs Ag.refl) M.reflᵗᵐ)
