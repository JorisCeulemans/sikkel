module Experimental.LogicalFramework.Instances.UnaryParametricity.bPropExtension where

open import Data.List
open import Data.Product renaming (_,_ to [_,_]) hiding (Σ)
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding (refl)

import Model.BaseCategory as M
import Model.CwF-Structure as M
import Model.DRA as DRA

import Applications.UnaryParametricity.Model as M

open import Experimental.LogicalFramework.Instances.UnaryParametricity.MSTT
open import Experimental.LogicalFramework.Instances.UnaryParametricity.TypeExtension
open import Experimental.LogicalFramework.Instances.UnaryParametricity.TermExtension

open import Experimental.LogicalFramework.Parameter.ArgInfo unary-param-mt unary-param-ty-ext
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension unary-param-mt unary-param-ty-ext
open import Experimental.LogicalFramework.Parameter.bPropExtension unary-param-mt unary-param-ty-ext unary-param-tm-ext
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics unary-param-mt unary-param-ty-ext unary-param-tm-ext

open import Experimental.LogicalFramework.Proof.CheckingMonad

private variable
  m n : Mode


data bPropExtCode : Mode → Set where
  bPred-code : (A : Ty ↑) → bPropExtCode ★

_≟bp-code_ : (c1 c2 : bPropExtCode m) → PCM (c1 ≡ c2)
(bPred-code A) ≟bp-code (bPred-code B) = do
  refl ← A ≟ty B
  return refl

bp-code-tmarg-infos : bPropExtCode m → List (TmArgInfo m)
bp-code-tmarg-infos (bPred-code A) = tmarg-info ◇ ⟨ forget ∣ A ⟩ ∷ []

bp-code-bparg-infos : bPropExtCode m → List (ArgInfo m)
bp-code-bparg-infos (bPred-code A) = []

unary-param-bp-ext : bPropExt
bPropExt.bPropExtCode unary-param-bp-ext = bPropExtCode
bPropExt._≟bp-code_ unary-param-bp-ext = _≟bp-code_
bPropExt.bp-code-tmarg-infos unary-param-bp-ext = bp-code-tmarg-infos
bPropExt.bp-code-bparg-infos unary-param-bp-ext = bp-code-bparg-infos


⟦_⟧bp-code : (c : bPropExtCode m) → SemPropConstructor (bp-code-tmarg-infos c) (bp-code-bparg-infos c)
⟦ bPred-code A ⟧bp-code = M.semPred (ty-closed-natural A)

⟦⟧bp-code-natural : (c : bPropExtCode m) → SemPropConstructorNatural ⟦ c ⟧bp-code
⟦⟧bp-code-natural (bPred-code A) = M.semPred-natural (ty-closed-natural A)

⟦⟧bp-code-cong : (c : bPropExtCode m) → SemPropConstructorCong ⟦ c ⟧bp-code
⟦⟧bp-code-cong (bPred-code A) = M.semPred-cong (ty-closed-natural A)

unary-param-bp-ext-sem : bPropExtSem unary-param-bp-ext
bPropExtSem.⟦_⟧bp-code unary-param-bp-ext-sem = ⟦_⟧bp-code
bPropExtSem.⟦⟧bp-code-natural unary-param-bp-ext-sem = ⟦⟧bp-code-natural
bPropExtSem.⟦⟧bp-code-cong unary-param-bp-ext-sem = ⟦⟧bp-code-cong
