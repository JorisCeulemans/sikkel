--------------------------------------------------
-- Reexporting the syntax for terms in guarded recursive type theory
--   + definition of some synonyms.
--------------------------------------------------

module Applications.GuardedRecursion.MSTT.Syntax.Term where

open import Data.Product
open import Data.Unit

open import Applications.GuardedRecursion.MSTT.ModeTheory
open import Applications.GuardedRecursion.MSTT.TypeExtension
open import Applications.GuardedRecursion.MSTT.TermExtension

open import Applications.GuardedRecursion.MSTT.Syntax.Type

import MSTT.Syntax.Term GR-mode-theory GR-ty-ext GR-tm-ext as GRTerm
open GRTerm using (ext)
open GRTerm public hiding (ext)

pattern constantly-if c t f = ext constantly-if-code (c , (t , (f , tt)))

infixr 4 löb[later∣_∈_]_
pattern löb[later∣_∈_]_ x T t = ext (löb-code x T) (t , tt)

pattern g-cons a s = ext g-cons-code (a , s , tt)
pattern g-head s = ext g-head-code (s , tt)
pattern g-tail s = ext g-tail-code (s , tt)


g-cons' : TyExpr ★ → TmExpr ω
g-cons' A = lam[ constantly ∣ "h" ∈ A ] lam[ later ∣ "t" ∈ GStream A ] g-cons (svar "h") (svar "t")

g-head' : TyExpr ★ → TmExpr ω
g-head' A = lam[ "s" ∈ GStream A ] g-head (svar "s")

g-tail' : TyExpr ★ → TmExpr ω
g-tail' A = lam[ "s" ∈ GStream A ] g-tail (svar "s")
