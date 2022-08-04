--------------------------------------------------
-- Definition of α-equivalence of STT terms via a translation to nameless terms
--------------------------------------------------

module Experimental.LogicalFramework.STT.AlphaEquivalence where

open import Data.String
open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.STT.Syntax.Named
import Experimental.LogicalFramework.STT.Syntax.Nameless as NMLS

private variable
  Γ : CtxExpr
  T : TyExpr
  x : String


erase-names-ctx : CtxExpr → NMLS.CtxExpr
erase-names-ctx ◇ = NMLS.◇
erase-names-ctx (Γ ,, x ∈ T) = erase-names-ctx Γ NMLS.,, _ ∈ T

erase-names-var : Var x Γ T → NMLS.Var _ (erase-names-ctx Γ) T
erase-names-var vzero = NMLS.vzero
erase-names-var (vsuc v) = NMLS.vsuc (erase-names-var v)

erase-names-tm : TmExpr Γ T → NMLS.TmExpr (erase-names-ctx Γ) T
erase-names-tm (var' x {v}) = NMLS.var' _ {erase-names-var v}
erase-names-tm (lam[ x ∈ T ] t) = NMLS.lam[ _ ∈ T ] erase-names-tm t
erase-names-tm (f ∙ t) = (erase-names-tm f) NMLS.∙ (erase-names-tm t)
erase-names-tm zero = NMLS.zero
erase-names-tm suc = NMLS.suc
erase-names-tm (nat-elim a f) = NMLS.nat-elim (erase-names-tm a) (erase-names-tm f)
erase-names-tm true = NMLS.true
erase-names-tm false = NMLS.false
erase-names-tm (if b t f) = NMLS.if (erase-names-tm b) (erase-names-tm t) (erase-names-tm f)
erase-names-tm (pair t s) = NMLS.pair (erase-names-tm t) (erase-names-tm s)
erase-names-tm (fst p) = NMLS.fst (erase-names-tm p)
erase-names-tm (snd p) = NMLS.snd (erase-names-tm p)

infix 2 _≈α_
_≈α_ : (t s : TmExpr Γ T) → Set
t ≈α s = erase-names-tm t ≡ erase-names-tm s
