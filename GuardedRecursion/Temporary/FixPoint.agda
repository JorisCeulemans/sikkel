-- This file contains the contents of the module Induction.WellFounded.Fixpoint
-- in the standard library (v1.3). The only difference is that _<_ is in Rel A r
-- instead of Rel A ℓ (same level as P). This should be fixed in the next release
-- of the std-lib.

open import Relation.Binary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality
open import Induction.WellFounded

module GuardedRecursion.Temporary.FixPoint
  {r ℓ ℓ' : _}{A : Set ℓ'}
  {_<_ : Rel A r} (wf : WellFounded _<_)
  (P : Pred A ℓ) (f : WfRec _<_ P ⊆′ P)
  (f-ext : (x : A) {IH IH' : WfRec _<_ P x} → (∀ {y} y<x → IH y y<x ≡ IH' y y<x) → f x IH ≡ f x IH')
  where

  some-wfRec-irrelevant : ∀ x → (q q' : Acc _<_ x) → Some.wfRec P f x q ≡ Some.wfRec P f x q'
  some-wfRec-irrelevant = All.wfRec wf _
                                   (λ x → (q q' : Acc _<_ x) → Some.wfRec P f x q ≡ Some.wfRec P f x q')
                                   (λ { x IH (acc rs) (acc rs') → f-ext x (λ y<x → IH _ y<x (rs _ y<x) (rs' _ y<x)) })

  open All wf ℓ
  wfRecBuilder-wfRec : ∀ {x y} y<x → wfRecBuilder P f x y y<x ≡ wfRec P f y
  wfRecBuilder-wfRec {x} {y} y<x with wf x
  ... | acc rs = some-wfRec-irrelevant y (rs y y<x) (wf y)

  unfold-wfRec : ∀ {x} → wfRec P f x ≡ f x (λ y _ → wfRec P f y)
  unfold-wfRec {x} = f-ext x wfRecBuilder-wfRec
