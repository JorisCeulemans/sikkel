module Experimental.DeepEmbedding.GuardedRecursion.GuardedStreamsExamples where

open import CwF-Structure
open import Types.Functions
open import Types.Discrete
open import GuardedRecursion.Modalities
open import GuardedRecursion.Streams.Guarded

open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker


_⊛timeless_ : TmExpr e-ω → TmExpr e-ω → TmExpr e-ω
f ⊛timeless t = e-mod-intro e-timeless (e-app (e-mod-elim e-timeless f) (e-mod-elim e-timeless t))

g-map : TmExpr e-ω
g-map =
  e-lam (e-mod e-timeless (e-Nat e→ e-Nat)) (
    e-löb (e-GStreamN e→ e-GStreamN) (
      e-lam e-GStreamN (
        e-app (e-app e-cons
                     (e-var 2 ⊛timeless e-app e-head (e-var 0)))
              (e-⊛' (e-var 1) (e-app e-tail (e-var 0))))))

⟦g-map⟧sikkel : Tm ◇ (timeless-ty (Nat' ⇛ Nat') ⇛ GStream Nat' ⇛ GStream Nat')
⟦g-map⟧sikkel = ⟦ g-map ⟧tm-in e-◇

{-
g-map : {A B : ClosedType ★} → {{IsClosedNatural A}} → {{IsClosedNatural B}} →
        Tm Γ (timeless-ty (A ⇛ B) ⇛ GStream A ⇛ GStream B)
g-map {A = A}{B} =
  lamι[ "f" ∈ timeless-ty (A ⇛ B) ]
    löbι[ "m" ∈▻' (GStream A ⇛ GStream B) ]
      lamι[ "s" ∈ GStream A ]
        g-cons $ varι "f" ⊛⟨ timeless ⟩ (g-head $ varι "s")
               $ varι "m" ⊛' (g-tail $ varι "s")
-}
