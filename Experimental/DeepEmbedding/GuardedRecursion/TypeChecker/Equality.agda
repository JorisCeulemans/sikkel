--------------------------------------------------
-- Checking equality for mode, modality and type expressions.
--------------------------------------------------

module Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Equality where

open import Data.String
open import Relation.Binary.PropositionalEquality

open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Syntax
open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Monad

private
  variable
    m m' : ModeExpr


_≟mode_ : (m1 m2 : ModeExpr) → TCM (m1 ≡ m2)
e-★ ≟mode e-★ = return refl
e-ω ≟mode e-ω = return refl
m ≟mode m' = type-error ("Mode " ++ show-mode m ++ " is not equal to " ++ show-mode m')

_≟modality_ : (μ ρ : ModalityExpr m m') → TCM (μ ≡ ρ)
e-𝟙 ≟modality e-𝟙 = return refl
e-timeless ≟modality e-timeless = return refl
e-allnow ≟modality e-allnow = return refl
e-later ≟modality e-later = return refl
μ ≟modality ρ = type-error ("Modality " ++ show-modality μ ++ " is not equal to " ++ show-modality ρ)

_≟ty_ : (T1 T2 : TyExpr m) → TCM (T1 ≡ T2)
e-Nat ≟ty e-Nat = return refl
e-Bool ≟ty e-Bool = return refl
(T1 e→ T2) ≟ty (T3 e→ T4) = do
  refl ← T1 ≟ty T3
  refl ← T2 ≟ty T4
  return refl
(T1 e-⊠ T2) ≟ty (T3 e-⊠ T4) = do
  refl ← T1 ≟ty T3
  refl ← T2 ≟ty T4
  return refl
(e-mod {m1} μ1 T1) ≟ty (e-mod {m2} μ2 T2) = do
  refl ← m1 ≟mode m2
  refl ← μ1 ≟modality μ2
  refl ← T1 ≟ty T2
  return refl
(e-▻' T) ≟ty (e-▻' S) = map (cong e-▻') (T ≟ty S)
(e-GStream T) ≟ty (e-GStream S) = map (cong e-GStream) (T ≟ty S)
T ≟ty S = type-error ("Type " ++ show-type T ++ " is not equal to " ++ show-type S)
