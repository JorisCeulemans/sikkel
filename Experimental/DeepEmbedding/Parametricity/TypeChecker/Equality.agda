--------------------------------------------------
-- Checking equality for mode, modality and type expressions.
--------------------------------------------------

open import Experimental.DeepEmbedding.Parametricity.TypeChecker.Builtin

module Experimental.DeepEmbedding.Parametricity.TypeChecker.Equality (builtin : BuiltinTypes) where

open BuiltinTypes builtin

open import Data.String
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import CwF-Structure as M hiding (◇; _,,_; var; _++_)
open import Types.Functions as M hiding (_⇛_; lam; app)
open import Types.Products as M hiding (_⊠_; pair; fst; snd)
open import Modalities as M hiding (𝟙; _ⓜ_; ⟨_∣_⟩; _,lock⟨_⟩; mod-intro; mod-elim)
open import GuardedRecursion.Modalities as M hiding (timeless; allnow; later; _⊛_; löb)
open import GuardedRecursion.Streams.Guarded as M hiding (GStream; g-cons; g-head; g-tail)

open import Experimental.DeepEmbedding.Parametricity.TypeChecker.Syntax builtin
open import Experimental.DeepEmbedding.Parametricity.TypeChecker.Monad
open import Experimental.DeepEmbedding.Parametricity.TypeChecker.TypeInterpretation builtin

private
  variable
    m m' m'' : ModeExpr


--------------------------------------------------
-- (Semi-)decidable equality for mode, modality and type expressions
--   Requiring modalities and types to be truly identical is too restrictive,
--   therefore we have the decision procedures further below which allow for
--   more definitional equalities.

_≟mode_ : (m1 m2 : ModeExpr) → TCM (m1 ≡ m2)
★ ≟mode ★ = return refl
⋀ ≟mode ⋀ = return refl
m ≟mode m' = type-error ("Mode " ++ show-mode m ++ " is not equal to " ++ show-mode m')

_≟modality_ : (μ ρ : ModalityExpr m m') → TCM (μ ≡ ρ)
𝟙 ≟modality 𝟙 = return refl
forget-left ≟modality forget-left = return refl
forget-right ≟modality forget-right = return refl
μ ≟modality ρ = type-error ("Modality " ++ show-modality μ ++ " is not equal to " ++ show-modality ρ)

⟦_⟧≅mod?⟦_⟧ : (μ ρ : ModalityExpr m m') → TCM (⟦ μ ⟧modality ≅ᵐ ⟦ ρ ⟧modality)
⟦ μ ⟧≅mod?⟦ ρ ⟧ = do
  refl ← μ ≟modality ρ
  return ≅ᵐ-refl

_≟ty_ : (T1 T2 : TyExpr m) → TCM (T1 ≡ T2)
Nat' ≟ty Nat' = return refl
Bool' ≟ty Bool' = return refl
(T1 ⇛ T2) ≟ty (T3 ⇛ T4) = (cong₂ _⇛_) <$> (T1 ≟ty T3) ⊛ (T2 ≟ty T4)
(T1 ⊠ T2) ≟ty (T3 ⊠ T4) = (cong₂ _⊠_) <$> (T1 ≟ty T3) ⊛ (T2 ≟ty T4)
(⟨_∣_⟩ {m1} μ1 T1) ≟ty (⟨_∣_⟩ {m2} μ2 T2) = do
  refl ← m1 ≟mode m2
  cong₂ ⟨_∣_⟩ <$> (μ1 ≟modality μ2) ⊛ (T1 ≟ty T2)
(Builtin c1) ≟ty (Builtin c2) = cong Builtin <$> (c1 ≟code c2)
T ≟ty S = type-error ("Type " ++ show-type T ++ " is not equal to " ++ show-type S)

⟦_⟧≅ty?⟦_⟧ : ∀ (T S : TyExpr m) {Γ} → TCM (⟦ T ⟧ty {Γ} ≅ᵗʸ ⟦ S ⟧ty)
⟦ T ⟧≅ty?⟦ S ⟧ = do
  refl ← T ≟ty S
  return ≅ᵗʸ-refl
