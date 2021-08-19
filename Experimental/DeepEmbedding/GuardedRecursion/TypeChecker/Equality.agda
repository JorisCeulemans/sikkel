--------------------------------------------------
-- Checking equality for mode, modality and type expressions.
--------------------------------------------------

module Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Equality where

open import Data.String
open import Relation.Binary.PropositionalEquality

open import Modalities
open import GuardedRecursion.Modalities using (later; timeless; allnow; allnow-timeless; allnow-later)

open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Syntax
open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Monad
open import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.TypeInterpretation

private
  variable
    m m' m'' : ModeExpr


--------------------------------------------------
-- (Semi-)decidable equality for mode, modality and type expressions
--   Requiring modalities and types to be truly identical is too restrictive,
--   therefore we have the decision procedures further below which allow for
--   more definitional equalities.

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
(T1 e→ T2) ≟ty (T3 e→ T4) = (cong₂ _e→_) <$> (T1 ≟ty T3) ⊛ (T2 ≟ty T4)
(T1 e-⊠ T2) ≟ty (T3 e-⊠ T4) = (cong₂ _e-⊠_) <$> (T1 ≟ty T3) ⊛ (T2 ≟ty T4)
(e-mod {m1} μ1 T1) ≟ty (e-mod {m2} μ2 T2) = do
  refl ← m1 ≟mode m2
  cong₂ e-mod <$> (μ1 ≟modality μ2) ⊛ (T1 ≟ty T2)
(e-▻' T) ≟ty (e-▻' S) = (cong e-▻') <$> (T ≟ty S)
(e-GStream T) ≟ty (e-GStream S) = (cong e-GStream) <$> (T ≟ty S)
T ≟ty S = type-error ("Type " ++ show-type T ++ " is not equal to " ++ show-type S)


--------------------------------------------------
-- Deciding whether two modalities' interpretations are equivalent

-- The decision procedure has two steps:
--   1. A possibly tree-like structure caused by multiple applications of modality
--      composition is flattened to a list-like structure. This is similar to a
--      standard monoid solver.
--   2. The list-like structure is reduced making use of specific equalities in the
--      mode theory such as `allnow ⓜ later ≅ᵐ allnow`.

-- A value of type S(imple)ModalityExpr represents a modality expression that does
-- not include composition.
data SModalityExpr : ModeExpr → ModeExpr → Set where
  se-timeless : SModalityExpr e-★ e-ω
  se-allnow : SModalityExpr e-ω e-★
  se-later : SModalityExpr e-ω e-ω

interpret-smod-expr : SModalityExpr m m' → ModalityExpr m m'
interpret-smod-expr se-timeless = e-timeless
interpret-smod-expr se-allnow = e-allnow
interpret-smod-expr se-later = e-later

⟦_⟧smod : SModalityExpr m m' → Modality ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ μ ⟧smod = ⟦ interpret-smod-expr μ ⟧modality

data SModalitySequence : ModeExpr → ModeExpr → Set where
  [] : SModalitySequence m m
  _∷_ : SModalityExpr m'' m' → SModalitySequence m m'' → SModalitySequence m m'

interpret-smod-sequence : SModalitySequence m m' → ModalityExpr m m'
interpret-smod-sequence [] = e-𝟙
interpret-smod-sequence (μ ∷ μs) = interpret-smod-expr μ e-ⓜ interpret-smod-sequence μs

⟦_⟧smod-seq : SModalitySequence m m' → Modality ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ μs ⟧smod-seq = ⟦ interpret-smod-sequence μs ⟧modality

-- Step 1: flattening a modality to a sequence of simple modalities.
_s++_ : SModalitySequence m'' m' → SModalitySequence m m'' → SModalitySequence m m'
[] s++ ρs = ρs
(μ ∷ μs) s++ ρs = μ ∷ (μs s++ ρs)

flatten : ModalityExpr m m' → SModalitySequence m m'
flatten e-𝟙 = []
flatten (μ e-ⓜ ρ) = flatten μ s++ flatten ρ
flatten e-timeless = se-timeless ∷ []
flatten e-allnow = se-allnow ∷ []
flatten e-later = se-later ∷ []

s++-sound : (μs : SModalitySequence m'' m') (ρs : SModalitySequence m m'') →
            ⟦ μs s++ ρs ⟧smod-seq ≅ᵐ ⟦ μs ⟧smod-seq ⓜ ⟦ ρs ⟧smod-seq
s++-sound [] ρs = ≅ᵐ-sym (𝟙-identityˡ _)
s++-sound (μ ∷ μs) ρs = begin
  ⟦ μ ⟧smod ⓜ ⟦ μs s++ ρs ⟧smod-seq
    ≅⟨ ⓜ-congˡ ⟦ μ ⟧smod (s++-sound μs ρs) ⟩
  ⟦ μ ⟧smod ⓜ (⟦ μs ⟧smod-seq ⓜ ⟦ ρs ⟧smod-seq)
    ≅˘⟨ ⓜ-assoc ⟦ μ ⟧smod ⟦ μs ⟧smod-seq ⟦ ρs ⟧smod-seq ⟩
  (⟦ μ ⟧smod ⓜ ⟦ μs ⟧smod-seq) ⓜ ⟦ ρs ⟧smod-seq ∎
  where open ≅ᵐ-Reasoning

flatten-sound : (μ : ModalityExpr m m') → ⟦ flatten μ ⟧smod-seq ≅ᵐ ⟦ μ ⟧modality
flatten-sound e-𝟙 = ≅ᵐ-refl
flatten-sound (μ e-ⓜ ρ) = begin
  ⟦ flatten μ s++ flatten ρ ⟧smod-seq
    ≅⟨ s++-sound (flatten μ) (flatten ρ) ⟩
  ⟦ flatten μ ⟧smod-seq ⓜ ⟦ flatten ρ ⟧smod-seq
    ≅⟨ ⓜ-congʳ ⟦ flatten ρ ⟧smod-seq (flatten-sound μ) ⟩
  ⟦ μ ⟧modality ⓜ ⟦ flatten ρ ⟧smod-seq
    ≅⟨ ⓜ-congˡ ⟦ μ ⟧modality (flatten-sound ρ) ⟩
  ⟦ μ ⟧modality ⓜ ⟦ ρ ⟧modality ∎
  where open ≅ᵐ-Reasoning
flatten-sound e-timeless = 𝟙-identityʳ timeless
flatten-sound e-allnow = 𝟙-identityʳ allnow
flatten-sound e-later = 𝟙-identityʳ later

-- Step 2: reducing the sequence using specific equalities
reduce-smod-seq-cons : SModalityExpr m'' m' → SModalitySequence m m'' → SModalitySequence m m'
reduce-smod-seq-cons se-allnow (se-timeless ∷ μs) = μs
reduce-smod-seq-cons se-allnow (se-later    ∷ μs) = reduce-smod-seq-cons se-allnow μs
reduce-smod-seq-cons μ         μs = μ ∷ μs

reduce-smod-seq : SModalitySequence m m' → SModalitySequence m m'
reduce-smod-seq [] = []
reduce-smod-seq (μ ∷ μs) = reduce-smod-seq-cons μ (reduce-smod-seq μs)

reduce-smod-seq-cons-sound : (μ : SModalityExpr m'' m') (μs : SModalitySequence m m'') →
                             ⟦ reduce-smod-seq-cons μ μs ⟧smod-seq ≅ᵐ ⟦ μ ⟧smod ⓜ ⟦ μs ⟧smod-seq
reduce-smod-seq-cons-sound se-allnow (se-timeless ∷ μs) = begin
  ⟦ μs ⟧smod-seq
    ≅˘⟨ 𝟙-identityˡ ⟦ μs ⟧smod-seq ⟩
  𝟙 ⓜ ⟦ μs ⟧smod-seq
    ≅˘⟨ ⓜ-congʳ ⟦ μs ⟧smod-seq allnow-timeless ⟩
  (allnow ⓜ timeless) ⓜ ⟦ μs ⟧smod-seq
    ≅⟨ ⓜ-assoc _ _ _ ⟩
  allnow ⓜ (timeless ⓜ ⟦ μs ⟧smod-seq) ∎
  where open ≅ᵐ-Reasoning
reduce-smod-seq-cons-sound se-allnow (se-later    ∷ μs) = begin
  ⟦ reduce-smod-seq-cons se-allnow μs ⟧smod-seq
    ≅⟨ reduce-smod-seq-cons-sound se-allnow μs ⟩
  allnow ⓜ ⟦ μs ⟧smod-seq
    ≅˘⟨ ⓜ-congʳ ⟦ μs ⟧smod-seq allnow-later ⟩
  (allnow ⓜ later) ⓜ ⟦ μs ⟧smod-seq
    ≅⟨ ⓜ-assoc _ _ _ ⟩
  allnow ⓜ (later ⓜ ⟦ μs ⟧smod-seq) ∎
  where open ≅ᵐ-Reasoning
reduce-smod-seq-cons-sound se-allnow [] = ≅ᵐ-refl
reduce-smod-seq-cons-sound se-timeless μs = ≅ᵐ-refl
reduce-smod-seq-cons-sound se-later μs = ≅ᵐ-refl

reduce-smod-seq-sound : (μs : SModalitySequence m m') → ⟦ reduce-smod-seq μs ⟧smod-seq ≅ᵐ ⟦ μs ⟧smod-seq
reduce-smod-seq-sound [] = ≅ᵐ-refl
reduce-smod-seq-sound (μ ∷ μs) = ≅ᵐ-trans (reduce-smod-seq-cons-sound μ (reduce-smod-seq μs))
                                          (ⓜ-congˡ ⟦ μ ⟧smod (reduce-smod-seq-sound μs))
