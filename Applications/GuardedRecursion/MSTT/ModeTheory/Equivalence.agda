--------------------------------------------------
-- Checking equivalence for mode and modality expressions.
--------------------------------------------------

module Applications.GuardedRecursion.MSTT.ModeTheory.Equivalence where

open import Data.String
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import Model.DRA as DRA hiding (𝟙; ⟨_∣_⟩)
open import Applications.GuardedRecursion.Model.Modalities as M hiding (constantly; forever; later)

open import MSTT.TCMonad
open import Applications.GuardedRecursion.MSTT.ModeTheory.Expressions

private
  variable
    m m' m'' : ModeExpr


--------------------------------------------------
-- (Semi-)decidable equality for mode and modality expressions
--   The operation _≟modality_ tests whether two modalities are truly identical,
--   the more expressive test _≃ᵐ?_ for equivalence is implemented below.

_≟mode_ : (m1 m2 : ModeExpr) → TCM (m1 ≡ m2)
★ ≟mode ★ = return refl
ω ≟mode ω = return refl
m ≟mode m' = type-error ("Mode " ++ show-mode m ++ " is not equal to " ++ show-mode m')

_≟modality_ : (μ ρ : ModalityExpr m m') → TCM (μ ≡ ρ)
𝟙 ≟modality 𝟙 = return refl
constantly ≟modality constantly = return refl
forever ≟modality forever = return refl
later ≟modality later = return refl
(_ⓜ_ {m} μ ρ) ≟modality (_ⓜ_ {m'} μ' ρ') = do
  refl ← m ≟mode m'
  cong₂ _ⓜ_ <$> (μ ≟modality μ') ⊛ (ρ ≟modality ρ')
μ ≟modality ρ = type-error ("Modality " ++ show-modality μ ++ " is not equal to " ++ show-modality ρ)


--------------------------------------------------
-- Deciding whether two modalities are equivalent

-- The decision procedure has two steps:
--   1. A possibly tree-like structure caused by multiple applications of modality
--      composition is flattened to a list-like structure. This is similar to a
--      standard monoid solver.
--   2. The list-like structure is reduced making use of specific equalities in the
--      mode theory such as `forever ⓜ later ≅ᵐ forever`.

-- A value of type S(imple)ModalityExpr represents a modality expression that does
-- not include composition.
data SModalityExpr : ModeExpr → ModeExpr → Set where
  s-constantly : SModalityExpr ★ ω
  s-forever : SModalityExpr ω ★
  s-later : SModalityExpr ω ω

interpret-smod-expr : SModalityExpr m m' → ModalityExpr m m'
interpret-smod-expr s-constantly = constantly
interpret-smod-expr s-forever = forever
interpret-smod-expr s-later = later

⟦_⟧smod : SModalityExpr m m' → DRA ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ μ ⟧smod = ⟦ interpret-smod-expr μ ⟧modality

data SModalitySeq : ModeExpr → ModeExpr → Set where
  [] : SModalitySeq m m
  _∷_ : SModalityExpr m'' m' → SModalitySeq m m'' → SModalitySeq m m'

interpret-smod-sequence : SModalitySeq m m' → ModalityExpr m m'
interpret-smod-sequence [] = 𝟙
interpret-smod-sequence (μ ∷ []) = interpret-smod-expr μ
interpret-smod-sequence (μ ∷ μs@(_ ∷ _)) = interpret-smod-expr μ ⓜ interpret-smod-sequence μs

⟦_⟧smod-seq : SModalitySeq m m' → DRA ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ μs ⟧smod-seq = ⟦ interpret-smod-sequence μs ⟧modality

interpret-smod-cons : (μ : SModalityExpr m'' m') (μs : SModalitySeq m m'') →
                      ⟦ μ ∷ μs ⟧smod-seq ≅ᵈ ⟦ μ ⟧smod ⓓ ⟦ μs ⟧smod-seq
interpret-smod-cons μ [] = symᵈ (𝟙-unitʳ ⟦ μ ⟧smod)
interpret-smod-cons μ (_ ∷ μs) = reflᵈ

-- Step 1: flattening a modality to a sequence of simple modalities.
_s++_ : SModalitySeq m'' m' → SModalitySeq m m'' → SModalitySeq m m'
[] s++ ρs = ρs
(μ ∷ μs) s++ ρs = μ ∷ (μs s++ ρs)

flatten : ModalityExpr m m' → SModalitySeq m m'
flatten 𝟙 = []
flatten (μ ⓜ ρ) = flatten μ s++ flatten ρ
flatten constantly = s-constantly ∷ []
flatten forever = s-forever ∷ []
flatten later = s-later ∷ []

s++-sound : (μs : SModalitySeq m'' m') (ρs : SModalitySeq m m'') →
            ⟦ μs s++ ρs ⟧smod-seq ≅ᵈ ⟦ μs ⟧smod-seq ⓓ ⟦ ρs ⟧smod-seq
s++-sound []               ρs = symᵈ (𝟙-unitˡ _)
s++-sound (μ ∷ [])         ρs = interpret-smod-cons μ ρs
s++-sound (μ ∷ μs@(_ ∷ _)) ρs =
  transᵈ (ⓓ-congʳ ⟦ μ ⟧smod (s++-sound μs ρs))
         (symᵈ (ⓓ-assoc ⟦ μ ⟧smod ⟦ μs ⟧smod-seq ⟦ ρs ⟧smod-seq))

flatten-sound : (μ : ModalityExpr m m') → ⟦ flatten μ ⟧smod-seq ≅ᵈ ⟦ μ ⟧modality
flatten-sound 𝟙 = reflᵈ
flatten-sound (μ ⓜ ρ) =
  transᵈ (s++-sound (flatten μ) (flatten ρ)) (
  transᵈ (ⓓ-congˡ ⟦ flatten ρ ⟧smod-seq (flatten-sound μ)) (
  ⓓ-congʳ ⟦ μ ⟧modality (flatten-sound ρ)))
flatten-sound constantly = reflᵈ
flatten-sound forever = reflᵈ
flatten-sound later = reflᵈ

-- Step 2: reducing the sequence using specific equalities
reduce-smod-seq-cons : SModalityExpr m'' m' → SModalitySeq m m'' → SModalitySeq m m'
reduce-smod-seq-cons s-forever (s-constantly ∷ μs) = μs
reduce-smod-seq-cons s-forever (s-later    ∷ μs) = reduce-smod-seq-cons s-forever μs
reduce-smod-seq-cons μ         μs = μ ∷ μs

reduce-smod-seq : SModalitySeq m m' → SModalitySeq m m'
reduce-smod-seq [] = []
reduce-smod-seq (μ ∷ μs) = reduce-smod-seq-cons μ (reduce-smod-seq μs)

reduce-smod-seq-cons-sound : (μ : SModalityExpr m'' m') (μs : SModalitySeq m m'') →
                             ⟦ reduce-smod-seq-cons μ μs ⟧smod-seq ≅ᵈ ⟦ μ ⟧smod ⓓ ⟦ μs ⟧smod-seq
reduce-smod-seq-cons-sound s-forever (s-constantly ∷ μs) =
  transᵈ (symᵈ (𝟙-unitˡ ⟦ μs ⟧smod-seq)) (
  transᵈ (symᵈ (ⓓ-congˡ ⟦ μs ⟧smod-seq forever-constantly)) (
  transᵈ (ⓓ-assoc _ _ _) (
  symᵈ (ⓓ-congʳ M.forever (interpret-smod-cons s-constantly μs)))))
reduce-smod-seq-cons-sound s-forever (s-later    ∷ μs) =
  transᵈ (reduce-smod-seq-cons-sound s-forever μs) (
  transᵈ (symᵈ (ⓓ-congˡ ⟦ μs ⟧smod-seq forever-later)) (
  transᵈ (ⓓ-assoc _ _ _) (
  symᵈ (ⓓ-congʳ M.forever (interpret-smod-cons s-later μs)))))
reduce-smod-seq-cons-sound s-forever [] = symᵈ (𝟙-unitʳ _)
reduce-smod-seq-cons-sound s-constantly μs = interpret-smod-cons s-constantly μs
reduce-smod-seq-cons-sound s-later μs = interpret-smod-cons s-later μs

reduce-smod-seq-cons-empty : (μ : SModalityExpr m m') → reduce-smod-seq-cons μ [] ≡ μ ∷ []
reduce-smod-seq-cons-empty s-constantly = refl
reduce-smod-seq-cons-empty s-forever = refl
reduce-smod-seq-cons-empty s-later = refl

reduce-smod-seq-sound : (μs : SModalitySeq m m') → ⟦ reduce-smod-seq μs ⟧smod-seq ≅ᵈ ⟦ μs ⟧smod-seq
reduce-smod-seq-sound [] = reflᵈ
reduce-smod-seq-sound (μ ∷ []) rewrite reduce-smod-seq-cons-empty μ = reflᵈ
reduce-smod-seq-sound (μ ∷ μs@(_ ∷ _)) =
  transᵈ (reduce-smod-seq-cons-sound μ (reduce-smod-seq μs))
         (ⓓ-congʳ ⟦ μ ⟧smod (reduce-smod-seq-sound μs))

reduce-modality-expr : ModalityExpr m m' → ModalityExpr m m'
reduce-modality-expr = interpret-smod-sequence ∘ reduce-smod-seq ∘ flatten

reduce-modality-expr-sound : (μ : ModalityExpr m m') → ⟦ reduce-modality-expr μ ⟧modality ≅ᵈ ⟦ μ ⟧modality
reduce-modality-expr-sound μ = transᵈ (reduce-smod-seq-sound (flatten μ)) (flatten-sound μ)

-- Finally: the actual new decision procedure for modalities
⟦⟧modality-cong : {μ ρ : ModalityExpr m m'} → μ ≡ ρ → ⟦ μ ⟧modality ≅ᵈ ⟦ ρ ⟧modality
⟦⟧modality-cong refl = reflᵈ

modality-reflect : (μ ρ : ModalityExpr m m') → reduce-modality-expr μ ≡ reduce-modality-expr ρ →
                   ⟦ μ ⟧modality ≅ᵈ ⟦ ρ ⟧modality
modality-reflect μ ρ e = transᵈ (transᵈ (symᵈ (reduce-modality-expr-sound μ))
                                        (⟦⟧modality-cong e))
                                (reduce-modality-expr-sound ρ)

reduce-compare-mod : (μ ρ : ModalityExpr m m') → TCM (⟦ μ ⟧modality ≅ᵈ ⟦ ρ ⟧modality)
reduce-compare-mod μ ρ =
  let μ' = reduce-modality-expr μ
      ρ' = reduce-modality-expr ρ
  in with-error-msg ("Modality " ++ show-modality μ ++ " is not equal to " ++ show-modality ρ ++ ", reduced the equality to " ++
                      show-modality μ' ++ " =?= " ++ show-modality ρ') (
    (μ' ≟modality ρ') >>= λ μ'=ρ' → return (modality-reflect μ ρ μ'=ρ'))

-- The final procedure will test if two modalities are literally equal before reducing them.
_≃ᵐ?_ : (μ ρ : ModalityExpr m m') → TCM (⟦ μ ⟧modality ≅ᵈ ⟦ ρ ⟧modality)
μ ≃ᵐ? ρ = (⟦⟧modality-cong <$> (μ ≟modality ρ)) <∣> reduce-compare-mod μ ρ
