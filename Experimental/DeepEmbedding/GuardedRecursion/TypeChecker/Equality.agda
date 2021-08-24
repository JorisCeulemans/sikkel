--------------------------------------------------
-- Checking equality for mode, modality and type expressions.
--------------------------------------------------

module Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Equality where

open import Data.String
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import CwF-Structure using (_≅ᵗʸ_; ≅ᵗʸ-refl; ≅ᵗʸ-trans; ≅ᵗʸ-sym)
open import Types.Functions
open import Types.Products
open import Modalities
open Modality
open import GuardedRecursion.Modalities using (later; timeless; allnow; allnow-timeless; allnow-later; ▻'-cong)
open import GuardedRecursion.Streams.Guarded

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
(_e-ⓜ_ {m} μ ρ) ≟modality (_e-ⓜ_ {m'} μ' ρ') = do
  refl ← m ≟mode m'
  cong₂ _e-ⓜ_ <$> (μ ≟modality μ') ⊛ (ρ ≟modality ρ')
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
interpret-smod-sequence (μ ∷ []) = interpret-smod-expr μ
interpret-smod-sequence (μ ∷ μs@(_ ∷ _)) = interpret-smod-expr μ e-ⓜ interpret-smod-sequence μs

⟦_⟧smod-seq : SModalitySequence m m' → Modality ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ μs ⟧smod-seq = ⟦ interpret-smod-sequence μs ⟧modality

interpret-smod-cons : (μ : SModalityExpr m'' m') (μs : SModalitySequence m m'') →
                      ⟦ μ ∷ μs ⟧smod-seq ≅ᵐ ⟦ μ ⟧smod ⓜ ⟦ μs ⟧smod-seq
interpret-smod-cons μ [] = ≅ᵐ-sym (𝟙-identityʳ ⟦ μ ⟧smod)
interpret-smod-cons μ (_ ∷ μs) = ≅ᵐ-refl

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
s++-sound []               ρs = ≅ᵐ-sym (𝟙-identityˡ _)
s++-sound (μ ∷ [])         ρs = interpret-smod-cons μ ρs
s++-sound (μ ∷ μs@(_ ∷ _)) ρs = begin
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
flatten-sound e-timeless = ≅ᵐ-refl
flatten-sound e-allnow = ≅ᵐ-refl
flatten-sound e-later = ≅ᵐ-refl

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
  allnow ⓜ (timeless ⓜ ⟦ μs ⟧smod-seq)
    ≅˘⟨ ⓜ-congˡ allnow (interpret-smod-cons se-timeless μs) ⟩
  allnow ⓜ ⟦ se-timeless ∷ μs ⟧smod-seq ∎
  where open ≅ᵐ-Reasoning
reduce-smod-seq-cons-sound se-allnow (se-later    ∷ μs) = begin
  ⟦ reduce-smod-seq-cons se-allnow μs ⟧smod-seq
    ≅⟨ reduce-smod-seq-cons-sound se-allnow μs ⟩
  allnow ⓜ ⟦ μs ⟧smod-seq
    ≅˘⟨ ⓜ-congʳ ⟦ μs ⟧smod-seq allnow-later ⟩
  (allnow ⓜ later) ⓜ ⟦ μs ⟧smod-seq
    ≅⟨ ⓜ-assoc _ _ _ ⟩
  allnow ⓜ (later ⓜ ⟦ μs ⟧smod-seq)
    ≅˘⟨ ⓜ-congˡ allnow (interpret-smod-cons se-later μs) ⟩
  allnow ⓜ ⟦ se-later ∷ μs ⟧smod-seq ∎
  where open ≅ᵐ-Reasoning
reduce-smod-seq-cons-sound se-allnow [] = ≅ᵐ-sym (𝟙-identityʳ _)
reduce-smod-seq-cons-sound se-timeless μs = interpret-smod-cons se-timeless μs
reduce-smod-seq-cons-sound se-later μs = interpret-smod-cons se-later μs

reduce-smod-seq-cons-empty : (μ : SModalityExpr m m') → reduce-smod-seq-cons μ [] ≡ μ ∷ []
reduce-smod-seq-cons-empty se-timeless = refl
reduce-smod-seq-cons-empty se-allnow = refl
reduce-smod-seq-cons-empty se-later = refl

reduce-smod-seq-sound : (μs : SModalitySequence m m') → ⟦ reduce-smod-seq μs ⟧smod-seq ≅ᵐ ⟦ μs ⟧smod-seq
reduce-smod-seq-sound [] = ≅ᵐ-refl
reduce-smod-seq-sound (μ ∷ []) rewrite reduce-smod-seq-cons-empty μ = ≅ᵐ-refl
reduce-smod-seq-sound (μ ∷ μs@(_ ∷ _)) = begin
  ⟦ reduce-smod-seq-cons μ (reduce-smod-seq μs) ⟧smod-seq
    ≅⟨ reduce-smod-seq-cons-sound μ (reduce-smod-seq μs) ⟩
  ⟦ μ ⟧smod ⓜ ⟦ reduce-smod-seq μs ⟧smod-seq
    ≅⟨ ⓜ-congˡ ⟦ μ ⟧smod (reduce-smod-seq-sound μs) ⟩
  ⟦ μ ⟧smod ⓜ ⟦ μs ⟧smod-seq ∎
  where open ≅ᵐ-Reasoning

reduce-modality-expr : ModalityExpr m m' → ModalityExpr m m'
reduce-modality-expr = interpret-smod-sequence ∘ reduce-smod-seq ∘ flatten

reduce-modality-expr-sound : (μ : ModalityExpr m m') → ⟦ reduce-modality-expr μ ⟧modality ≅ᵐ ⟦ μ ⟧modality
reduce-modality-expr-sound μ = ≅ᵐ-trans (reduce-smod-seq-sound (flatten μ)) (flatten-sound μ)

-- Finally: the actual new decision procedure for modalities
⟦⟧modality-cong : {μ ρ : ModalityExpr m m'} → μ ≡ ρ → ⟦ μ ⟧modality ≅ᵐ ⟦ ρ ⟧modality
⟦⟧modality-cong refl = ≅ᵐ-refl

modality-reflect : (μ ρ : ModalityExpr m m') → reduce-modality-expr μ ≡ reduce-modality-expr ρ →
                   ⟦ μ ⟧modality ≅ᵐ ⟦ ρ ⟧modality
modality-reflect μ ρ e = ≅ᵐ-trans (≅ᵐ-trans (≅ᵐ-sym (reduce-modality-expr-sound μ))
                                            (⟦⟧modality-cong e))
                                  (reduce-modality-expr-sound ρ)

reduce-compare-mod : (μ ρ : ModalityExpr m m') → TCM (⟦ μ ⟧modality ≅ᵐ ⟦ ρ ⟧modality)
reduce-compare-mod μ ρ =
  let μ' = reduce-modality-expr μ
      ρ' = reduce-modality-expr ρ
  in with-error-msg ("Modality " ++ show-modality μ ++ " is not equal to " ++ show-modality ρ ++ ", reduced the equality to " ++
                      show-modality μ' ++ " =?= " ++ show-modality ρ') (
    (μ' ≟modality ρ') >>= λ μ'=ρ' → return (modality-reflect μ ρ μ'=ρ'))

-- The final procedure will test if two modalities are literally equal before reducing them.
⟦_⟧≅mod?⟦_⟧ : (μ ρ : ModalityExpr m m') → TCM (⟦ μ ⟧modality ≅ᵐ ⟦ ρ ⟧modality)
⟦ μ ⟧≅mod?⟦ ρ ⟧ = (⟦⟧modality-cong <$> (μ ≟modality ρ)) <∣> reduce-compare-mod μ ρ


--------------------------------------------------
-- Deciding whether two types' interpretations are equivalent

apply-mod-reduced : ModalityExpr m m' → TyExpr m → TyExpr m'
apply-mod-reduced e-𝟙 T = T
apply-mod-reduced μ   (e-mod ρ T) = apply-mod-reduced (reduce-modality-expr (μ e-ⓜ ρ)) T
apply-mod-reduced μ   T = e-mod μ T

reduce-ty-expr : TyExpr m → TyExpr m
reduce-ty-expr e-Nat = e-Nat
reduce-ty-expr e-Bool = e-Bool
reduce-ty-expr (T1 e→ T2) = reduce-ty-expr T1 e→ reduce-ty-expr T2
reduce-ty-expr (T1 e-⊠ T2) = reduce-ty-expr T1 e-⊠ reduce-ty-expr T2
reduce-ty-expr (e-mod μ T) = apply-mod-reduced (reduce-modality-expr μ) -- we have to apply reduce-modality-expr here to see if μ reduces to e-𝟙
                                               (reduce-ty-expr T)
reduce-ty-expr (e-▻' T) = e-▻' (reduce-ty-expr T)
reduce-ty-expr (e-GStream T) = e-GStream (reduce-ty-expr T)

apply-mod-reduced-sound : ∀ (μ : ModalityExpr m m') (T : TyExpr m) {Γ} →
                          ⟦ apply-mod-reduced μ T ⟧ty {Γ} ≅ᵗʸ mod ⟦ μ ⟧modality ⟦ T ⟧ty
apply-mod-reduced-sound e-𝟙 T = ≅ᵗʸ-refl
apply-mod-reduced-sound (μ e-ⓜ ρ) e-Nat = ≅ᵗʸ-refl
apply-mod-reduced-sound (μ e-ⓜ ρ) e-Bool = ≅ᵗʸ-refl
apply-mod-reduced-sound (μ e-ⓜ ρ) (T1 e→ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound (μ e-ⓜ ρ) (T1 e-⊠ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound (μ e-ⓜ ρ) (e-mod κ T) = ≅ᵗʸ-trans (apply-mod-reduced-sound (reduce-modality-expr (μ e-ⓜ ρ e-ⓜ κ)) T)
                                                          (eq-mod-closed (reduce-modality-expr-sound (μ e-ⓜ ρ e-ⓜ κ)) ⟦ T ⟧ty {{⟦⟧ty-natural T}})
apply-mod-reduced-sound (μ e-ⓜ ρ) (e-▻' T) = ≅ᵗʸ-refl
apply-mod-reduced-sound (μ e-ⓜ ρ) (e-GStream T) = ≅ᵗʸ-refl
apply-mod-reduced-sound e-timeless e-Nat = ≅ᵗʸ-refl
apply-mod-reduced-sound e-timeless e-Bool = ≅ᵗʸ-refl
apply-mod-reduced-sound e-timeless (T1 e→ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound e-timeless (T1 e-⊠ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound e-timeless (e-mod κ T) = ≅ᵗʸ-trans (apply-mod-reduced-sound (reduce-modality-expr (e-timeless e-ⓜ κ)) T)
                                                           (eq-mod-closed (reduce-modality-expr-sound (e-timeless e-ⓜ κ)) ⟦ T ⟧ty {{⟦⟧ty-natural T}})
apply-mod-reduced-sound e-allnow e-Nat = ≅ᵗʸ-refl
apply-mod-reduced-sound e-allnow e-Bool = ≅ᵗʸ-refl
apply-mod-reduced-sound e-allnow (T1 e→ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound e-allnow (T1 e-⊠ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound e-allnow (e-mod κ T) = ≅ᵗʸ-trans (apply-mod-reduced-sound (reduce-modality-expr (e-allnow e-ⓜ κ)) T)
                                                         (eq-mod-closed (reduce-modality-expr-sound (e-allnow e-ⓜ κ)) ⟦ T ⟧ty {{⟦⟧ty-natural T}})
apply-mod-reduced-sound e-allnow (e-▻' T) = ≅ᵗʸ-refl
apply-mod-reduced-sound e-allnow (e-GStream T) = ≅ᵗʸ-refl
apply-mod-reduced-sound e-later e-Nat = ≅ᵗʸ-refl
apply-mod-reduced-sound e-later e-Bool = ≅ᵗʸ-refl
apply-mod-reduced-sound e-later (T1 e→ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound e-later (T1 e-⊠ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound e-later (e-mod κ T) = ≅ᵗʸ-trans (apply-mod-reduced-sound (reduce-modality-expr (e-later e-ⓜ κ)) T)
                                                        (eq-mod-closed (reduce-modality-expr-sound (e-later e-ⓜ κ)) ⟦ T ⟧ty {{⟦⟧ty-natural T}})
apply-mod-reduced-sound e-later (e-▻' T) = ≅ᵗʸ-refl
apply-mod-reduced-sound e-later (e-GStream T) = ≅ᵗʸ-refl

reduce-ty-expr-sound : (T : TyExpr m) → ∀ {Γ} →  ⟦ reduce-ty-expr T ⟧ty {Γ} ≅ᵗʸ ⟦ T ⟧ty
reduce-ty-expr-sound e-Nat = ≅ᵗʸ-refl
reduce-ty-expr-sound e-Bool = ≅ᵗʸ-refl
reduce-ty-expr-sound (T1 e→ T2) = ⇛-cong (reduce-ty-expr-sound T1) (reduce-ty-expr-sound T2)
reduce-ty-expr-sound (T1 e-⊠ T2) = ⊠-cong (reduce-ty-expr-sound T1) (reduce-ty-expr-sound T2)
reduce-ty-expr-sound (e-mod μ T) = ≅ᵗʸ-trans (apply-mod-reduced-sound (reduce-modality-expr μ) (reduce-ty-expr T))
                                             (≅ᵗʸ-trans (eq-mod-closed (reduce-modality-expr-sound μ) ⟦ reduce-ty-expr T ⟧ty {{⟦⟧ty-natural (reduce-ty-expr T)}})
                                                        (mod-cong ⟦ μ ⟧modality (reduce-ty-expr-sound T)))
reduce-ty-expr-sound (e-▻' T) = ▻'-cong (reduce-ty-expr-sound T)
reduce-ty-expr-sound (e-GStream T) = gstream-cong (reduce-ty-expr-sound T)

⟦⟧ty-cong : (T S : TyExpr m) → T ≡ S → ∀ {Γ} →  ⟦ T ⟧ty {Γ} ≅ᵗʸ ⟦ S ⟧ty
⟦⟧ty-cong T .T refl = ≅ᵗʸ-refl

ty-reflect : (T S : TyExpr m) → reduce-ty-expr T ≡ reduce-ty-expr S → ∀ {Γ} → ⟦ T ⟧ty {Γ} ≅ᵗʸ ⟦ S ⟧ty
ty-reflect T S e = ≅ᵗʸ-trans (≅ᵗʸ-trans (≅ᵗʸ-sym (reduce-ty-expr-sound T))
                                        (⟦⟧ty-cong _ _ e))
                             (reduce-ty-expr-sound S)

reduce-compare-ty : (T S : TyExpr m) → TCM (∀ {Γ} → ⟦ T ⟧ty {Γ} ≅ᵗʸ ⟦ S ⟧ty)
reduce-compare-ty T S =
  let T' = reduce-ty-expr T
      S' = reduce-ty-expr S
  in with-error-msg ("Type " ++ show-type T ++ " is not equal to " ++ show-type S ++ ", reduced the equality to " ++
                      show-type T' ++ " =?= " ++ show-type S') (
    (T' ≟ty S') >>= λ T'=S' → return (ty-reflect T S T'=S'))

⟦_⟧≅ty?⟦_⟧ : (T S : TyExpr m) → TCM (∀ {Γ} → ⟦ T ⟧ty {Γ} ≅ᵗʸ ⟦ S ⟧ty)
⟦ T ⟧≅ty?⟦ S ⟧ = (⟦⟧ty-cong T S <$> (T ≟ty S)) <∣> reduce-compare-ty T S

{-
⟦_⟧≅ty?⟦_⟧ : (T S : TyExpr m) → TCM (∀ {Γ} → ⟦ T ⟧ty {Γ} ≅ᵗʸ ⟦ S ⟧ty)
⟦ e-mod {m} μ T ⟧≅ty?⟦ e-mod {m'} ρ S ⟧ = do
  refl ← m ≟mode m'
  T=S ← ⟦ T ⟧≅ty?⟦ S ⟧
  μ=ρ ← ⟦ μ ⟧≅mod?⟦ ρ ⟧
  return (≅ᵗʸ-trans (mod-cong ⟦ μ ⟧modality T=S) (eq-mod-closed μ=ρ ⟦ S ⟧ty {{⟦⟧ty-natural S}}))
⟦ T ⟧≅ty?⟦ S ⟧ = ⟦⟧ty-cong T S <$> (T ≟ty S)
-}
