--------------------------------------------------
-- Checking equality for mode, modality and type expressions.
--------------------------------------------------

module Experimental.DeepEmbedding.GuardedRecursion.TypeChecker.Equality where

open import Data.String
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import CwF-Structure as M hiding (◇; _,,_; var; _++_)
open import Types.Functions as M hiding (_⇛_; lam; app)
open import Types.Products as M hiding (_⊠_; pair; fst; snd)
open import Modalities as M hiding (𝟙; _ⓜ_; ⟨_∣_⟩; _,lock⟨_⟩; mod-intro; mod-elim)
open import GuardedRecursion.Modalities as M hiding (timeless; allnow; later; _⊛_; löb)
open import GuardedRecursion.Streams.Guarded as M hiding (GStream; g-cons; g-head; g-tail)

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
★ ≟mode ★ = return refl
ω ≟mode ω = return refl
m ≟mode m' = type-error ("Mode " ++ show-mode m ++ " is not equal to " ++ show-mode m')

_≟modality_ : (μ ρ : ModalityExpr m m') → TCM (μ ≡ ρ)
𝟙 ≟modality 𝟙 = return refl
timeless ≟modality timeless = return refl
allnow ≟modality allnow = return refl
later ≟modality later = return refl
(_ⓜ_ {m} μ ρ) ≟modality (_ⓜ_ {m'} μ' ρ') = do
  refl ← m ≟mode m'
  cong₂ _ⓜ_ <$> (μ ≟modality μ') ⊛ (ρ ≟modality ρ')
μ ≟modality ρ = type-error ("Modality " ++ show-modality μ ++ " is not equal to " ++ show-modality ρ)

_≟ty_ : (T1 T2 : TyExpr m) → TCM (T1 ≡ T2)
Nat' ≟ty Nat' = return refl
Bool' ≟ty Bool' = return refl
(T1 ⇛ T2) ≟ty (T3 ⇛ T4) = (cong₂ _⇛_) <$> (T1 ≟ty T3) ⊛ (T2 ≟ty T4)
(T1 ⊠ T2) ≟ty (T3 ⊠ T4) = (cong₂ _⊠_) <$> (T1 ≟ty T3) ⊛ (T2 ≟ty T4)
(⟨_∣_⟩ {m1} μ1 T1) ≟ty (⟨_∣_⟩ {m2} μ2 T2) = do
  refl ← m1 ≟mode m2
  cong₂ ⟨_∣_⟩ <$> (μ1 ≟modality μ2) ⊛ (T1 ≟ty T2)
(GStream T) ≟ty (GStream S) = (cong GStream) <$> (T ≟ty S)
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
  s-timeless : SModalityExpr ★ ω
  s-allnow : SModalityExpr ω ★
  s-later : SModalityExpr ω ω

interpret-smod-expr : SModalityExpr m m' → ModalityExpr m m'
interpret-smod-expr s-timeless = timeless
interpret-smod-expr s-allnow = allnow
interpret-smod-expr s-later = later

⟦_⟧smod : SModalityExpr m m' → Modality ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ μ ⟧smod = ⟦ interpret-smod-expr μ ⟧modality

data SModalitySeq : ModeExpr → ModeExpr → Set where
  [] : SModalitySeq m m
  _∷_ : SModalityExpr m'' m' → SModalitySeq m m'' → SModalitySeq m m'

interpret-smod-sequence : SModalitySeq m m' → ModalityExpr m m'
interpret-smod-sequence [] = 𝟙
interpret-smod-sequence (μ ∷ []) = interpret-smod-expr μ
interpret-smod-sequence (μ ∷ μs@(_ ∷ _)) = interpret-smod-expr μ ⓜ interpret-smod-sequence μs

⟦_⟧smod-seq : SModalitySeq m m' → Modality ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ μs ⟧smod-seq = ⟦ interpret-smod-sequence μs ⟧modality

interpret-smod-cons : (μ : SModalityExpr m'' m') (μs : SModalitySeq m m'') →
                      ⟦ μ ∷ μs ⟧smod-seq ≅ᵐ ⟦ μ ⟧smod M.ⓜ ⟦ μs ⟧smod-seq
interpret-smod-cons μ [] = ≅ᵐ-sym (𝟙-identityʳ ⟦ μ ⟧smod)
interpret-smod-cons μ (_ ∷ μs) = ≅ᵐ-refl

-- Step 1: flattening a modality to a sequence of simple modalities.
_s++_ : SModalitySeq m'' m' → SModalitySeq m m'' → SModalitySeq m m'
[] s++ ρs = ρs
(μ ∷ μs) s++ ρs = μ ∷ (μs s++ ρs)

flatten : ModalityExpr m m' → SModalitySeq m m'
flatten 𝟙 = []
flatten (μ ⓜ ρ) = flatten μ s++ flatten ρ
flatten timeless = s-timeless ∷ []
flatten allnow = s-allnow ∷ []
flatten later = s-later ∷ []

s++-sound : (μs : SModalitySeq m'' m') (ρs : SModalitySeq m m'') →
            ⟦ μs s++ ρs ⟧smod-seq ≅ᵐ ⟦ μs ⟧smod-seq M.ⓜ ⟦ ρs ⟧smod-seq
s++-sound []               ρs = ≅ᵐ-sym (𝟙-identityˡ _)
s++-sound (μ ∷ [])         ρs = interpret-smod-cons μ ρs
s++-sound (μ ∷ μs@(_ ∷ _)) ρs = begin
  ⟦ μ ⟧smod M.ⓜ ⟦ μs s++ ρs ⟧smod-seq
    ≅⟨ ⓜ-congˡ ⟦ μ ⟧smod (s++-sound μs ρs) ⟩
  ⟦ μ ⟧smod M.ⓜ (⟦ μs ⟧smod-seq M.ⓜ ⟦ ρs ⟧smod-seq)
    ≅˘⟨ ⓜ-assoc ⟦ μ ⟧smod ⟦ μs ⟧smod-seq ⟦ ρs ⟧smod-seq ⟩
  (⟦ μ ⟧smod M.ⓜ ⟦ μs ⟧smod-seq) M.ⓜ ⟦ ρs ⟧smod-seq ∎
  where open ≅ᵐ-Reasoning

flatten-sound : (μ : ModalityExpr m m') → ⟦ flatten μ ⟧smod-seq ≅ᵐ ⟦ μ ⟧modality
flatten-sound 𝟙 = ≅ᵐ-refl
flatten-sound (μ ⓜ ρ) = begin
  ⟦ flatten μ s++ flatten ρ ⟧smod-seq
    ≅⟨ s++-sound (flatten μ) (flatten ρ) ⟩
  ⟦ flatten μ ⟧smod-seq M.ⓜ ⟦ flatten ρ ⟧smod-seq
    ≅⟨ ⓜ-congʳ ⟦ flatten ρ ⟧smod-seq (flatten-sound μ) ⟩
  ⟦ μ ⟧modality M.ⓜ ⟦ flatten ρ ⟧smod-seq
    ≅⟨ ⓜ-congˡ ⟦ μ ⟧modality (flatten-sound ρ) ⟩
  ⟦ μ ⟧modality M.ⓜ ⟦ ρ ⟧modality ∎
  where open ≅ᵐ-Reasoning
flatten-sound timeless = ≅ᵐ-refl
flatten-sound allnow = ≅ᵐ-refl
flatten-sound later = ≅ᵐ-refl

-- Step 2: reducing the sequence using specific equalities
reduce-smod-seq-cons : SModalityExpr m'' m' → SModalitySeq m m'' → SModalitySeq m m'
reduce-smod-seq-cons s-allnow (s-timeless ∷ μs) = μs
reduce-smod-seq-cons s-allnow (s-later    ∷ μs) = reduce-smod-seq-cons s-allnow μs
reduce-smod-seq-cons μ        μs = μ ∷ μs

reduce-smod-seq : SModalitySeq m m' → SModalitySeq m m'
reduce-smod-seq [] = []
reduce-smod-seq (μ ∷ μs) = reduce-smod-seq-cons μ (reduce-smod-seq μs)

reduce-smod-seq-cons-sound : (μ : SModalityExpr m'' m') (μs : SModalitySeq m m'') →
                             ⟦ reduce-smod-seq-cons μ μs ⟧smod-seq ≅ᵐ ⟦ μ ⟧smod M.ⓜ ⟦ μs ⟧smod-seq
reduce-smod-seq-cons-sound s-allnow (s-timeless ∷ μs) = begin
  ⟦ μs ⟧smod-seq
    ≅˘⟨ 𝟙-identityˡ ⟦ μs ⟧smod-seq ⟩
  M.𝟙 M.ⓜ ⟦ μs ⟧smod-seq
    ≅˘⟨ ⓜ-congʳ ⟦ μs ⟧smod-seq allnow-timeless ⟩
  (M.allnow M.ⓜ M.timeless) M.ⓜ ⟦ μs ⟧smod-seq
    ≅⟨ ⓜ-assoc _ _ _ ⟩
  M.allnow M.ⓜ (M.timeless M.ⓜ ⟦ μs ⟧smod-seq)
    ≅˘⟨ ⓜ-congˡ M.allnow (interpret-smod-cons s-timeless μs) ⟩
  M.allnow M.ⓜ ⟦ s-timeless ∷ μs ⟧smod-seq ∎
  where open ≅ᵐ-Reasoning
reduce-smod-seq-cons-sound s-allnow (s-later    ∷ μs) = begin
  ⟦ reduce-smod-seq-cons s-allnow μs ⟧smod-seq
    ≅⟨ reduce-smod-seq-cons-sound s-allnow μs ⟩
  M.allnow M.ⓜ ⟦ μs ⟧smod-seq
    ≅˘⟨ ⓜ-congʳ ⟦ μs ⟧smod-seq allnow-later ⟩
  (M.allnow M.ⓜ M.later) M.ⓜ ⟦ μs ⟧smod-seq
    ≅⟨ ⓜ-assoc _ _ _ ⟩
  M.allnow M.ⓜ (M.later M.ⓜ ⟦ μs ⟧smod-seq)
    ≅˘⟨ ⓜ-congˡ M.allnow (interpret-smod-cons s-later μs) ⟩
  M.allnow M.ⓜ ⟦ s-later ∷ μs ⟧smod-seq ∎
  where open ≅ᵐ-Reasoning
reduce-smod-seq-cons-sound s-allnow [] = ≅ᵐ-sym (𝟙-identityʳ _)
reduce-smod-seq-cons-sound s-timeless μs = interpret-smod-cons s-timeless μs
reduce-smod-seq-cons-sound s-later μs = interpret-smod-cons s-later μs

reduce-smod-seq-cons-empty : (μ : SModalityExpr m m') → reduce-smod-seq-cons μ [] ≡ μ ∷ []
reduce-smod-seq-cons-empty s-timeless = refl
reduce-smod-seq-cons-empty s-allnow = refl
reduce-smod-seq-cons-empty s-later = refl

reduce-smod-seq-sound : (μs : SModalitySeq m m') → ⟦ reduce-smod-seq μs ⟧smod-seq ≅ᵐ ⟦ μs ⟧smod-seq
reduce-smod-seq-sound [] = ≅ᵐ-refl
reduce-smod-seq-sound (μ ∷ []) rewrite reduce-smod-seq-cons-empty μ = ≅ᵐ-refl
reduce-smod-seq-sound (μ ∷ μs@(_ ∷ _)) = begin
  ⟦ reduce-smod-seq-cons μ (reduce-smod-seq μs) ⟧smod-seq
    ≅⟨ reduce-smod-seq-cons-sound μ (reduce-smod-seq μs) ⟩
  ⟦ μ ⟧smod M.ⓜ ⟦ reduce-smod-seq μs ⟧smod-seq
    ≅⟨ ⓜ-congˡ ⟦ μ ⟧smod (reduce-smod-seq-sound μs) ⟩
  ⟦ μ ⟧smod M.ⓜ ⟦ μs ⟧smod-seq ∎
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
apply-mod-reduced 𝟙 T = T
apply-mod-reduced μ ⟨ ρ ∣ T ⟩ = apply-mod-reduced (reduce-modality-expr (μ ⓜ ρ)) T
apply-mod-reduced μ T = ⟨ μ ∣ T ⟩

reduce-ty-expr : TyExpr m → TyExpr m
reduce-ty-expr Nat' = Nat'
reduce-ty-expr Bool' = Bool'
reduce-ty-expr (T1 ⇛ T2) = reduce-ty-expr T1 ⇛ reduce-ty-expr T2
reduce-ty-expr (T1 ⊠ T2) = reduce-ty-expr T1 ⊠ reduce-ty-expr T2
reduce-ty-expr ⟨ μ ∣ T ⟩ = apply-mod-reduced (reduce-modality-expr μ) -- we have to apply reduce-modality-expr here to see if μ reduces to 𝟙
                                             (reduce-ty-expr T)
reduce-ty-expr (GStream T) = GStream (reduce-ty-expr T)

apply-mod-reduced-sound : ∀ (μ : ModalityExpr m m') (T : TyExpr m) {Γ} →
                          ⟦ apply-mod-reduced μ T ⟧ty {Γ} ≅ᵗʸ M.⟨_∣_⟩ ⟦ μ ⟧modality ⟦ T ⟧ty
apply-mod-reduced-sound 𝟙 T = ≅ᵗʸ-refl
apply-mod-reduced-sound (μ ⓜ ρ) Nat' = ≅ᵗʸ-refl
apply-mod-reduced-sound (μ ⓜ ρ) Bool' = ≅ᵗʸ-refl
apply-mod-reduced-sound (μ ⓜ ρ) (T1 ⇛ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound (μ ⓜ ρ) (T1 ⊠ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound (μ ⓜ ρ) ⟨ κ ∣ T ⟩ = ≅ᵗʸ-trans (apply-mod-reduced-sound (reduce-modality-expr (μ ⓜ ρ ⓜ κ)) T)
                                                      (eq-mod-closed (reduce-modality-expr-sound (μ ⓜ ρ ⓜ κ)) ⟦ T ⟧ty {{⟦⟧ty-natural T}})
apply-mod-reduced-sound (μ ⓜ ρ) (GStream T) = ≅ᵗʸ-refl
apply-mod-reduced-sound timeless Nat' = ≅ᵗʸ-refl
apply-mod-reduced-sound timeless Bool' = ≅ᵗʸ-refl
apply-mod-reduced-sound timeless (T1 ⇛ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound timeless (T1 ⊠ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound timeless ⟨ κ ∣ T ⟩ = ≅ᵗʸ-trans (apply-mod-reduced-sound (reduce-modality-expr (timeless ⓜ κ)) T)
                                                       (eq-mod-closed (reduce-modality-expr-sound (timeless ⓜ κ)) ⟦ T ⟧ty {{⟦⟧ty-natural T}})
apply-mod-reduced-sound allnow Nat' = ≅ᵗʸ-refl
apply-mod-reduced-sound allnow Bool' = ≅ᵗʸ-refl
apply-mod-reduced-sound allnow (T1 ⇛ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound allnow (T1 ⊠ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound allnow ⟨ κ ∣ T ⟩ = ≅ᵗʸ-trans (apply-mod-reduced-sound (reduce-modality-expr (allnow ⓜ κ)) T)
                                                     (eq-mod-closed (reduce-modality-expr-sound (allnow ⓜ κ)) ⟦ T ⟧ty {{⟦⟧ty-natural T}})
apply-mod-reduced-sound allnow (GStream T) = ≅ᵗʸ-refl
apply-mod-reduced-sound later Nat' = ≅ᵗʸ-refl
apply-mod-reduced-sound later Bool' = ≅ᵗʸ-refl
apply-mod-reduced-sound later (T1 ⇛ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound later (T1 ⊠ T2) = ≅ᵗʸ-refl
apply-mod-reduced-sound later ⟨ κ ∣ T ⟩ = ≅ᵗʸ-trans (apply-mod-reduced-sound (reduce-modality-expr (later ⓜ κ)) T)
                                                    (eq-mod-closed (reduce-modality-expr-sound (later ⓜ κ)) ⟦ T ⟧ty {{⟦⟧ty-natural T}})
apply-mod-reduced-sound later (GStream T) = ≅ᵗʸ-refl

reduce-ty-expr-sound : (T : TyExpr m) → ∀ {Γ} →  ⟦ reduce-ty-expr T ⟧ty {Γ} ≅ᵗʸ ⟦ T ⟧ty
reduce-ty-expr-sound Nat' = ≅ᵗʸ-refl
reduce-ty-expr-sound Bool' = ≅ᵗʸ-refl
reduce-ty-expr-sound (T1 ⇛ T2) = ⇛-cong (reduce-ty-expr-sound T1) (reduce-ty-expr-sound T2)
reduce-ty-expr-sound (T1 ⊠ T2) = ⊠-cong (reduce-ty-expr-sound T1) (reduce-ty-expr-sound T2)
reduce-ty-expr-sound ⟨ μ ∣ T ⟩ = ≅ᵗʸ-trans (apply-mod-reduced-sound (reduce-modality-expr μ) (reduce-ty-expr T))
                                           (≅ᵗʸ-trans (eq-mod-closed (reduce-modality-expr-sound μ) ⟦ reduce-ty-expr T ⟧ty {{⟦⟧ty-natural (reduce-ty-expr T)}})
                                                      (mod-cong ⟦ μ ⟧modality (reduce-ty-expr-sound T)))
reduce-ty-expr-sound (GStream T) = gstream-cong (reduce-ty-expr-sound T)

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
⟦ mod {m} μ T ⟧≅ty?⟦ mod {m'} ρ S ⟧ = do
  refl ← m ≟mode m'
  T=S ← ⟦ T ⟧≅ty?⟦ S ⟧
  μ=ρ ← ⟦ μ ⟧≅mod?⟦ ρ ⟧
  return (≅ᵗʸ-trans (mod-cong ⟦ μ ⟧modality T=S) (eq-mod-closed μ=ρ ⟦ S ⟧ty {{⟦⟧ty-natural S}}))
⟦ T ⟧≅ty?⟦ S ⟧ = ⟦⟧ty-cong T S <$> (T ≟ty S)
-}
