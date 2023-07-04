module Experimental.LogicalFramework.MSTT.Parameter.ModeTheory where

open import Data.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory as M using (BaseCategory)
open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.Modality as M using (_≅ᵐ_)

open import Experimental.LogicalFramework.Proof.CheckingMonad


record MTBasis : Set₁ where
  field
    Mode : Set
    NonTrivModality : Mode → Mode → Set
      -- ^ A modality is either the unit modality 𝟙 or a non-trivial modality
      --   described above. This treatment allows for some more definitional
      --   equalities (e.g. the interpretation of the unit modality is
      --   definitionally the semantic unit modality, and 𝟙 is definitionally
      --   a left unit of modality composition ⓜ).

    mode-eq? : (m n : Mode) → Maybe (m ≡ n)
    non-triv-mod-eq? : ∀ {m n} (μ κ : NonTrivModality m n) → Maybe (μ ≡ κ)

    ⟦_⟧mode : Mode → BaseCategory
    ⟦_⟧non-triv-mod : ∀ {m n} → NonTrivModality m n → M.Modality ⟦ m ⟧mode ⟦ n ⟧mode

  infix 50 ‵_
  data Modality : Mode → Mode → Set where
    𝟙 : ∀ {m} → Modality m m
    ‵_ : ∀ {m n} → NonTrivModality m n → Modality m n

  mod-dom mod-cod : ∀ {m n} → Modality m n → Mode
  mod-dom {m}     μ = m
  mod-cod {_} {n} μ = n

  ⟦_⟧mod : ∀ {m n} → Modality m n → M.Modality ⟦ m ⟧mode ⟦ n ⟧mode
  ⟦ 𝟙 ⟧mod = M.𝟙
  ⟦ ‵ μ ⟧mod = ⟦ μ ⟧non-triv-mod

  ⟦𝟙⟧-sound : ∀ {m} → ⟦ 𝟙 {m} ⟧mod ≅ᵐ M.𝟙
  ⟦𝟙⟧-sound = M.reflᵐ

  _≟mode_ : (m n : Mode) → PCM (m ≡ n)
  m ≟mode n = from-maybe "Modes are not equal." (mode-eq? m n)

  modality-msg : ErrorMsg
  modality-msg = "Modalities are not equal."

  _≟mod_ : {m n : Mode} (μ κ : Modality m n) → PCM (μ ≡ κ)
  𝟙 ≟mod 𝟙 = return refl
  ‵ μ ≟mod ‵ κ = do
    refl ← from-maybe modality-msg (non-triv-mod-eq? μ κ)
    return refl
  _ ≟mod _ = throw-error modality-msg


record MTComposition (mtb : MTBasis) : Set₁ where
  open MTBasis mtb

  field
    _ⓜnon-triv_ : ∀ {m n o} → NonTrivModality n o → NonTrivModality m n → Modality m o

    ⟦ⓜ⟧-non-triv-sound : ∀ {m n o} (μ : NonTrivModality n o) (κ : NonTrivModality m n) →
                         ⟦ μ ⓜnon-triv κ ⟧mod ≅ᵐ ⟦ μ ⟧non-triv-mod M.ⓜ ⟦ κ ⟧non-triv-mod

  _ⓜ_ : ∀ {m n o} → Modality n o → Modality m n → Modality m o
  𝟙 ⓜ ρ = ρ
  ‵ μ ⓜ 𝟙 = ‵ μ
  ‵ μ ⓜ ‵ ρ = μ ⓜnon-triv ρ

  ⟦ⓜ⟧-sound : ∀ {m n o} (μ : Modality n o) (κ : Modality m n) → ⟦ μ ⓜ κ ⟧mod ≅ᵐ ⟦ μ ⟧mod M.ⓜ ⟦ κ ⟧mod
  ⟦ⓜ⟧-sound 𝟙     κ     = M.symᵐ (M.𝟙-unitˡ _)
  ⟦ⓜ⟧-sound (‵ μ) 𝟙     = M.symᵐ (M.𝟙-unitʳ _)
  ⟦ⓜ⟧-sound (‵ μ) (‵ κ) = ⟦ⓜ⟧-non-triv-sound μ κ


record MTCompositionLaws (mtb : MTBasis) (mtc : MTComposition mtb) : Set where
  open MTBasis mtb
  open MTComposition mtc
  
  field
    mod-non-triv-assoc : ∀ {m n o p} → (μ : NonTrivModality o p) (ρ : NonTrivModality n o) (κ : NonTrivModality m n) →
                         (μ ⓜnon-triv ρ) ⓜ ‵ κ ≡ ‵ μ ⓜ (ρ ⓜnon-triv κ)

  mod-unitˡ : ∀ {m n} {μ : Modality m n} → 𝟙 ⓜ μ ≡ μ
  mod-unitˡ  = refl

  mod-unitʳ : ∀ {m n} {μ : Modality m n} → μ ⓜ 𝟙 ≡ μ
  mod-unitʳ {μ = 𝟙} = refl
  mod-unitʳ {μ = ‵ μ} = refl

  mod-assoc : ∀ {m n o p} (μ : Modality o p) {ρ : Modality n o} {κ : Modality m n} → (μ ⓜ ρ) ⓜ κ ≡ μ ⓜ (ρ ⓜ κ)
  mod-assoc 𝟙 = refl
  mod-assoc (‵ μ) {ρ = 𝟙} = refl
  mod-assoc (‵ μ) {ρ = ‵ ρ} {κ = 𝟙} = mod-unitʳ
  mod-assoc (‵ μ) {ρ = ‵ ρ} {κ = ‵ κ} = mod-non-triv-assoc μ ρ κ


record MTTwoCell (mtb : MTBasis) (mtc : MTComposition mtb) : Set₁ where
  open MTBasis mtb
  open MTComposition mtc

  infixl 6 _ⓣ-vert_
  infixl 5 _ⓣ-hor_
  field
    TwoCell : ∀ {m n} (μ ρ : Modality m n) → Set
    id-cell : ∀ {m n} {μ : Modality m n} → TwoCell μ μ
    _ⓣ-vert_ : ∀ {m n} {μ ρ κ : Modality m n} → TwoCell ρ κ → TwoCell μ ρ → TwoCell μ κ
    _ⓣ-hor_ : ∀ {m n o} {μ1 ρ1 : Modality n o} {μ2 ρ2 : Modality m n} →
              TwoCell μ1 ρ1 → TwoCell μ2 ρ2 → TwoCell (μ1 ⓜ μ2) (ρ1 ⓜ ρ2)
    two-cell-eq? : ∀ {m n} {μ ρ : Modality m n} (α β : TwoCell μ ρ) → Maybe (α ≡ β)

    ⟦_⟧two-cell : ∀ {m n} {μ κ : Modality m n} → TwoCell μ κ → M.TwoCell ⟦ μ ⟧mod ⟦ κ ⟧mod

  eq-cell : ∀ {m n} {μ ρ : Modality m n} → μ ≡ ρ → TwoCell μ ρ
  eq-cell refl = id-cell

  transp-cellʳ : ∀ {m n} {μ ρ ρ' : Modality m n} → ρ ≡ ρ' → TwoCell μ ρ → TwoCell μ ρ'
  transp-cellʳ refl α = α

  transp-cellˡ : ∀ {m n} {μ μ' ρ : Modality m n} → μ ≡ μ' → TwoCell μ ρ → TwoCell μ' ρ
  transp-cellˡ refl α = α

  _≟cell_ : {m n : Mode} {μ κ : Modality m n} (α β : TwoCell μ κ) → PCM (α ≡ β)
  α ≟cell β = from-maybe "Two-cells are not equal." (two-cell-eq? α β)

record ModeTheory : Set₁ where
  field
    mtb : MTBasis
    mtc : MTComposition mtb
    mtc-laws : MTCompositionLaws mtb mtc
    mt2 : MTTwoCell mtb mtc

  open MTBasis mtb public
  open MTComposition mtc public
  open MTCompositionLaws mtc-laws public
  open MTTwoCell mt2 public
