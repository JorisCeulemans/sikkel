module Experimental.LogicalFramework.MSTT.Parameter.ModeTheory where

open import Data.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory as M using (BaseCategory)
open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.DRA as DRA hiding (𝟙; TwoCell; id-cell; _ⓣ-vert_; _ⓣ-hor_)

open import Experimental.LogicalFramework.Proof.CheckingMonad


record MTBasis : Set₁ where
  no-eta-equality
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
    ⟦_⟧non-triv-mod : ∀ {m n} → NonTrivModality m n → DRA ⟦ m ⟧mode ⟦ n ⟧mode

  infix 50 ‵_
  data Modality : Mode → Mode → Set where
    𝟙 : ∀ {m} → Modality m m
    ‵_ : ∀ {m n} → NonTrivModality m n → Modality m n

  mod-dom mod-cod : ∀ {m n} → Modality m n → Mode
  mod-dom {m}     μ = m
  mod-cod {_} {n} μ = n

  ⟦_⟧mod : ∀ {m n} → Modality m n → DRA ⟦ m ⟧mode ⟦ n ⟧mode
  ⟦ 𝟙 ⟧mod = DRA.𝟙
  ⟦ ‵ μ ⟧mod = ⟦ μ ⟧non-triv-mod

  ⟦𝟙⟧-sound : ∀ {m} → ⟦ 𝟙 {m} ⟧mod ≅ᵈ DRA.𝟙
  ⟦𝟙⟧-sound = DRA.reflᵈ

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
  no-eta-equality

  open MTBasis mtb

  field
    _ⓜnon-triv_ : ∀ {m n o} → NonTrivModality n o → NonTrivModality m n → Modality m o

    ⟦ⓜ⟧-non-triv-sound : ∀ {m n o} (μ : NonTrivModality n o) (κ : NonTrivModality m n) →
                         ⟦ μ ⓜnon-triv κ ⟧mod ≅ᵈ ⟦ μ ⟧non-triv-mod DRA.ⓓ ⟦ κ ⟧non-triv-mod

  _ⓜ_ : ∀ {m n o} → Modality n o → Modality m n → Modality m o
  μ   ⓜ 𝟙 = μ
  𝟙   ⓜ ‵ ρ = ‵ ρ
  ‵ μ ⓜ ‵ ρ = μ ⓜnon-triv ρ

  ⟦ⓜ⟧-sound : ∀ {m n o} (μ : Modality n o) (κ : Modality m n) → ⟦ μ ⓜ κ ⟧mod ≅ᵈ ⟦ μ ⟧mod ⓓ ⟦ κ ⟧mod
  ⟦ⓜ⟧-sound μ     𝟙     = symᵈ (𝟙-unitʳ _)
  ⟦ⓜ⟧-sound 𝟙     (‵ κ) = symᵈ (𝟙-unitˡ _)
  ⟦ⓜ⟧-sound (‵ μ) (‵ κ) = ⟦ⓜ⟧-non-triv-sound μ κ


record MTCompositionLaws (mtb : MTBasis) (mtc : MTComposition mtb) : Set where
  no-eta-equality

  open MTBasis mtb
  open MTComposition mtc
  
  field
    mod-non-triv-assoc : ∀ {m n o p} → (μ : NonTrivModality o p) (ρ : NonTrivModality n o) (κ : NonTrivModality m n) →
                         (μ ⓜnon-triv ρ) ⓜ ‵ κ ≡ ‵ μ ⓜ (ρ ⓜnon-triv κ)

  mod-unitˡ : ∀ {m n} {μ : Modality m n} → 𝟙 ⓜ μ ≡ μ
  mod-unitˡ {μ = 𝟙}   = refl
  mod-unitˡ {μ = ‵ μ} = refl

  mod-unitʳ : ∀ {m n} {μ : Modality m n} → μ ⓜ 𝟙 ≡ μ
  mod-unitʳ = refl

  mod-assoc : ∀ {m n o p} {μ : Modality o p} {ρ : Modality n o} (κ : Modality m n) → (μ ⓜ ρ) ⓜ κ ≡ μ ⓜ (ρ ⓜ κ)
  mod-assoc 𝟙 = refl
  mod-assoc {ρ = 𝟙} (‵ κ) = refl
  mod-assoc {μ = 𝟙} {ρ = ‵ ρ} (‵ κ) = sym mod-unitˡ
  mod-assoc {μ = ‵ μ} {ρ = ‵ ρ} (‵ κ) = mod-non-triv-assoc μ ρ κ


record MTTwoCell (mtb : MTBasis) (mtc : MTComposition mtb) : Set₁ where
  no-eta-equality

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

    ⟦_⟧two-cell : ∀ {m n} {μ κ : Modality m n} → TwoCell μ κ → DRA.TwoCell ⟦ μ ⟧mod ⟦ κ ⟧mod

    -- TODO: add comment that we are constructing a pseudofunctor from
    -- the mode theory to the 2-category of base categories and DRAs.
    -- (and possibly find better name for ⟦ⓜ⟧-sound)
    ⟦id-cell⟧-sound : ∀ {m n} (μ : Modality m n) → ⟦ id-cell {μ = μ} ⟧two-cell DRA.≅ᵗᶜ DRA.id-cell
    ⟦ⓣ-vert⟧-sound : ∀ {m n} {μ κ ρ : Modality m n}
                     (β : TwoCell κ ρ) (α : TwoCell μ κ) →
                     ⟦ β ⓣ-vert α ⟧two-cell DRA.≅ᵗᶜ ⟦ β ⟧two-cell DRA.ⓣ-vert ⟦ α ⟧two-cell
    ⟦ⓜ⟧-sound-natural : ∀ {m n o} {μ μ' : Modality n o} {ρ ρ' : Modality m n}
                        (α : TwoCell μ μ') (β : TwoCell ρ ρ') →
                        from (⟦ⓜ⟧-sound μ' ρ') DRA.ⓣ-vert ⟦ α ⓣ-hor β ⟧two-cell
                          DRA.≅ᵗᶜ
                        (⟦ α ⟧two-cell DRA.ⓣ-hor ⟦ β ⟧two-cell) DRA.ⓣ-vert from (⟦ⓜ⟧-sound μ ρ)

  eq-cell : ∀ {m n} {μ ρ : Modality m n} → μ ≡ ρ → TwoCell μ ρ
  eq-cell refl = id-cell

  transp-cellʳ : ∀ {m n} {μ ρ ρ' : Modality m n} → ρ ≡ ρ' → TwoCell μ ρ → TwoCell μ ρ'
  transp-cellʳ refl α = α

  transp-cellˡ : ∀ {m n} {μ μ' ρ : Modality m n} → μ ≡ μ' → TwoCell μ ρ → TwoCell μ' ρ
  transp-cellˡ refl α = α

  _≟cell_ : {m n : Mode} {μ κ : Modality m n} (α β : TwoCell μ κ) → PCM (α ≡ β)
  α ≟cell β = from-maybe "Two-cells are not equal." (two-cell-eq? α β)

record ModeTheory : Set₁ where
  no-eta-equality
  field
    mtb : MTBasis
    mtc : MTComposition mtb
    mtc-laws : MTCompositionLaws mtb mtc
    mt2 : MTTwoCell mtb mtc

  open MTBasis mtb public
  open MTComposition mtc public
  open MTCompositionLaws mtc-laws public
  open MTTwoCell mt2 public
