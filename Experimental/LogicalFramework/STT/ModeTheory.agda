module Experimental.LogicalFramework.STT.ModeTheory where

open import Data.Nat


data Mode : Set where
  ★ ω : Mode

private variable
  m n o : Mode


data Modality : Mode → Mode → Set where
  𝟙★ : Modality ★ ★
  forever : Modality ω ★
  later^[_]ⓜconstantly : ℕ → Modality ★ ω
  later^[_] : ℕ → Modality ω ω
  later^[_]ⓜconstantlyⓜforever : ℕ → Modality ω ω

private variable
  μ ρ κ : Modality m n

𝟙 : Modality m m
𝟙 {★} = 𝟙★
𝟙 {ω} = later^[ 0 ]

later : Modality ω ω
later = later^[ 1 ]

constantly : Modality ★ ω
constantly = later^[ 0 ]ⓜconstantly

_ⓜ_ : Modality n o → Modality m n → Modality m o
𝟙★ ⓜ ρ = ρ
forever ⓜ later^[ k ]ⓜconstantly = 𝟙★
forever ⓜ later^[ k ] = forever
forever ⓜ later^[ k ]ⓜconstantlyⓜforever = forever
later^[ k ]ⓜconstantly ⓜ 𝟙★ = later^[ k ]ⓜconstantly
later^[ k ]ⓜconstantly ⓜ forever = later^[ k ]ⓜconstantlyⓜforever
later^[ k ] ⓜ later^[ l ]ⓜconstantly = later^[ k + l ]ⓜconstantly
later^[ k ] ⓜ later^[ l ] = later^[ k + l ]
later^[ k ] ⓜ later^[ l ]ⓜconstantlyⓜforever = later^[ k + l ]ⓜconstantlyⓜforever
later^[ k ]ⓜconstantlyⓜforever ⓜ later^[ l ]ⓜconstantly = later^[ k ]ⓜconstantly
later^[ k ]ⓜconstantlyⓜforever ⓜ later^[ l ] = later^[ k ]ⓜconstantlyⓜforever
later^[ k ]ⓜconstantlyⓜforever ⓜ later^[ l ]ⓜconstantlyⓜforever = later^[ k ]ⓜconstantlyⓜforever

infixl 5 _ⓣ-hor_
infixl 6 _ⓣ-vert_
data TwoCell : (μ ρ : Modality m n) → Set where
  id-cell : TwoCell μ μ
  _ⓣ-vert_ : TwoCell ρ κ → TwoCell μ ρ → TwoCell μ κ
    -- ^ Vertical composition of 2-cells
  _ⓣ-hor_ : {μ1 ρ1 : Modality n o} {μ2 ρ2 : Modality m n} →
            TwoCell μ1 ρ1 → TwoCell μ2 ρ2 → TwoCell (μ1 ⓜ μ2) (ρ1 ⓜ ρ2)
    -- ^ Horizontal composition of 2-cells
  𝟙≤later : TwoCell 𝟙 later
  constantly∘forever≤𝟙 : TwoCell (constantly ⓜ forever) 𝟙
