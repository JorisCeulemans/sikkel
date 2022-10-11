module Experimental.LogicalFramework.MSTT.ModeTheory where

open import Data.Nat
open import Data.Nat.Properties using (+-identityʳ; +-assoc; ≤-refl; ≤-trans; +-mono-≤; ≤-stepsʳ)
open import Relation.Binary.PropositionalEquality


data Mode : Set where
  ★ ω : Mode

private variable
  m n o p : Mode
  k l : ℕ


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

mod-unitˡ : {μ : Modality m n} → 𝟙 ⓜ μ ≡ μ
mod-unitˡ {n = ★} {μ} = refl
mod-unitˡ {n = ω} {later^[ k ]ⓜconstantly} = refl
mod-unitˡ {n = ω} {later^[ k ]} = refl
mod-unitˡ {n = ω} {later^[ k ]ⓜconstantlyⓜforever} = refl

mod-unitʳ : {μ : Modality m n} → μ ⓜ 𝟙 ≡ μ
mod-unitʳ {μ = 𝟙★} = refl
mod-unitʳ {μ = forever} = refl
mod-unitʳ {μ = later^[ k ]ⓜconstantly} = refl
mod-unitʳ {μ = later^[ k ]} = cong later^[_] (+-identityʳ k)
mod-unitʳ {μ = later^[ k ]ⓜconstantlyⓜforever} = refl

mod-assoc : {μ : Modality o p} {ρ : Modality n o} {κ : Modality m n} → (μ ⓜ ρ) ⓜ κ ≡ μ ⓜ (ρ ⓜ κ)
mod-assoc {μ = 𝟙★} = refl
mod-assoc {μ = forever} {ρ = later^[ k ]ⓜconstantly} {κ = 𝟙★} = refl
mod-assoc {μ = forever} {ρ = later^[ k ]ⓜconstantly} {κ = forever} = refl
mod-assoc {μ = forever} {ρ = later^[ k ]} {κ = later^[ l ]ⓜconstantly} = refl
mod-assoc {μ = forever} {ρ = later^[ k ]} {κ = later^[ l ]} = refl
mod-assoc {μ = forever} {ρ = later^[ k ]} {κ = later^[ l ]ⓜconstantlyⓜforever} = refl
mod-assoc {μ = forever} {ρ = later^[ k ]ⓜconstantlyⓜforever} {κ = later^[ l ]ⓜconstantly} = refl
mod-assoc {μ = forever} {ρ = later^[ k ]ⓜconstantlyⓜforever} {κ = later^[ l ]} = refl
mod-assoc {μ = forever} {ρ = later^[ k ]ⓜconstantlyⓜforever} {κ = later^[ l ]ⓜconstantlyⓜforever} = refl
mod-assoc {μ = later^[ k ]ⓜconstantly} {ρ = 𝟙★} = refl
mod-assoc {μ = later^[ k ]ⓜconstantly} {ρ = forever} {κ = later^[ l ]ⓜconstantly} = refl
mod-assoc {μ = later^[ k ]ⓜconstantly} {ρ = forever} {κ = later^[ l ]} = refl
mod-assoc {μ = later^[ k ]ⓜconstantly} {ρ = forever} {κ = later^[ l ]ⓜconstantlyⓜforever} = refl
mod-assoc {μ = later^[ k ]} {ρ = later^[ l ]ⓜconstantly} {κ = 𝟙★} = refl
mod-assoc {μ = later^[ k ]} {ρ = later^[ l ]ⓜconstantly} {κ = forever} = refl
mod-assoc {μ = later^[ k ]} {ρ = later^[ l ]} {κ = later^[ m ]ⓜconstantly} = cong later^[_]ⓜconstantly (+-assoc k l m)
mod-assoc {μ = later^[ k ]} {ρ = later^[ l ]} {κ = later^[ m ]} = cong later^[_] (+-assoc k l m)
mod-assoc {μ = later^[ k ]} {ρ = later^[ l ]} {κ = later^[ m ]ⓜconstantlyⓜforever} = cong later^[_]ⓜconstantlyⓜforever (+-assoc k l m)
mod-assoc {μ = later^[ k ]} {ρ = later^[ l ]ⓜconstantlyⓜforever} {κ = later^[ m ]ⓜconstantly} = refl
mod-assoc {μ = later^[ k ]} {ρ = later^[ l ]ⓜconstantlyⓜforever} {κ = later^[ m ]} = refl
mod-assoc {μ = later^[ k ]} {ρ = later^[ l ]ⓜconstantlyⓜforever} {κ = later^[ m ]ⓜconstantlyⓜforever} = refl
mod-assoc {μ = later^[ k ]ⓜconstantlyⓜforever} {ρ = later^[ l ]ⓜconstantly} {κ = 𝟙★} = refl
mod-assoc {μ = later^[ k ]ⓜconstantlyⓜforever} {ρ = later^[ l ]ⓜconstantly} {κ = forever} = refl
mod-assoc {μ = later^[ k ]ⓜconstantlyⓜforever} {ρ = later^[ l ]} {κ = later^[ m ]ⓜconstantly} = refl
mod-assoc {μ = later^[ k ]ⓜconstantlyⓜforever} {ρ = later^[ l ]} {κ = later^[ m ]} = refl
mod-assoc {μ = later^[ k ]ⓜconstantlyⓜforever} {ρ = later^[ l ]} {κ = later^[ m ]ⓜconstantlyⓜforever} = refl
mod-assoc {μ = later^[ k ]ⓜconstantlyⓜforever} {ρ = later^[ l ]ⓜconstantlyⓜforever} {κ = later^[ m ]ⓜconstantly} = refl
mod-assoc {μ = later^[ k ]ⓜconstantlyⓜforever} {ρ = later^[ l ]ⓜconstantlyⓜforever} {κ = later^[ m ]} = refl
mod-assoc {μ = later^[ k ]ⓜconstantlyⓜforever} {ρ = later^[ l ]ⓜconstantlyⓜforever} {κ = later^[ m ]ⓜconstantlyⓜforever} = refl

{-
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
-}

data TwoCell : (μ ρ : Modality m n) → Set where
  id𝟙★ : TwoCell 𝟙★ 𝟙★
  ltrⓜcst : k ≤ l → TwoCell later^[ k ]ⓜconstantly later^[ l ]ⓜconstantly
  id-frv : TwoCell forever forever
  ltr : k ≤ l → TwoCell later^[ k ] later^[ l ]
  ltrⓜcstⓜfrv : k ≤ l → TwoCell later^[ k ]ⓜconstantlyⓜforever later^[ l ]ⓜconstantlyⓜforever
  cstⓜfrv≤𝟙 : k ≤ l → TwoCell later^[ k ]ⓜconstantlyⓜforever later^[ l ]

id-cell : TwoCell μ μ
id-cell {μ = 𝟙★} = id𝟙★
id-cell {μ = forever} = id-frv
id-cell {μ = later^[ k ]ⓜconstantly} = ltrⓜcst ≤-refl
id-cell {μ = later^[ k ]} = ltr ≤-refl
id-cell {μ = later^[ k ]ⓜconstantlyⓜforever} = ltrⓜcstⓜfrv ≤-refl

𝟙≤later : TwoCell 𝟙 later
𝟙≤later = ltr z≤n

constantlyⓜforever≤𝟙 : TwoCell (constantly ⓜ forever) 𝟙
constantlyⓜforever≤𝟙 = cstⓜfrv≤𝟙 z≤n

infixl 6 _ⓣ-vert_
_ⓣ-vert_ : TwoCell ρ κ → TwoCell μ ρ → TwoCell μ κ
id𝟙★ ⓣ-vert β = β
ltrⓜcst l≤m ⓣ-vert ltrⓜcst k≤l = ltrⓜcst (≤-trans k≤l l≤m)
id-frv ⓣ-vert β = β
ltr l≤m ⓣ-vert ltr k≤l = ltr (≤-trans k≤l l≤m)
ltr l≤m ⓣ-vert cstⓜfrv≤𝟙 k≤l = cstⓜfrv≤𝟙 (≤-trans k≤l l≤m)
ltrⓜcstⓜfrv l≤m ⓣ-vert ltrⓜcstⓜfrv k≤l = ltrⓜcstⓜfrv (≤-trans k≤l l≤m)
cstⓜfrv≤𝟙 l≤m ⓣ-vert ltrⓜcstⓜfrv k≤l = cstⓜfrv≤𝟙 (≤-trans k≤l l≤m)

infixl 5 _ⓣ-hor_
_ⓣ-hor_ : {μ1 ρ1 : Modality n o} {μ2 ρ2 : Modality m n} →
          TwoCell μ1 ρ1 → TwoCell μ2 ρ2 → TwoCell (μ1 ⓜ μ2) (ρ1 ⓜ ρ2)
id𝟙★ ⓣ-hor β = β
ltrⓜcst k≤l ⓣ-hor id𝟙★ = ltrⓜcst k≤l
ltrⓜcst k≤l ⓣ-hor id-frv = ltrⓜcstⓜfrv k≤l
id-frv ⓣ-hor ltrⓜcst _ = id𝟙★
id-frv ⓣ-hor ltr _ = id-frv
id-frv ⓣ-hor ltrⓜcstⓜfrv _ = id-frv
id-frv ⓣ-hor cstⓜfrv≤𝟙 _ = id-frv
ltr k≤l ⓣ-hor ltrⓜcst m≤n = ltrⓜcst (+-mono-≤ k≤l m≤n)
ltr k≤l ⓣ-hor ltr m≤n = ltr (+-mono-≤ k≤l m≤n)
ltr k≤l ⓣ-hor ltrⓜcstⓜfrv m≤n = ltrⓜcstⓜfrv (+-mono-≤ k≤l m≤n)
ltr k≤l ⓣ-hor cstⓜfrv≤𝟙 m≤n = cstⓜfrv≤𝟙 (+-mono-≤ k≤l m≤n)
ltrⓜcstⓜfrv k≤l ⓣ-hor ltrⓜcst _ = ltrⓜcst k≤l
ltrⓜcstⓜfrv k≤l ⓣ-hor ltr _ = ltrⓜcstⓜfrv k≤l
ltrⓜcstⓜfrv k≤l ⓣ-hor ltrⓜcstⓜfrv _ = ltrⓜcstⓜfrv k≤l
ltrⓜcstⓜfrv k≤l ⓣ-hor cstⓜfrv≤𝟙 _ = ltrⓜcstⓜfrv k≤l
cstⓜfrv≤𝟙 k≤l ⓣ-hor ltrⓜcst _ = ltrⓜcst (≤-stepsʳ _ k≤l)
cstⓜfrv≤𝟙 k≤l ⓣ-hor ltr _ = cstⓜfrv≤𝟙 (≤-stepsʳ _ k≤l)
cstⓜfrv≤𝟙 k≤l ⓣ-hor ltrⓜcstⓜfrv _ = ltrⓜcstⓜfrv (≤-stepsʳ _ k≤l)
cstⓜfrv≤𝟙 k≤l ⓣ-hor cstⓜfrv≤𝟙 _ = cstⓜfrv≤𝟙 (≤-stepsʳ _ k≤l)
