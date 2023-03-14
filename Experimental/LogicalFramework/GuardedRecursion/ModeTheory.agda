-- Code to be reused later to implement a mode theory for guarded
-- recursion. Is not supposed to typecheck right now.

module Experimental.LogicalFramework.MSTT.ModeTheory where

open import Data.Nat
open import Data.Nat.Properties
  using (+-identityʳ; +-assoc; +-suc; ≤-refl; ≤-trans; +-mono-≤; ≤-step; ≤-stepsʳ; ≤-stepsˡ)
open import Relation.Binary.PropositionalEquality


data Mode : Set where
  ★ ω : Mode

private variable
  m n o p : Mode
  k l : ℕ


data NonTrivModality : Mode → Mode → Set where
  nt-forever : NonTrivModality ω ★
  later^[_]ⓜconstantly : ℕ → NonTrivModality ★ ω
  later^[1+_] : ℕ → NonTrivModality ω ω
  later^[_]ⓜconstantlyⓜforever : ℕ → NonTrivModality ω ω

-- A modality is either the unit modality 𝟙 or a non-trivial modality
-- described above. This treatment allows for some more definitional
-- equalities (e.g. the interpretation of the unit modality is
-- definitionally the semantic unit modality, and 𝟙 is definitionally
-- a left unit of modality composition ⓜ).
data Modality : Mode → Mode → Set where
  𝟙 : Modality m m
  non-triv : NonTrivModality m n → Modality m n

mod-dom mod-cod : Modality m n → Mode
mod-dom {m} μ = m
mod-cod {_} {n} μ = n

private variable
  μ ρ κ : Modality m n


later : Modality ω ω
later = non-triv later^[1+ 0 ]

{-# DISPLAY non-triv (later^[1+_] 0) = later #-}

constantly : Modality ★ ω
constantly = non-triv later^[ 0 ]ⓜconstantly

{-# DISPLAY non-triv (later^[_]ⓜconstantly 0) = constantly #-}

forever : Modality ω ★
forever = non-triv nt-forever

{-# DISPLAY non-triv nt-forever = forever #-}

_ⓜnon-triv_ : NonTrivModality n o → NonTrivModality m n → Modality m o
nt-forever ⓜnon-triv later^[ k ]ⓜconstantly = 𝟙
nt-forever ⓜnon-triv later^[1+ k ] = forever
nt-forever ⓜnon-triv later^[ k ]ⓜconstantlyⓜforever = forever
later^[ k ]ⓜconstantly ⓜnon-triv nt-forever = non-triv later^[ k ]ⓜconstantlyⓜforever
later^[1+ k ] ⓜnon-triv later^[ l ]ⓜconstantly = non-triv later^[ 1 + (k + l) ]ⓜconstantly
later^[1+ k ] ⓜnon-triv later^[1+ l ] = non-triv later^[1+ 1 + (k + l) ]
later^[1+ k ] ⓜnon-triv later^[ l ]ⓜconstantlyⓜforever = non-triv later^[ 1 + (k + l) ]ⓜconstantlyⓜforever
later^[ k ]ⓜconstantlyⓜforever ⓜnon-triv later^[ l ]ⓜconstantly = non-triv later^[ k ]ⓜconstantly
later^[ k ]ⓜconstantlyⓜforever ⓜnon-triv later^[1+ l ] = non-triv later^[ k ]ⓜconstantlyⓜforever
later^[ k ]ⓜconstantlyⓜforever ⓜnon-triv later^[ l ]ⓜconstantlyⓜforever = non-triv later^[ k ]ⓜconstantlyⓜforever

_ⓜ_ : Modality n o → Modality m n → Modality m o
𝟙 ⓜ ρ = ρ
non-triv μ ⓜ 𝟙 = non-triv μ
non-triv μ ⓜ non-triv ρ = μ ⓜnon-triv ρ

mod-unitˡ : {μ : Modality m n} → 𝟙 ⓜ μ ≡ μ
mod-unitˡ  = refl

mod-unitʳ : {μ : Modality m n} → μ ⓜ 𝟙 ≡ μ
mod-unitʳ {μ = 𝟙} = refl
mod-unitʳ {μ = non-triv μ'} = refl

mod-non-triv-assoc : (μ : NonTrivModality o p) (ρ : NonTrivModality n o) (κ : NonTrivModality m n) →
                     (μ ⓜnon-triv ρ) ⓜ non-triv κ ≡ non-triv μ ⓜ (ρ ⓜnon-triv κ)
mod-non-triv-assoc nt-forever later^[ k ]ⓜconstantly nt-forever = refl
mod-non-triv-assoc nt-forever later^[1+ k ] later^[ l ]ⓜconstantly = refl
mod-non-triv-assoc nt-forever later^[1+ k ] later^[1+ l ] = refl
mod-non-triv-assoc nt-forever later^[1+ k ] later^[ l ]ⓜconstantlyⓜforever = refl
mod-non-triv-assoc nt-forever later^[ k ]ⓜconstantlyⓜforever later^[ l ]ⓜconstantly = refl
mod-non-triv-assoc nt-forever later^[ k ]ⓜconstantlyⓜforever later^[1+ l ] = refl
mod-non-triv-assoc nt-forever later^[ k ]ⓜconstantlyⓜforever later^[ l ]ⓜconstantlyⓜforever = refl
mod-non-triv-assoc later^[ k ]ⓜconstantly nt-forever later^[ l ]ⓜconstantly = refl
mod-non-triv-assoc later^[ k ]ⓜconstantly nt-forever later^[1+ l ] = refl
mod-non-triv-assoc later^[ k ]ⓜconstantly nt-forever later^[ l ]ⓜconstantlyⓜforever = refl
mod-non-triv-assoc later^[1+ k ] later^[ l ]ⓜconstantly nt-forever = refl
mod-non-triv-assoc later^[1+ k ] later^[1+ l ] later^[ m ]ⓜconstantly =
  cong (λ x → non-triv later^[ suc x ]ⓜconstantly) (trans (cong suc (+-assoc k l m)) (sym (+-suc k (l + m))))
mod-non-triv-assoc later^[1+ k ] later^[1+ l ] later^[1+ m ] =
  cong (λ x → non-triv later^[1+ suc x ]) (trans (cong suc (+-assoc k l m)) (sym (+-suc k (l + m))))
mod-non-triv-assoc later^[1+ k ] later^[1+ l ] later^[ m ]ⓜconstantlyⓜforever =
  cong (λ x → non-triv later^[ suc x ]ⓜconstantlyⓜforever) (trans (cong suc (+-assoc k l m)) (sym (+-suc k (l + m))))
mod-non-triv-assoc later^[1+ k ] later^[ l ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantly = refl
mod-non-triv-assoc later^[1+ k ] later^[ l ]ⓜconstantlyⓜforever later^[1+ m ] = refl
mod-non-triv-assoc later^[1+ k ] later^[ l ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantlyⓜforever = refl
mod-non-triv-assoc later^[ k ]ⓜconstantlyⓜforever later^[ l ]ⓜconstantly nt-forever = refl
mod-non-triv-assoc later^[ k ]ⓜconstantlyⓜforever later^[1+ l ] later^[ m ]ⓜconstantly = refl
mod-non-triv-assoc later^[ k ]ⓜconstantlyⓜforever later^[1+ l ] later^[1+ m ] = refl
mod-non-triv-assoc later^[ k ]ⓜconstantlyⓜforever later^[1+ l ] later^[ m ]ⓜconstantlyⓜforever = refl
mod-non-triv-assoc later^[ k ]ⓜconstantlyⓜforever later^[ l ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantly = refl
mod-non-triv-assoc later^[ k ]ⓜconstantlyⓜforever later^[ l ]ⓜconstantlyⓜforever later^[1+ m ] = refl
mod-non-triv-assoc later^[ k ]ⓜconstantlyⓜforever later^[ l ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantlyⓜforever = refl

mod-assoc : (μ : Modality o p) {ρ : Modality n o} {κ : Modality m n} → (μ ⓜ ρ) ⓜ κ ≡ μ ⓜ (ρ ⓜ κ)
mod-assoc 𝟙 = refl
mod-assoc (non-triv μ') {ρ = 𝟙} = refl
mod-assoc (non-triv μ') {ρ = non-triv ρ'} {κ = 𝟙} = mod-unitʳ
mod-assoc (non-triv μ') {ρ = non-triv ρ'} {κ = non-triv κ'} = mod-non-triv-assoc μ' ρ' κ'

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
  id𝟙 : ∀ {m} → TwoCell (𝟙 {m}) 𝟙
  ltrⓜcst : k ≤ l → TwoCell (non-triv later^[ k ]ⓜconstantly) (non-triv later^[ l ]ⓜconstantly)
  id-frv : TwoCell forever forever
  ltr : k ≤ l → TwoCell (non-triv later^[1+ k ]) (non-triv later^[1+ l ])
  𝟙≤ltr :  TwoCell 𝟙 (non-triv later^[1+ k ])
  ltrⓜcstⓜfrv : k ≤ l → TwoCell (non-triv later^[ k ]ⓜconstantlyⓜforever) (non-triv later^[ l ]ⓜconstantlyⓜforever)
  cstⓜfrv≤𝟙 : TwoCell (non-triv later^[ 0 ]ⓜconstantlyⓜforever) 𝟙
  cstⓜfrv≤ltr : k ≤ 1 + l → TwoCell (non-triv later^[ k ]ⓜconstantlyⓜforever) (non-triv later^[1+ l ])

id-cell : {μ : Modality m n} → TwoCell μ μ
id-cell {μ = 𝟙} = id𝟙
id-cell {μ = non-triv nt-forever} = id-frv
id-cell {μ = non-triv later^[ k ]ⓜconstantly} = ltrⓜcst ≤-refl
id-cell {μ = non-triv later^[1+ k ]} = ltr ≤-refl
id-cell {μ = non-triv later^[ k ]ⓜconstantlyⓜforever} = ltrⓜcstⓜfrv ≤-refl

eq-cell : {μ ρ : Modality m n} → μ ≡ ρ → TwoCell μ ρ
eq-cell refl = id-cell

transp-cellʳ : {μ ρ ρ' : Modality m n} → ρ ≡ ρ' → TwoCell μ ρ → TwoCell μ ρ'
transp-cellʳ refl α = α

transp-cellˡ : {μ μ' ρ : Modality m n} → μ ≡ μ' → TwoCell μ ρ → TwoCell μ' ρ
transp-cellˡ refl α = α

infixl 6 _ⓣ-vert_
_ⓣ-vert_ : TwoCell ρ κ → TwoCell μ ρ → TwoCell μ κ
id𝟙 ⓣ-vert β = β
ltrⓜcst l≤m ⓣ-vert ltrⓜcst k≤l = ltrⓜcst (≤-trans k≤l l≤m)
id-frv ⓣ-vert β = β
ltr l≤m ⓣ-vert ltr k≤l = ltr (≤-trans k≤l l≤m)
ltr l≤m ⓣ-vert 𝟙≤ltr = 𝟙≤ltr
ltr l≤m ⓣ-vert cstⓜfrv≤ltr k≤l = cstⓜfrv≤ltr (≤-trans k≤l (s≤s l≤m))
𝟙≤ltr ⓣ-vert id𝟙 = 𝟙≤ltr
𝟙≤ltr ⓣ-vert cstⓜfrv≤𝟙 = cstⓜfrv≤ltr z≤n
ltrⓜcstⓜfrv l≤m ⓣ-vert ltrⓜcstⓜfrv k≤l = ltrⓜcstⓜfrv (≤-trans k≤l l≤m)
cstⓜfrv≤𝟙 ⓣ-vert ltrⓜcstⓜfrv z≤n = cstⓜfrv≤𝟙
cstⓜfrv≤ltr l≤m ⓣ-vert ltrⓜcstⓜfrv k≤l = cstⓜfrv≤ltr (≤-trans k≤l l≤m)

infixl 5 _ⓣ-hor_
_ⓣ-hor_ : {μ1 ρ1 : Modality n o} {μ2 ρ2 : Modality m n} →
          TwoCell μ1 ρ1 → TwoCell μ2 ρ2 → TwoCell (μ1 ⓜ μ2) (ρ1 ⓜ ρ2)
id𝟙 ⓣ-hor β = β
ltrⓜcst k≤l ⓣ-hor id𝟙 = ltrⓜcst k≤l
ltrⓜcst k≤l ⓣ-hor id-frv = ltrⓜcstⓜfrv k≤l
id-frv ⓣ-hor id𝟙 = id-frv
id-frv ⓣ-hor ltrⓜcst _ = id𝟙
id-frv ⓣ-hor ltr _ = id-frv
id-frv ⓣ-hor 𝟙≤ltr = id-frv
id-frv ⓣ-hor ltrⓜcstⓜfrv _ = id-frv
id-frv ⓣ-hor cstⓜfrv≤𝟙 = id-frv
id-frv ⓣ-hor cstⓜfrv≤ltr _ = id-frv
ltr k≤l ⓣ-hor id𝟙 = ltr k≤l
ltr k≤l ⓣ-hor ltrⓜcst m≤n = ltrⓜcst (s≤s (+-mono-≤ k≤l m≤n))
ltr k≤l ⓣ-hor ltr m≤n = ltr (s≤s (+-mono-≤ k≤l m≤n))
ltr k≤l ⓣ-hor 𝟙≤ltr = ltr (≤-step (≤-stepsʳ _ k≤l))
ltr k≤l ⓣ-hor ltrⓜcstⓜfrv m≤n = ltrⓜcstⓜfrv (s≤s (+-mono-≤ k≤l m≤n))
ltr {_} {l} k≤l ⓣ-hor cstⓜfrv≤𝟙 = cstⓜfrv≤ltr (s≤s (subst (_≤ l) (sym (+-identityʳ _)) k≤l))
ltr {k} k≤l ⓣ-hor cstⓜfrv≤ltr {m} m≤1+n = cstⓜfrv≤ltr (s≤s (subst (k + m ≤_) (+-suc _ _) (+-mono-≤ k≤l m≤1+n)))
𝟙≤ltr ⓣ-hor id𝟙 = 𝟙≤ltr
𝟙≤ltr ⓣ-hor ltrⓜcst k≤l = ltrⓜcst (≤-stepsˡ _ k≤l)
𝟙≤ltr ⓣ-hor ltr k≤l = ltr (≤-stepsˡ _ k≤l)
𝟙≤ltr ⓣ-hor 𝟙≤ltr = 𝟙≤ltr
𝟙≤ltr ⓣ-hor ltrⓜcstⓜfrv k≤l = ltrⓜcstⓜfrv (≤-stepsˡ _ k≤l)
𝟙≤ltr ⓣ-hor cstⓜfrv≤𝟙 = cstⓜfrv≤ltr z≤n
𝟙≤ltr ⓣ-hor cstⓜfrv≤ltr {k} {l} k≤1+l = cstⓜfrv≤ltr (≤-step (subst (λ x → k ≤ x) (+-suc _ l) (≤-stepsˡ _ k≤1+l)))
ltrⓜcstⓜfrv k≤l ⓣ-hor id𝟙 = ltrⓜcstⓜfrv k≤l
ltrⓜcstⓜfrv k≤l ⓣ-hor ltrⓜcst _ = ltrⓜcst k≤l
ltrⓜcstⓜfrv k≤l ⓣ-hor ltr _ = ltrⓜcstⓜfrv k≤l
ltrⓜcstⓜfrv k≤l ⓣ-hor 𝟙≤ltr = ltrⓜcstⓜfrv k≤l
ltrⓜcstⓜfrv k≤l ⓣ-hor ltrⓜcstⓜfrv _ = ltrⓜcstⓜfrv k≤l
ltrⓜcstⓜfrv k≤l ⓣ-hor cstⓜfrv≤𝟙 = ltrⓜcstⓜfrv k≤l
ltrⓜcstⓜfrv k≤l ⓣ-hor cstⓜfrv≤ltr _ = ltrⓜcstⓜfrv k≤l
cstⓜfrv≤𝟙 ⓣ-hor id𝟙 = cstⓜfrv≤𝟙
cstⓜfrv≤𝟙 ⓣ-hor ltrⓜcst _ = ltrⓜcst z≤n
cstⓜfrv≤𝟙 ⓣ-hor ltr _ = cstⓜfrv≤ltr z≤n
cstⓜfrv≤𝟙 ⓣ-hor 𝟙≤ltr = cstⓜfrv≤ltr z≤n
cstⓜfrv≤𝟙 ⓣ-hor ltrⓜcstⓜfrv _ = ltrⓜcstⓜfrv z≤n
cstⓜfrv≤𝟙 ⓣ-hor cstⓜfrv≤𝟙 = cstⓜfrv≤𝟙
cstⓜfrv≤𝟙 ⓣ-hor cstⓜfrv≤ltr _ = cstⓜfrv≤ltr z≤n
cstⓜfrv≤ltr k≤l ⓣ-hor id𝟙 = cstⓜfrv≤ltr k≤l
cstⓜfrv≤ltr k≤l ⓣ-hor ltrⓜcst _ = ltrⓜcst (≤-stepsʳ _ k≤l)
cstⓜfrv≤ltr k≤l ⓣ-hor ltr _ = cstⓜfrv≤ltr (≤-step (≤-stepsʳ _ k≤l))
cstⓜfrv≤ltr k≤l ⓣ-hor 𝟙≤ltr = cstⓜfrv≤ltr (≤-step (≤-stepsʳ _ k≤l))
cstⓜfrv≤ltr k≤l ⓣ-hor ltrⓜcstⓜfrv _ = ltrⓜcstⓜfrv (≤-stepsʳ _ k≤l)
cstⓜfrv≤ltr k≤l ⓣ-hor cstⓜfrv≤𝟙 = cstⓜfrv≤ltr k≤l
cstⓜfrv≤ltr k≤l ⓣ-hor cstⓜfrv≤ltr x = cstⓜfrv≤ltr (≤-step (≤-stepsʳ _ k≤l))
