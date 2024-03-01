module Experimental.LogicalFramework.Instances.GuardedRecursion.ModeTheory where

open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
  using (+-identityʳ; +-assoc; +-suc; ≤-refl; ≤-trans; +-mono-≤; m≤n⇒m≤1+n; m≤n⇒m≤n+o; m≤n⇒m≤o+n; ≤-irrelevant)
  renaming (_≟_ to _≟nat_)
open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory as M using (BaseCategory)
open import Model.DRA as DRA hiding (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; TwoCell; id-cell; _ⓣ-vert_; _ⓣ-hor_)
import Applications.GuardedRecursion.Model.Modalities as M

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory



data Mode : Set where
  ★ ω : Mode

mode-eq? : (m n : Mode) → Maybe (m ≡ n)
mode-eq? ★ ★ = just refl
mode-eq? ★ ω = nothing
mode-eq? ω ★ = nothing
mode-eq? ω ω = just refl

private variable
  m n o p : Mode
  k l : ℕ


data NonTrivModality : Mode → Mode → Set where
  nt-forever : NonTrivModality ω ★
  later^[_]ⓜconstantly : ℕ → NonTrivModality ★ ω
  later^[1+_] : ℕ → NonTrivModality ω ω
  later^[_]ⓜconstantlyⓜforever : ℕ → NonTrivModality ω ω

non-triv-mod-eq? : (μ κ : NonTrivModality m n) → Maybe (μ ≡ κ)
non-triv-mod-eq? nt-forever nt-forever = just refl
non-triv-mod-eq? later^[ k ]ⓜconstantly later^[ l ]ⓜconstantly = map (cong later^[_]ⓜconstantly) (decToMaybe (k ≟nat l))
non-triv-mod-eq? later^[1+ k ] later^[1+ l ] = map (cong later^[1+_]) (decToMaybe (k ≟nat l))
non-triv-mod-eq? later^[1+ k ] later^[ l ]ⓜconstantlyⓜforever = nothing
non-triv-mod-eq? later^[ k ]ⓜconstantlyⓜforever later^[1+ l ] = nothing
non-triv-mod-eq? later^[ k ]ⓜconstantlyⓜforever later^[ l ]ⓜconstantlyⓜforever =
  map (cong later^[_]ⓜconstantlyⓜforever) (decToMaybe (k ≟nat l))

⟦_⟧mode : Mode → BaseCategory
⟦ ★ ⟧mode = M.★
⟦ ω ⟧mode = M.ω

⟦_⟧non-triv-mod : NonTrivModality m n → DRA ⟦ m ⟧mode ⟦ n ⟧mode
⟦ nt-forever ⟧non-triv-mod = M.forever
⟦ later^[ zero  ]ⓜconstantly ⟧non-triv-mod = M.constantly
⟦ later^[ suc k ]ⓜconstantly ⟧non-triv-mod = M.later ⓓ ⟦ later^[ k ]ⓜconstantly ⟧non-triv-mod
⟦ later^[1+ zero  ] ⟧non-triv-mod = M.later
⟦ later^[1+ suc k ] ⟧non-triv-mod = M.later ⓓ ⟦ later^[1+ k ] ⟧non-triv-mod
⟦ later^[ zero  ]ⓜconstantlyⓜforever ⟧non-triv-mod = M.constantly ⓓ M.forever
⟦ later^[ suc k ]ⓜconstantlyⓜforever ⟧non-triv-mod = M.later ⓓ ⟦ later^[ k ]ⓜconstantlyⓜforever ⟧non-triv-mod


guarded-mtb : MTBasis
MTBasis.Mode guarded-mtb = Mode
MTBasis.NonTrivModality guarded-mtb = NonTrivModality
MTBasis.mode-eq? guarded-mtb = mode-eq?
MTBasis.non-triv-mod-eq? guarded-mtb = non-triv-mod-eq?
MTBasis.⟦_⟧mode guarded-mtb = ⟦_⟧mode
MTBasis.⟦_⟧non-triv-mod guarded-mtb = ⟦_⟧non-triv-mod

open MTBasis guarded-mtb using (Modality; ‵_; 𝟙; ⟦_⟧mod)

private variable
  μ ρ κ : Modality m n


later : Modality ω ω
later = ‵ later^[1+ 0 ]

{-# DISPLAY ‵_ (later^[1+_] 0) = later #-}

constantly : Modality ★ ω
constantly = ‵ later^[ 0 ]ⓜconstantly

{-# DISPLAY ‵_ (later^[_]ⓜconstantly 0) = constantly #-}

forever : Modality ω ★
forever = ‵ nt-forever

{-# DISPLAY ‵_ nt-forever = forever #-}


_ⓜnon-triv_ : NonTrivModality n o → NonTrivModality m n → Modality m o
nt-forever ⓜnon-triv later^[ k ]ⓜconstantly = 𝟙
nt-forever ⓜnon-triv later^[1+ k ] = forever
nt-forever ⓜnon-triv later^[ k ]ⓜconstantlyⓜforever = forever
later^[ k ]ⓜconstantly ⓜnon-triv nt-forever = ‵ later^[ k ]ⓜconstantlyⓜforever
later^[1+ k ] ⓜnon-triv later^[ l ]ⓜconstantly = ‵ later^[ 1 + (k + l) ]ⓜconstantly
later^[1+ k ] ⓜnon-triv later^[1+ l ] = ‵ later^[1+ 1 + (k + l) ]
later^[1+ k ] ⓜnon-triv later^[ l ]ⓜconstantlyⓜforever = ‵ later^[ 1 + (k + l) ]ⓜconstantlyⓜforever
later^[ k ]ⓜconstantlyⓜforever ⓜnon-triv later^[ l ]ⓜconstantly = ‵ later^[ k ]ⓜconstantly
later^[ k ]ⓜconstantlyⓜforever ⓜnon-triv later^[1+ l ] = ‵ later^[ k ]ⓜconstantlyⓜforever
later^[ k ]ⓜconstantlyⓜforever ⓜnon-triv later^[ l ]ⓜconstantlyⓜforever = ‵ later^[ k ]ⓜconstantlyⓜforever

⟦ⓜ⟧-sound : (μ : NonTrivModality n o) (κ : NonTrivModality m n) → ⟦ μ ⓜnon-triv κ ⟧mod ≅ᵈ ⟦ μ ⟧non-triv-mod ⓓ ⟦ κ ⟧non-triv-mod
⟦ⓜ⟧-sound nt-forever later^[ zero  ]ⓜconstantly = symᵈ M.forever-constantly
⟦ⓜ⟧-sound nt-forever later^[ suc k ]ⓜconstantly =
  transᵈ (transᵈ (⟦ⓜ⟧-sound (nt-forever) (later^[ k ]ⓜconstantly))
                 (ⓓ-congˡ _ (symᵈ M.forever-later)))
         (ⓓ-assoc _ _ _)
⟦ⓜ⟧-sound nt-forever later^[1+ zero  ] = symᵈ M.forever-later
⟦ⓜ⟧-sound nt-forever later^[1+ suc k ] =
  transᵈ (transᵈ (⟦ⓜ⟧-sound (nt-forever) (later^[1+ k ]))
                 (ⓓ-congˡ _ (symᵈ M.forever-later)))
         (ⓓ-assoc _ _ _)
⟦ⓜ⟧-sound nt-forever later^[ zero  ]ⓜconstantlyⓜforever =
  transᵈ (transᵈ (symᵈ (DRA.𝟙-unitˡ _)) (ⓓ-congˡ _ (symᵈ M.forever-constantly))) (ⓓ-assoc _ _ _)
⟦ⓜ⟧-sound nt-forever later^[ suc k ]ⓜconstantlyⓜforever =
  transᵈ (transᵈ (⟦ⓜ⟧-sound (nt-forever) (later^[ k ]ⓜconstantlyⓜforever))
                 (ⓓ-congˡ _ (symᵈ M.forever-later)))
         (ⓓ-assoc _ _ _)
⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantly nt-forever = reflᵈ
⟦ⓜ⟧-sound later^[ suc k ]ⓜconstantly nt-forever =
  transᵈ (ⓓ-congʳ _ (⟦ⓜ⟧-sound (later^[ k ]ⓜconstantly) nt-forever)) (symᵈ (ⓓ-assoc _ _ _))
⟦ⓜ⟧-sound later^[1+ zero  ] later^[ l ]ⓜconstantly = reflᵈ
⟦ⓜ⟧-sound later^[1+ suc k ] later^[ l ]ⓜconstantly =
  transᵈ (ⓓ-congʳ _ (⟦ⓜ⟧-sound (later^[1+ k ]) (later^[ l ]ⓜconstantly))) (symᵈ (ⓓ-assoc _ _ _))
⟦ⓜ⟧-sound later^[1+ zero  ] later^[1+ l ] = reflᵈ
⟦ⓜ⟧-sound later^[1+ suc k ] later^[1+ l ] =
  transᵈ (ⓓ-congʳ _ (⟦ⓜ⟧-sound (later^[1+ k ]) (later^[1+ l ]))) (symᵈ (ⓓ-assoc _ _ _))
⟦ⓜ⟧-sound later^[1+ zero  ] later^[ l ]ⓜconstantlyⓜforever = reflᵈ
⟦ⓜ⟧-sound later^[1+ suc k ] later^[ l ]ⓜconstantlyⓜforever =
  transᵈ (ⓓ-congʳ _ (⟦ⓜ⟧-sound (later^[1+ k ]) (later^[ l ]ⓜconstantlyⓜforever))) (symᵈ (ⓓ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ zero ]ⓜconstantlyⓜforever later^[ zero  ]ⓜconstantly =
  symᵈ (transᵈ (transᵈ (ⓓ-assoc _ _ _) (ⓓ-congʳ _ M.forever-constantly)) (DRA.𝟙-unitʳ _))
⟦ⓜ⟧-sound later^[ zero ]ⓜconstantlyⓜforever later^[ suc l ]ⓜconstantly =
  transᵈ (transᵈ (⟦ⓜ⟧-sound (later^[ zero ]ⓜconstantlyⓜforever) (later^[ l ]ⓜconstantly))
                 (ⓓ-congˡ _ (transᵈ (ⓓ-congʳ _ (symᵈ M.forever-later)) (symᵈ (ⓓ-assoc _ _ _)))))
         (ⓓ-assoc _ _ _)
⟦ⓜ⟧-sound later^[ suc k ]ⓜconstantlyⓜforever later^[ l ]ⓜconstantly =
  transᵈ (ⓓ-congʳ _ (⟦ⓜ⟧-sound (later^[ k ]ⓜconstantlyⓜforever) (later^[ l ]ⓜconstantly))) (symᵈ (ⓓ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ zero ]ⓜconstantlyⓜforever later^[1+ zero  ] =
  symᵈ (transᵈ (ⓓ-assoc _ _ _) (ⓓ-congʳ _ M.forever-later))
⟦ⓜ⟧-sound later^[ zero ]ⓜconstantlyⓜforever later^[1+ suc l ] =
  transᵈ (⟦ⓜ⟧-sound (later^[ zero  ]ⓜconstantlyⓜforever) (later^[1+ l ]))
         (transᵈ (ⓓ-congˡ _ (transᵈ (ⓓ-congʳ _ (symᵈ M.forever-later)) (symᵈ (ⓓ-assoc _ _ _)))) (ⓓ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ suc k ]ⓜconstantlyⓜforever later^[1+ l ] =
  transᵈ (ⓓ-congʳ _ (⟦ⓜ⟧-sound (later^[ k ]ⓜconstantlyⓜforever) (later^[1+ l ]))) (symᵈ (ⓓ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ zero ]ⓜconstantlyⓜforever later^[ zero  ]ⓜconstantlyⓜforever =
  transᵈ (ⓓ-congʳ _ (symᵈ (transᵈ (ⓓ-congˡ _ M.forever-constantly) (𝟙-unitˡ _))))
         (transᵈ (ⓓ-congʳ _ (ⓓ-assoc _ _ _)) (symᵈ (ⓓ-assoc _ _ _)))
⟦ⓜ⟧-sound later^[ zero ]ⓜconstantlyⓜforever later^[ suc l ]ⓜconstantlyⓜforever =
  transᵈ (⟦ⓜ⟧-sound (later^[ zero  ]ⓜconstantlyⓜforever) (later^[ l ]ⓜconstantlyⓜforever))
         (transᵈ (ⓓ-congˡ _ (transᵈ (ⓓ-congʳ _ (symᵈ M.forever-later)) (symᵈ (ⓓ-assoc _ _ _)))) (ⓓ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ suc k ]ⓜconstantlyⓜforever later^[ l ]ⓜconstantlyⓜforever =
  transᵈ (ⓓ-congʳ _ (⟦ⓜ⟧-sound (later^[ k ]ⓜconstantlyⓜforever) (later^[ l ]ⓜconstantlyⓜforever))) (symᵈ (ⓓ-assoc _ _ _))


guarded-mtc : MTComposition guarded-mtb
MTComposition._ⓜnon-triv_ guarded-mtc = _ⓜnon-triv_
MTComposition.⟦ⓜ⟧-non-triv-sound guarded-mtc = ⟦ⓜ⟧-sound

open MTComposition guarded-mtc using (_ⓜ_)


mod-non-triv-assoc : (μ : NonTrivModality o p) (ρ : NonTrivModality n o) (κ : NonTrivModality m n) →
                     (μ ⓜnon-triv ρ) ⓜ ‵ κ ≡ ‵ μ ⓜ (ρ ⓜnon-triv κ)
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
  cong (λ x → ‵ later^[ suc x ]ⓜconstantly) (trans (cong suc (+-assoc k l m)) (sym (+-suc k (l + m))))
mod-non-triv-assoc later^[1+ k ] later^[1+ l ] later^[1+ m ] =
  cong (λ x → ‵ later^[1+ suc x ]) (trans (cong suc (+-assoc k l m)) (sym (+-suc k (l + m))))
mod-non-triv-assoc later^[1+ k ] later^[1+ l ] later^[ m ]ⓜconstantlyⓜforever =
  cong (λ x → ‵ later^[ suc x ]ⓜconstantlyⓜforever) (trans (cong suc (+-assoc k l m)) (sym (+-suc k (l + m))))
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

guarded-mtcl : MTCompositionLaws guarded-mtb guarded-mtc
MTCompositionLaws.mod-non-triv-assoc guarded-mtcl = mod-non-triv-assoc


data TwoCell : (μ ρ : Modality m n) → Set where
  id𝟙 : ∀ {m} → TwoCell (𝟙 {m}) 𝟙
  ltrⓜcst : k ≤ l → TwoCell (‵ later^[ k ]ⓜconstantly) (‵ later^[ l ]ⓜconstantly)
  id-frv : TwoCell forever forever
  ltr : k ≤ l → TwoCell (‵ later^[1+ k ]) (‵ later^[1+ l ])
  𝟙≤ltr :  TwoCell 𝟙 (‵ later^[1+ k ])
  ltrⓜcstⓜfrv : k ≤ l → TwoCell (‵ later^[ k ]ⓜconstantlyⓜforever) (‵ later^[ l ]ⓜconstantlyⓜforever)
  cstⓜfrv≤𝟙 : TwoCell (‵ later^[ 0 ]ⓜconstantlyⓜforever) 𝟙
  cstⓜfrv≤ltr : k ≤ 1 + l → TwoCell (‵ later^[ k ]ⓜconstantlyⓜforever) (‵ later^[1+ l ])

id-cell : {μ : Modality m n} → TwoCell μ μ
id-cell {μ = 𝟙} = id𝟙
id-cell {μ = ‵ nt-forever} = id-frv
id-cell {μ = ‵ later^[ k ]ⓜconstantly} = ltrⓜcst ≤-refl
id-cell {μ = ‵ later^[1+ k ]} = ltr ≤-refl
id-cell {μ = ‵ later^[ k ]ⓜconstantlyⓜforever} = ltrⓜcstⓜfrv ≤-refl

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
α               ⓣ-hor id𝟙 = α
id𝟙             ⓣ-hor ltrⓜcst k≤l = ltrⓜcst k≤l
id-frv          ⓣ-hor ltrⓜcst _ = id𝟙
ltr k≤l         ⓣ-hor ltrⓜcst m≤n = ltrⓜcst (s≤s (+-mono-≤ k≤l m≤n))
𝟙≤ltr           ⓣ-hor ltrⓜcst k≤l = ltrⓜcst (m≤n⇒m≤o+n _ k≤l)
ltrⓜcstⓜfrv k≤l ⓣ-hor ltrⓜcst _ = ltrⓜcst k≤l
cstⓜfrv≤𝟙       ⓣ-hor ltrⓜcst _ = ltrⓜcst z≤n
cstⓜfrv≤ltr k≤l ⓣ-hor ltrⓜcst _ = ltrⓜcst (m≤n⇒m≤n+o _ k≤l)
id𝟙             ⓣ-hor id-frv = id-frv
ltrⓜcst k≤l     ⓣ-hor id-frv = ltrⓜcstⓜfrv k≤l
id𝟙             ⓣ-hor ltr k≤l = ltr k≤l
id-frv          ⓣ-hor ltr _ = id-frv
ltr k≤l         ⓣ-hor ltr m≤n = ltr (s≤s (+-mono-≤ k≤l m≤n))
𝟙≤ltr           ⓣ-hor ltr k≤l = ltr (m≤n⇒m≤o+n _ k≤l)
ltrⓜcstⓜfrv k≤l ⓣ-hor ltr _ = ltrⓜcstⓜfrv k≤l
cstⓜfrv≤𝟙       ⓣ-hor ltr _ = cstⓜfrv≤ltr z≤n
cstⓜfrv≤ltr k≤l ⓣ-hor ltr _ = cstⓜfrv≤ltr (m≤n⇒m≤1+n (m≤n⇒m≤n+o _ k≤l))
id𝟙             ⓣ-hor 𝟙≤ltr = 𝟙≤ltr
id-frv          ⓣ-hor 𝟙≤ltr = id-frv
ltr k≤l         ⓣ-hor 𝟙≤ltr = ltr (m≤n⇒m≤1+n (m≤n⇒m≤n+o _ k≤l))
𝟙≤ltr           ⓣ-hor 𝟙≤ltr = 𝟙≤ltr
ltrⓜcstⓜfrv k≤l ⓣ-hor 𝟙≤ltr = ltrⓜcstⓜfrv k≤l
cstⓜfrv≤𝟙       ⓣ-hor 𝟙≤ltr = cstⓜfrv≤ltr z≤n
cstⓜfrv≤ltr k≤l ⓣ-hor 𝟙≤ltr = cstⓜfrv≤ltr (m≤n⇒m≤1+n (m≤n⇒m≤n+o _ k≤l))
id𝟙             ⓣ-hor ltrⓜcstⓜfrv k≤l = ltrⓜcstⓜfrv k≤l
id-frv          ⓣ-hor ltrⓜcstⓜfrv _ = id-frv
ltr k≤l         ⓣ-hor ltrⓜcstⓜfrv m≤n = ltrⓜcstⓜfrv (s≤s (+-mono-≤ k≤l m≤n))
𝟙≤ltr           ⓣ-hor ltrⓜcstⓜfrv k≤l = ltrⓜcstⓜfrv (m≤n⇒m≤o+n _ k≤l)
ltrⓜcstⓜfrv k≤l ⓣ-hor ltrⓜcstⓜfrv _ = ltrⓜcstⓜfrv k≤l
cstⓜfrv≤𝟙       ⓣ-hor ltrⓜcstⓜfrv _ = ltrⓜcstⓜfrv z≤n
cstⓜfrv≤ltr k≤l ⓣ-hor ltrⓜcstⓜfrv _ = ltrⓜcstⓜfrv (m≤n⇒m≤n+o _ k≤l)
id𝟙             ⓣ-hor cstⓜfrv≤𝟙 = cstⓜfrv≤𝟙
id-frv          ⓣ-hor cstⓜfrv≤𝟙 = id-frv
ltr {_} {l} k≤l ⓣ-hor cstⓜfrv≤𝟙 = cstⓜfrv≤ltr (s≤s (subst (_≤ l) (sym (+-identityʳ _)) k≤l))
𝟙≤ltr           ⓣ-hor cstⓜfrv≤𝟙 = cstⓜfrv≤ltr z≤n
ltrⓜcstⓜfrv k≤l ⓣ-hor cstⓜfrv≤𝟙 = ltrⓜcstⓜfrv k≤l
cstⓜfrv≤𝟙       ⓣ-hor cstⓜfrv≤𝟙 = cstⓜfrv≤𝟙
cstⓜfrv≤ltr k≤l ⓣ-hor cstⓜfrv≤𝟙 = cstⓜfrv≤ltr k≤l
id𝟙             ⓣ-hor cstⓜfrv≤ltr k≤l = cstⓜfrv≤ltr k≤l
id-frv          ⓣ-hor cstⓜfrv≤ltr _ = id-frv
ltr {k} k≤l     ⓣ-hor cstⓜfrv≤ltr {m} m≤1+n = cstⓜfrv≤ltr (s≤s (subst (k + m ≤_) (+-suc _ _) (+-mono-≤ k≤l m≤1+n)))
𝟙≤ltr           ⓣ-hor cstⓜfrv≤ltr {k} {l} k≤1+l = cstⓜfrv≤ltr (m≤n⇒m≤1+n (subst (λ x → k ≤ x) (+-suc _ l) (m≤n⇒m≤o+n _ k≤1+l)))
ltrⓜcstⓜfrv k≤l ⓣ-hor cstⓜfrv≤ltr _ = ltrⓜcstⓜfrv k≤l
cstⓜfrv≤𝟙       ⓣ-hor cstⓜfrv≤ltr _ = cstⓜfrv≤ltr z≤n
cstⓜfrv≤ltr k≤l ⓣ-hor cstⓜfrv≤ltr x = cstⓜfrv≤ltr (m≤n⇒m≤1+n (m≤n⇒m≤n+o _ k≤l))

two-cell-eq? : (α β : TwoCell μ ρ) → Maybe (α ≡ β)
two-cell-eq? id𝟙 id𝟙 = just refl
two-cell-eq? (ltrⓜcst k≤l) (ltrⓜcst k≤l') = just (cong ltrⓜcst (≤-irrelevant k≤l k≤l'))
two-cell-eq? id-frv id-frv = just refl
two-cell-eq? (ltr k≤l) (ltr k≤l') = just (cong ltr (≤-irrelevant k≤l k≤l'))
two-cell-eq? 𝟙≤ltr 𝟙≤ltr = just refl
two-cell-eq? (ltrⓜcstⓜfrv k≤l) (ltrⓜcstⓜfrv k≤l') = just (cong ltrⓜcstⓜfrv (≤-irrelevant k≤l k≤l'))
two-cell-eq? cstⓜfrv≤𝟙 cstⓜfrv≤𝟙 = just refl
two-cell-eq? (cstⓜfrv≤ltr k≤l) (cstⓜfrv≤ltr k≤l') = just (cong cstⓜfrv≤ltr (≤-irrelevant k≤l k≤l'))

⟦_⟧two-cell : TwoCell μ κ → DRA.TwoCell ⟦ μ ⟧mod ⟦ κ ⟧mod
⟦ id𝟙 ⟧two-cell = DRA.id-cell
⟦ ltrⓜcst {l = zero } z≤n ⟧two-cell = DRA.id-cell
⟦ ltrⓜcst {l = suc l} z≤n ⟧two-cell = (M.𝟙≤later DRA.ⓣ-hor ⟦ ltrⓜcst {l = l} z≤n ⟧two-cell) DRA.ⓣ-vert from (symᵈ (DRA.𝟙-unitˡ _))
⟦ ltrⓜcst (s≤s k≤l) ⟧two-cell = DRA.id-cell DRA.ⓣ-hor ⟦ ltrⓜcst k≤l ⟧two-cell
⟦ id-frv ⟧two-cell = DRA.id-cell
⟦ ltr {l = zero } z≤n ⟧two-cell = DRA.id-cell
⟦ ltr {l = suc l} z≤n ⟧two-cell = (M.𝟙≤later DRA.ⓣ-hor ⟦ ltr {l = l} z≤n ⟧two-cell) DRA.ⓣ-vert from (symᵈ (DRA.𝟙-unitˡ _))
⟦ ltr (s≤s k≤l) ⟧two-cell = DRA.id-cell DRA.ⓣ-hor ⟦ ltr k≤l ⟧two-cell
⟦ 𝟙≤ltr {k = zero } ⟧two-cell = M.𝟙≤later
⟦ 𝟙≤ltr {k = suc k} ⟧two-cell = (M.𝟙≤later DRA.ⓣ-hor ⟦ 𝟙≤ltr {k = k} ⟧two-cell) DRA.ⓣ-vert from (symᵈ (DRA.𝟙-unitˡ _))
⟦ ltrⓜcstⓜfrv {l = zero } z≤n ⟧two-cell = DRA.id-cell
⟦ ltrⓜcstⓜfrv {l = suc l} z≤n ⟧two-cell = (M.𝟙≤later DRA.ⓣ-hor ⟦ ltrⓜcstⓜfrv {l = l} z≤n ⟧two-cell) DRA.ⓣ-vert from (symᵈ (DRA.𝟙-unitˡ _))
⟦ ltrⓜcstⓜfrv (s≤s k≤l) ⟧two-cell = DRA.id-cell DRA.ⓣ-hor ⟦ ltrⓜcstⓜfrv k≤l ⟧two-cell
⟦ cstⓜfrv≤𝟙 ⟧two-cell = M.constantly∘forever≤𝟙
⟦ cstⓜfrv≤ltr {l = zero } z≤n ⟧two-cell = M.𝟙≤later DRA.ⓣ-vert M.constantly∘forever≤𝟙
⟦ cstⓜfrv≤ltr {l = suc l} z≤n ⟧two-cell = (M.𝟙≤later DRA.ⓣ-hor ⟦ cstⓜfrv≤ltr {l = l} z≤n ⟧two-cell) DRA.ⓣ-vert from (symᵈ (DRA.𝟙-unitˡ _))
⟦ cstⓜfrv≤ltr {l = zero } (s≤s z≤n)   ⟧two-cell = from (DRA.𝟙-unitʳ _) DRA.ⓣ-vert (DRA.id-cell DRA.ⓣ-hor M.constantly∘forever≤𝟙)
⟦ cstⓜfrv≤ltr {l = suc l} (s≤s k≤1+l) ⟧two-cell = DRA.id-cell DRA.ⓣ-hor ⟦ cstⓜfrv≤ltr {l = l} k≤1+l ⟧two-cell

guarded-mt2c : MTTwoCell guarded-mtb guarded-mtc
MTTwoCell.TwoCell guarded-mt2c = TwoCell
MTTwoCell.id-cell guarded-mt2c = id-cell
MTTwoCell._ⓣ-vert_ guarded-mt2c = _ⓣ-vert_
MTTwoCell._ⓣ-hor_ guarded-mt2c = _ⓣ-hor_
MTTwoCell.two-cell-eq? guarded-mt2c = two-cell-eq?
MTTwoCell.⟦_⟧two-cell guarded-mt2c = ⟦_⟧two-cell


guarded-mt : ModeTheory
ModeTheory.mtb guarded-mt = guarded-mtb
ModeTheory.mtc guarded-mt = guarded-mtc
ModeTheory.mtc-laws guarded-mt = guarded-mtcl
ModeTheory.mt2 guarded-mt = guarded-mt2c
