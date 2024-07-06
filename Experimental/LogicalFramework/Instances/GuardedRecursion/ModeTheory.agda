module Experimental.LogicalFramework.Instances.GuardedRecursion.ModeTheory where

open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
  using (+-identityʳ; +-assoc; +-suc; ≤-refl; ≤-trans; +-mono-≤; m≤n⇒m≤1+n; m≤n⇒m≤n+o; m≤n⇒m≤o+n; ≤-irrelevant)
  renaming (_≟_ to _≟nat_)
open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory as M hiding (ω; ★)
import Model.CwF-Structure as M
open import Model.DRA as DRA hiding (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; TwoCell; id-cell; _ⓣ-vert_; _ⓣ-hor_)
import Applications.GuardedRecursion.Model.Modalities as M

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory



data NonTrivMode : Set where
  nt-ω : NonTrivMode

non-triv-mode-eq? : (m n : NonTrivMode) → Maybe (m ≡ n)
non-triv-mode-eq? nt-ω nt-ω = just refl

⟦_⟧non-triv-mode : NonTrivMode → BaseCategory
⟦ nt-ω ⟧non-triv-mode = M.ω

guarded-mtm : MTMode
MTMode.NonTrivMode guarded-mtm = NonTrivMode
MTMode.non-triv-mode-eq? guarded-mtm = non-triv-mode-eq?
MTMode.⟦_⟧non-triv-mode guarded-mtm = ⟦_⟧non-triv-mode

open MTMode guarded-mtm using (Mode; ★; ‵_; ⟦_⟧mode)

pattern ω = ‵ nt-ω

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

⟦_⟧non-triv-mod : NonTrivModality m n → DRA ⟦ m ⟧mode ⟦ n ⟧mode
⟦ nt-forever ⟧non-triv-mod = M.forever
⟦ later^[ k ]ⓜconstantly ⟧non-triv-mod = M.later^[ k ] ⓓ M.constantly
⟦ later^[1+ k ] ⟧non-triv-mod = M.later^[ suc k ]
⟦ later^[ k ]ⓜconstantlyⓜforever ⟧non-triv-mod = M.later^[ k ] ⓓ M.constantly ⓓ M.forever

guarded-mtμ : MTModality guarded-mtm
MTModality.NonTrivModality guarded-mtμ = NonTrivModality
MTModality.non-triv-mod-eq? guarded-mtμ = non-triv-mod-eq?
MTModality.⟦_⟧non-triv-mod guarded-mtμ = ⟦_⟧non-triv-mod

open MTModality guarded-mtμ using (Modality; ‵_; 𝟙; ⟦_⟧mod)

private variable
  μ ρ κ : Modality m n

pattern later = ‵ later^[1+ 0 ]

pattern constantly = ‵ later^[ 0 ]ⓜconstantly

pattern forever = ‵ nt-forever


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

⟦ⓜ⟧-non-triv-sound : (μ : NonTrivModality n o) (κ : NonTrivModality m n) → ⟦ μ ⓜnon-triv κ ⟧mod ≅ᵈ ⟦ μ ⟧non-triv-mod ⓓ ⟦ κ ⟧non-triv-mod
⟦ⓜ⟧-non-triv-sound nt-forever later^[ l ]ⓜconstantly =
  transᵈ (symᵈ M.forever-constantly) (
  transᵈ (symᵈ (ⓓ-congˡ _ M.forever-later^[ l ])) (
  ⓓ-assoc _ _ _))
⟦ⓜ⟧-non-triv-sound nt-forever later^[1+ l ] = symᵈ M.forever-later^[ suc l ]
⟦ⓜ⟧-non-triv-sound nt-forever later^[ l ]ⓜconstantlyⓜforever =
  transᵈ (symᵈ (𝟙-unitˡ _)) (
  transᵈ (ⓓ-congˡ _ (symᵈ (
  transᵈ (symᵈ (ⓓ-assoc _ _ _)) (
  transᵈ (ⓓ-congˡ _ M.forever-later^[ l ]) M.forever-constantly)))) (
  ⓓ-assoc _ _ _))
⟦ⓜ⟧-non-triv-sound later^[ k ]ⓜconstantly nt-forever = reflᵈ
⟦ⓜ⟧-non-triv-sound later^[1+ k ] later^[ l ]ⓜconstantly =
  transᵈ (ⓓ-congˡ _ (M.later^m+n (suc k))) (ⓓ-assoc _ _ _)
⟦ⓜ⟧-non-triv-sound later^[1+ k ] later^[1+ l ] =
  transᵈ (ⓓ-congʳ _ (M.later^m+n (suc k))) (
  transᵈ (ⓓ-congʳ _ (ⓓ-congˡ _ (M.laters-later-commute k))) (
  transᵈ (ⓓ-congʳ _ (ⓓ-assoc _ _ _)) (symᵈ (ⓓ-assoc _ _ _))))
⟦ⓜ⟧-non-triv-sound later^[1+ k ] later^[ l ]ⓜconstantlyⓜforever =
  transᵈ (ⓓ-congˡ _ (ⓓ-congˡ _ (M.later^m+n (suc k)))) (
  transᵈ (ⓓ-congˡ _ (ⓓ-assoc _ _ _)) (ⓓ-assoc _ _ _))
⟦ⓜ⟧-non-triv-sound later^[ k ]ⓜconstantlyⓜforever later^[ l ]ⓜconstantly = symᵈ (
  transᵈ (transᵈ (ⓓ-assoc _ _ _) (ⓓ-congʳ _ (
  transᵈ (symᵈ (ⓓ-assoc _ _ _)) (
  transᵈ (ⓓ-congˡ _ M.forever-later^[ l ])
  M.forever-constantly)))) (
  𝟙-unitʳ _))
⟦ⓜ⟧-non-triv-sound later^[ k ]ⓜconstantlyⓜforever later^[1+ l ] = symᵈ (
  transᵈ (ⓓ-assoc _ _ _) (ⓓ-congʳ _ (M.forever-later^[ suc l ])))
⟦ⓜ⟧-non-triv-sound later^[ k ]ⓜconstantlyⓜforever later^[ l ]ⓜconstantlyⓜforever = symᵈ (
  transᵈ (ⓓ-assoc _ _ _) (ⓓ-congʳ _ (
  transᵈ (transᵈ (symᵈ (ⓓ-assoc _ _ _)) (ⓓ-congˡ _ (
  transᵈ (symᵈ (ⓓ-assoc _ _ _)) (
  transᵈ (ⓓ-congˡ _ M.forever-later^[ l ])
  M.forever-constantly)))) (
  𝟙-unitˡ _))))

guarded-mtc : MTComposition guarded-mtm guarded-mtμ
MTComposition._ⓜnon-triv_ guarded-mtc = _ⓜnon-triv_
MTComposition.⟦ⓜ⟧-non-triv-sound guarded-mtc = ⟦ⓜ⟧-non-triv-sound

open MTComposition guarded-mtc using (_ⓜ_; ⟦ⓜ⟧-sound)


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

guarded-mtc-laws : MTCompositionLaws guarded-mtm guarded-mtμ guarded-mtc
MTCompositionLaws.mod-non-triv-assoc guarded-mtc-laws = mod-non-triv-assoc

open MTCompositionLaws guarded-mtc-laws using (mod-assoc)


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
⟦ ltrⓜcst k≤l ⟧two-cell = M.laters≤laters k≤l DRA.ⓣ-hor DRA.id-cell
⟦ id-frv ⟧two-cell = DRA.id-cell
⟦ ltr k≤l ⟧two-cell = M.laters≤laters (s≤s k≤l)
⟦ 𝟙≤ltr {k = k} ⟧two-cell = M.laters≤laters {n = suc k} z≤n
⟦ ltrⓜcstⓜfrv k≤l ⟧two-cell = (M.laters≤laters k≤l DRA.ⓣ-hor DRA.id-cell) DRA.ⓣ-hor DRA.id-cell
⟦ cstⓜfrv≤𝟙 ⟧two-cell = M.constantly∘forever≤𝟙 DRA.ⓣ-vert DRA.from (ⓓ-congˡ _ (𝟙-unitˡ _))
⟦ cstⓜfrv≤ltr k≤1+l ⟧two-cell =
  DRA.from (𝟙-unitʳ _)
  DRA.ⓣ-vert (M.laters≤laters k≤1+l DRA.ⓣ-hor M.constantly∘forever≤𝟙)
  DRA.ⓣ-vert DRA.from (ⓓ-assoc _ _ _)

guarded-mt2 : MTTwoCell guarded-mtm guarded-mtμ guarded-mtc
MTTwoCell.TwoCell guarded-mt2 = TwoCell
MTTwoCell.id-cell guarded-mt2 = id-cell
MTTwoCell._ⓣ-vert_ guarded-mt2 = _ⓣ-vert_
MTTwoCell._ⓣ-hor_ guarded-mt2 = _ⓣ-hor_
MTTwoCell.two-cell-eq? guarded-mt2 = two-cell-eq?
MTTwoCell.⟦_⟧two-cell guarded-mt2 = ⟦_⟧two-cell

open MTTwoCell guarded-mt2 using (eq-cell)


mode-is-preorder : (m : Mode) → IsPreorder ⟦ m ⟧mode
mode-is-preorder ★ = ★-is-preorder
mode-is-preorder ω = ω-is-preorder

lock-is-lifted : (μ : Modality m n) → M.IsLiftedFunctor (DRA.ctx-functor ⟦ μ ⟧mod)
lock-is-lifted 𝟙 = M.is-lifted-id
lock-is-lifted (‵ nt-forever) = M.is-lifted-lift
lock-is-lifted (‵ later^[ k ]ⓜconstantly) = M.is-lifted-lift M.ⓕ-lifted M.laters-lock-is-lifted k
lock-is-lifted (‵ later^[1+ k ]) = M.laters-lock-is-lifted (suc k)
lock-is-lifted (‵ later^[ k ]ⓜconstantlyⓜforever) =
  M.is-lifted-lift M.ⓕ-lifted (M.is-lifted-lift M.ⓕ-lifted M.laters-lock-is-lifted k)

sem-2-cell-unique : {m n : Mode} (μ ρ : Modality m n) {α β : DRA.TwoCell ⟦ μ ⟧mod ⟦ ρ ⟧mod} →
                    α ≅ᵗᶜ β
sem-2-cell-unique {n = n} μ ρ =
  transf-eq-to-cell-eq (M.lifted-functor-transf-eq (lock-is-lifted ρ)
                                                   (lock-is-lifted μ)
                                                   (preorder-nat-transf-irrelevant (mode-is-preorder n)))

⟦id-cell⟧-sound : ∀ {m n} {μ : Modality m n} → ⟦ id-cell {μ = μ} ⟧two-cell DRA.≅ᵗᶜ DRA.id-cell
⟦id-cell⟧-sound {μ = μ} = sem-2-cell-unique μ μ

⟦ⓣ-vert⟧-sound : ∀ {m n} {μ κ ρ : Modality m n}
                 (β : TwoCell κ ρ) (α : TwoCell μ κ) →
                 ⟦ β ⓣ-vert α ⟧two-cell DRA.≅ᵗᶜ ⟦ β ⟧two-cell DRA.ⓣ-vert ⟦ α ⟧two-cell
⟦ⓣ-vert⟧-sound {μ = μ} {κ} {ρ} β α = sem-2-cell-unique μ ρ

⟦ⓜ⟧-sound-natural-helper : ∀ {m n o} {μ μ' : Modality n o} {ρ ρ' : Modality m n}
                           (α : TwoCell μ μ') (β : TwoCell ρ ρ') →
                           ⟦ α ⓣ-hor β ⟧two-cell
                             DRA.≅ᵗᶜ
                           to (⟦ⓜ⟧-sound μ' ρ')
                           DRA.ⓣ-vert ((⟦ α ⟧two-cell DRA.ⓣ-hor ⟦ β ⟧two-cell)
                           DRA.ⓣ-vert from (⟦ⓜ⟧-sound μ ρ))
⟦ⓜ⟧-sound-natural-helper {μ = μ} {μ'} {ρ} {ρ'} α β = sem-2-cell-unique (μ ⓜ ρ) (μ' ⓜ ρ')

⟦ⓜ⟧-sound-natural : ∀ {m n o} {μ μ' : Modality n o} {ρ ρ' : Modality m n}
                    (α : TwoCell μ μ') (β : TwoCell ρ ρ') →
                    from (⟦ⓜ⟧-sound μ' ρ') DRA.ⓣ-vert ⟦ α ⓣ-hor β ⟧two-cell
                      DRA.≅ᵗᶜ
                    (⟦ α ⟧two-cell DRA.ⓣ-hor ⟦ β ⟧two-cell) DRA.ⓣ-vert from (⟦ⓜ⟧-sound μ ρ)
⟦ⓜ⟧-sound-natural {μ' = μ'} {ρ' = ρ'} α β =
  transᵗᶜ (ⓣ-vert-congʳ (⟦ⓜ⟧-sound-natural-helper α β)) (
  transᵗᶜ (symᵗᶜ ⓣ-vert-assoc) (
  transᵗᶜ (ⓣ-vert-congˡ (isoʳ (⟦ⓜ⟧-sound μ' ρ')))
  ⓣ-vert-unitˡ))


⟦associator⟧-helper : ∀ {m n o p} {μ : Modality o p} {ρ : Modality n o} (κ : Modality m n) →
                      ⟦ eq-cell (mod-assoc κ) ⟧two-cell
                        DRA.≅ᵗᶜ
                      to (⟦ⓜ⟧-sound μ (ρ ⓜ κ)) DRA.ⓣ-vert
                      ((DRA.id-cell DRA.ⓣ-hor to (⟦ⓜ⟧-sound ρ κ))
                      DRA.ⓣ-vert
                      ((from (DRA.ⓓ-assoc ⟦ μ ⟧mod ⟦ ρ ⟧mod ⟦ κ ⟧mod)
                      DRA.ⓣ-vert (from (⟦ⓜ⟧-sound μ ρ) DRA.ⓣ-hor DRA.id-cell))
                      DRA.ⓣ-vert from (⟦ⓜ⟧-sound (μ ⓜ ρ) κ)))
⟦associator⟧-helper {μ = μ} {ρ} κ = sem-2-cell-unique ((μ ⓜ ρ) ⓜ κ) (μ ⓜ (ρ ⓜ κ))

⟦associator⟧ : ∀ {m n o p} {μ : Modality o p} {ρ : Modality n o} (κ : Modality m n) →
               ((DRA.id-cell DRA.ⓣ-hor from (⟦ⓜ⟧-sound ρ κ))
               DRA.ⓣ-vert from (⟦ⓜ⟧-sound μ (ρ ⓜ κ)))
               DRA.ⓣ-vert ⟦ eq-cell (mod-assoc κ) ⟧two-cell
                 DRA.≅ᵗᶜ
               (from (DRA.ⓓ-assoc ⟦ μ ⟧mod ⟦ ρ ⟧mod ⟦ κ ⟧mod)
               DRA.ⓣ-vert (from (⟦ⓜ⟧-sound μ ρ) DRA.ⓣ-hor DRA.id-cell))
               DRA.ⓣ-vert from (⟦ⓜ⟧-sound (μ ⓜ ρ) κ)
⟦associator⟧ {μ = μ} {ρ} κ =
  transᵗᶜ (ⓣ-vert-congʳ (⟦associator⟧-helper κ)) (
  transᵗᶜ (transᵗᶜ ⓣ-vert-assoc (ⓣ-vert-congʳ (symᵗᶜ ⓣ-vert-assoc))) (
  transᵗᶜ (ⓣ-vert-congʳ (transᵗᶜ (ⓣ-vert-congˡ (isoʳ (⟦ⓜ⟧-sound μ (ρ ⓜ κ)))) ⓣ-vert-unitˡ)) (
  transᵗᶜ (symᵗᶜ ⓣ-vert-assoc) (
  transᵗᶜ (ⓣ-vert-congˡ (transᵗᶜ (symᵗᶜ 2-cell-interchange) (transᵗᶜ (ⓣ-hor-cong ⓣ-vert-unitˡ (isoʳ (⟦ⓜ⟧-sound ρ κ))) ⓣ-hor-id)))
  ⓣ-vert-unitˡ))))

guarded-mt2-laws : MTTwoCellLaws guarded-mtm guarded-mtμ guarded-mtc guarded-mtc-laws guarded-mt2
MTTwoCellLaws.⟦id-cell⟧-sound guarded-mt2-laws {μ = μ} = ⟦id-cell⟧-sound {μ = μ}
MTTwoCellLaws.⟦ⓣ-vert⟧-sound guarded-mt2-laws = ⟦ⓣ-vert⟧-sound
MTTwoCellLaws.⟦ⓜ⟧-sound-natural guarded-mt2-laws = ⟦ⓜ⟧-sound-natural
MTTwoCellLaws.⟦associator⟧ guarded-mt2-laws = ⟦associator⟧


guarded-mt : ModeTheory
ModeTheory.mtm guarded-mt = guarded-mtm
ModeTheory.mtμ guarded-mt = guarded-mtμ
ModeTheory.mtc guarded-mt = guarded-mtc
ModeTheory.mtc-laws guarded-mt = guarded-mtc-laws
ModeTheory.mt2 guarded-mt = guarded-mt2
ModeTheory.mt2-laws guarded-mt = guarded-mt2-laws
