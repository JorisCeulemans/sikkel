module Experimental.LogicalFramework.Instances.UnaryParametricity.ModeTheory where

open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory as M hiding (★; ↑)
open import Model.CwF-Structure as M using (eq)
open import Model.DRA as DRA hiding (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; TwoCell; id-cell; _ⓣ-vert_; _ⓣ-hor_)

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory

open import Applications.UnaryParametricity.Model as M hiding (π-cell)


data NonTrivMode : Set where
  nt-↑ : NonTrivMode

non-triv-mode-eq? : (m n : NonTrivMode) → Maybe (m ≡ n)
non-triv-mode-eq? nt-↑ nt-↑ = just refl

⟦_⟧non-triv-mode : NonTrivMode → BaseCategory
⟦ nt-↑ ⟧non-triv-mode = M.↑

unary-param-mtm : MTMode
MTMode.NonTrivMode unary-param-mtm = NonTrivMode
MTMode.non-triv-mode-eq? unary-param-mtm = non-triv-mode-eq?
MTMode.⟦_⟧non-triv-mode unary-param-mtm = ⟦_⟧non-triv-mode

open MTMode unary-param-mtm using (Mode; ★; ‵_; ⟦_⟧mode)

pattern ↑ = ‵ nt-↑

private variable
  m n o p : Mode


data NonTrivModality : Mode → Mode → Set where
  nt-forget nt-Σ : NonTrivModality ↑ ★

non-triv-mod-eq? : (μ κ : NonTrivModality m n) → Maybe (μ ≡ κ)
non-triv-mod-eq? nt-forget nt-forget = just refl
non-triv-mod-eq? nt-forget nt-Σ = nothing
non-triv-mod-eq? nt-Σ nt-forget = nothing
non-triv-mod-eq? nt-Σ nt-Σ = just refl

⟦_⟧non-triv-mod : NonTrivModality m n → DRA ⟦ m ⟧mode ⟦ n ⟧mode
⟦ nt-forget ⟧non-triv-mod = forget-dra
⟦ nt-Σ ⟧non-triv-mod = Σ-dra

unary-param-mtμ : MTModality unary-param-mtm
MTModality.NonTrivModality unary-param-mtμ = NonTrivModality
MTModality.non-triv-mod-eq? unary-param-mtμ = non-triv-mod-eq?
MTModality.⟦_⟧non-triv-mod unary-param-mtμ = ⟦_⟧non-triv-mod

open MTModality unary-param-mtμ using (Modality; ‵_; 𝟙; ⟦_⟧mod)

private variable
  μ ρ κ : Modality m n

pattern forget = ‵ nt-forget

pattern Σ = ‵ nt-Σ


_ⓜnon-triv_ : NonTrivModality n o → NonTrivModality m n → Modality m o
nt-forget ⓜnon-triv ()
nt-Σ ⓜnon-triv ()

⟦ⓜ⟧-non-triv-sound : (μ : NonTrivModality n o) (κ : NonTrivModality m n) → ⟦ μ ⓜnon-triv κ ⟧mod ≅ᵈ ⟦ μ ⟧non-triv-mod ⓓ ⟦ κ ⟧non-triv-mod
⟦ⓜ⟧-non-triv-sound nt-forget ()
⟦ⓜ⟧-non-triv-sound nt-Σ ()

unary-param-mtc : MTComposition unary-param-mtm unary-param-mtμ
MTComposition._ⓜnon-triv_ unary-param-mtc = _ⓜnon-triv_
MTComposition.⟦ⓜ⟧-non-triv-sound unary-param-mtc = ⟦ⓜ⟧-non-triv-sound

open MTComposition unary-param-mtc using (_ⓜ_; ⟦ⓜ⟧-sound)


mod-non-triv-assoc : (μ : NonTrivModality o p) (ρ : NonTrivModality n o) (κ : NonTrivModality m n) →
                     (μ ⓜnon-triv ρ) ⓜ ‵ κ ≡ ‵ μ ⓜ (ρ ⓜnon-triv κ)
mod-non-triv-assoc nt-forget () κ
mod-non-triv-assoc nt-Σ () κ

unary-param-mtc-laws : MTCompositionLaws unary-param-mtm unary-param-mtμ unary-param-mtc
MTCompositionLaws.mod-non-triv-assoc unary-param-mtc-laws = mod-non-triv-assoc

open MTCompositionLaws unary-param-mtc-laws using (mod-assoc)


data TwoCell : (μ ρ : Modality m n) → Set where
  idcl : TwoCell μ μ
  π-cell : TwoCell Σ forget

id-cell : {μ : Modality m n} → TwoCell μ μ
id-cell = idcl

infixl 6 _ⓣ-vert_
_ⓣ-vert_ : TwoCell ρ κ → TwoCell μ ρ → TwoCell μ κ
idcl ⓣ-vert β = β
π-cell ⓣ-vert idcl = π-cell

infixl 5 _ⓣ-hor_
_ⓣ-hor_ : {μ1 ρ1 : Modality n o} {μ2 ρ2 : Modality m n} →
          TwoCell μ1 ρ1 → TwoCell μ2 ρ2 → TwoCell (μ1 ⓜ μ2) (ρ1 ⓜ ρ2)
_ⓣ-hor_ idcl idcl = idcl
_ⓣ-hor_ {μ1 = 𝟙} idcl π-cell = π-cell
_ⓣ-hor_ {μ2 = 𝟙} π-cell idcl = π-cell

two-cell-eq? : (α β : TwoCell μ ρ) → Maybe (α ≡ β)
two-cell-eq? idcl idcl = just refl
two-cell-eq? π-cell π-cell = just refl

⟦_⟧two-cell : TwoCell μ κ → DRA.TwoCell ⟦ μ ⟧mod ⟦ κ ⟧mod
⟦ idcl ⟧two-cell = DRA.id-cell
⟦ π-cell ⟧two-cell = M.π-cell

unary-param-mt2 : MTTwoCell unary-param-mtm unary-param-mtμ unary-param-mtc
MTTwoCell.TwoCell unary-param-mt2 = TwoCell
MTTwoCell.id-cell unary-param-mt2 = id-cell
MTTwoCell._ⓣ-vert_ unary-param-mt2 = _ⓣ-vert_
MTTwoCell._ⓣ-hor_ unary-param-mt2 = _ⓣ-hor_
MTTwoCell.two-cell-eq? unary-param-mt2 = two-cell-eq?
MTTwoCell.⟦_⟧two-cell unary-param-mt2 = ⟦_⟧two-cell

open MTTwoCell unary-param-mt2 using (eq-cell)


⟦id-cell⟧-sound : ∀ {m n} {μ : Modality m n} → ⟦ id-cell {μ = μ} ⟧two-cell DRA.≅ᵗᶜ DRA.id-cell
⟦id-cell⟧-sound = DRA.reflᵗᶜ

⟦ⓣ-vert⟧-sound : ∀ {m n} {μ κ ρ : Modality m n}
                 (β : TwoCell κ ρ) (α : TwoCell μ κ) →
                 ⟦ β ⓣ-vert α ⟧two-cell DRA.≅ᵗᶜ ⟦ β ⟧two-cell DRA.ⓣ-vert ⟦ α ⟧two-cell
⟦ⓣ-vert⟧-sound idcl α = symᵗᶜ DRA.ⓣ-vert-unitˡ
⟦ⓣ-vert⟧-sound π-cell idcl = symᵗᶜ DRA.ⓣ-vert-unitʳ

⟦ⓜ⟧-sound-natural : ∀ {m n o} {μ μ' : Modality n o} {ρ ρ' : Modality m n}
                    (α : TwoCell μ μ') (β : TwoCell ρ ρ') →
                    from (⟦ⓜ⟧-sound μ' ρ')
                    DRA.ⓣ-vert ⟦ α ⓣ-hor β ⟧two-cell
                      DRA.≅ᵗᶜ
                    (⟦ α ⟧two-cell DRA.ⓣ-hor ⟦ β ⟧two-cell)
                    DRA.ⓣ-vert from (⟦ⓜ⟧-sound μ ρ)
⟦ⓜ⟧-sound-natural idcl idcl = transᵗᶜ ⓣ-vert-unitʳ (symᵗᶜ (transᵗᶜ (ⓣ-vert-congˡ ⓣ-hor-id) ⓣ-vert-unitˡ))
⟦ⓜ⟧-sound-natural {μ = 𝟙} idcl π-cell = symᵗᶜ (𝟙-unitˡ-natural-to _)
⟦ⓜ⟧-sound-natural {ρ = 𝟙} π-cell idcl = symᵗᶜ (𝟙-unitʳ-natural-to _)


⟦associator⟧ : ∀ {m n o p} {μ : Modality o p} {ρ : Modality n o} (κ : Modality m n) →
               ((DRA.id-cell DRA.ⓣ-hor from (⟦ⓜ⟧-sound ρ κ))
               DRA.ⓣ-vert from (⟦ⓜ⟧-sound μ (ρ ⓜ κ)))
               DRA.ⓣ-vert ⟦ eq-cell (mod-assoc κ) ⟧two-cell
                 DRA.≅ᵗᶜ
               (from (DRA.ⓓ-assoc ⟦ μ ⟧mod ⟦ ρ ⟧mod ⟦ κ ⟧mod)
               DRA.ⓣ-vert (from (⟦ⓜ⟧-sound μ ρ) DRA.ⓣ-hor DRA.id-cell))
               DRA.ⓣ-vert from (⟦ⓜ⟧-sound (μ ⓜ ρ) κ)
eq (key-subst-eq (⟦associator⟧ {μ = 𝟙} {ρ = 𝟙} 𝟙)) _ = refl
eq (key-subst-eq (⟦associator⟧ {μ = 𝟙} {ρ = 𝟙} (‵ x))) _ = refl
eq (key-subst-eq (⟦associator⟧ {μ = 𝟙} {ρ = forget} 𝟙)) {x} γ = eq always-false-subst-id {x} γ
eq (key-subst-eq (⟦associator⟧ {μ = 𝟙} {ρ = Σ} 𝟙)) _ = refl
eq (key-subst-eq (⟦associator⟧ {μ = forget} {ρ = 𝟙} 𝟙)) _ = refl
eq (key-subst-eq (⟦associator⟧ {μ = Σ} {ρ = 𝟙} 𝟙)) _ = refl

unary-param-mt2-laws : MTTwoCellLaws unary-param-mtm unary-param-mtμ unary-param-mtc unary-param-mtc-laws unary-param-mt2
MTTwoCellLaws.⟦id-cell⟧-sound unary-param-mt2-laws {μ = μ} = ⟦id-cell⟧-sound {μ = μ}
MTTwoCellLaws.⟦ⓣ-vert⟧-sound unary-param-mt2-laws = ⟦ⓣ-vert⟧-sound
MTTwoCellLaws.⟦ⓜ⟧-sound-natural unary-param-mt2-laws = ⟦ⓜ⟧-sound-natural
MTTwoCellLaws.⟦associator⟧ unary-param-mt2-laws = ⟦associator⟧


unary-param-mt : ModeTheory
ModeTheory.mtm unary-param-mt = unary-param-mtm
ModeTheory.mtμ unary-param-mt = unary-param-mtμ
ModeTheory.mtc unary-param-mt = unary-param-mtc
ModeTheory.mtc-laws unary-param-mt = unary-param-mtc-laws
ModeTheory.mt2 unary-param-mt = unary-param-mt2
ModeTheory.mt2-laws unary-param-mt = unary-param-mt2-laws
