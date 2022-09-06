module Experimental.LogicalFramework.STT.Interpretation.ModeTheory where

open import Data.Nat

open import Model.BaseCategory as M using (BaseCategory)
open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.Modality as M using (_≅ᵐ_)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Discrete as M

import Applications.GuardedRecursion.Model.Modalities as M

open import Experimental.LogicalFramework.STT.ModeTheory


private variable
  m n o : Mode
  μ κ : Modality m n


⟦_⟧mode : Mode → BaseCategory
⟦ ★ ⟧mode = M.★
⟦ ω ⟧mode = M.ω

⟦_⟧mod : Modality m n → M.Modality ⟦ m ⟧mode ⟦ n ⟧mode
⟦ 𝟙★ ⟧mod = M.𝟙
⟦ forever ⟧mod = M.forever
⟦ later^[ zero  ]ⓜconstantly ⟧mod = M.constantly
⟦ later^[ suc n ]ⓜconstantly ⟧mod = M.later M.ⓜ ⟦ later^[ n ]ⓜconstantly ⟧mod
⟦ later^[ zero  ] ⟧mod = M.𝟙
⟦ later^[ suc n ] ⟧mod = M.later M.ⓜ ⟦ later^[ n ] ⟧mod
⟦ later^[ zero  ]ⓜconstantlyⓜforever ⟧mod = M.constantly M.ⓜ M.forever
⟦ later^[ suc n ]ⓜconstantlyⓜforever ⟧mod = M.later M.ⓜ ⟦ later^[ n ]ⓜconstantlyⓜforever ⟧mod

⟦𝟙⟧-sound : ∀ {m} → ⟦ 𝟙 {m} ⟧mod ≅ᵐ M.𝟙
⟦𝟙⟧-sound {★} = M.≅ᵐ-refl
⟦𝟙⟧-sound {ω} = M.≅ᵐ-refl

⟦ⓜ⟧-sound : (μ : Modality n o) (κ : Modality m n) → ⟦ μ ⓜ κ ⟧mod ≅ᵐ ⟦ μ ⟧mod M.ⓜ ⟦ κ ⟧mod
⟦ⓜ⟧-sound 𝟙★ κ = M.≅ᵐ-sym (M.𝟙-identityˡ _)
⟦ⓜ⟧-sound forever later^[ zero  ]ⓜconstantly = M.≅ᵐ-sym M.forever-constantly
⟦ⓜ⟧-sound forever later^[ suc n ]ⓜconstantly =
  M.≅ᵐ-trans (M.≅ᵐ-trans (⟦ⓜ⟧-sound forever later^[ n ]ⓜconstantly)
                         (M.ⓜ-congʳ _ (M.≅ᵐ-sym M.forever-later)))
             (M.ⓜ-assoc _ _ _)
⟦ⓜ⟧-sound forever later^[ zero  ] = M.≅ᵐ-sym (M.𝟙-identityʳ _)
⟦ⓜ⟧-sound forever later^[ suc n ] =
  M.≅ᵐ-trans (M.≅ᵐ-trans (⟦ⓜ⟧-sound forever later^[ n ])
                         (M.ⓜ-congʳ _ (M.≅ᵐ-sym M.forever-later)))
             (M.ⓜ-assoc _ _ _)
⟦ⓜ⟧-sound forever later^[ zero  ]ⓜconstantlyⓜforever =
  M.≅ᵐ-trans (M.≅ᵐ-trans (M.≅ᵐ-sym (M.𝟙-identityˡ _)) (M.ⓜ-congʳ _ (M.≅ᵐ-sym M.forever-constantly))) (M.ⓜ-assoc _ _ _)
⟦ⓜ⟧-sound forever later^[ suc n ]ⓜconstantlyⓜforever =
  M.≅ᵐ-trans (M.≅ᵐ-trans (⟦ⓜ⟧-sound forever later^[ n ]ⓜconstantlyⓜforever)
                         (M.ⓜ-congʳ _ (M.≅ᵐ-sym M.forever-later)))
             (M.ⓜ-assoc _ _ _)
⟦ⓜ⟧-sound later^[ n ]ⓜconstantly 𝟙★ = M.≅ᵐ-sym (M.𝟙-identityʳ _)
⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantly forever = M.≅ᵐ-refl
⟦ⓜ⟧-sound later^[ suc n ]ⓜconstantly forever =
  M.≅ᵐ-trans (M.ⓜ-congˡ _ (⟦ⓜ⟧-sound later^[ n ]ⓜconstantly forever)) (M.≅ᵐ-sym (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ zero  ] later^[ m ]ⓜconstantly = M.≅ᵐ-sym (M.𝟙-identityˡ _)
⟦ⓜ⟧-sound later^[ suc n ] later^[ m ]ⓜconstantly =
  M.≅ᵐ-trans (M.ⓜ-congˡ _ (⟦ⓜ⟧-sound later^[ n ] later^[ m ]ⓜconstantly)) (M.≅ᵐ-sym (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ zero  ] later^[ m ] = M.≅ᵐ-sym (M.𝟙-identityˡ _)
⟦ⓜ⟧-sound later^[ suc n ] later^[ m ] =
  M.≅ᵐ-trans (M.ⓜ-congˡ _ (⟦ⓜ⟧-sound later^[ n ] later^[ m ])) (M.≅ᵐ-sym (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ zero  ] later^[ m ]ⓜconstantlyⓜforever = M.≅ᵐ-sym (M.𝟙-identityˡ _)
⟦ⓜ⟧-sound later^[ suc n ] later^[ m ]ⓜconstantlyⓜforever =
  M.≅ᵐ-trans (M.ⓜ-congˡ _ (⟦ⓜ⟧-sound later^[ n ] later^[ m ]ⓜconstantlyⓜforever)) (M.≅ᵐ-sym (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ zero  ]ⓜconstantly =
  M.≅ᵐ-sym (M.≅ᵐ-trans (M.≅ᵐ-trans (M.ⓜ-assoc _ _ _) (M.ⓜ-congˡ _ M.forever-constantly)) (M.𝟙-identityʳ _))
⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ suc m ]ⓜconstantly =
  M.≅ᵐ-trans (M.≅ᵐ-trans (⟦ⓜ⟧-sound later^[ zero ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantly)
                         (M.ⓜ-congʳ _ (M.≅ᵐ-trans (M.ⓜ-congˡ _ (M.≅ᵐ-sym M.forever-later)) (M.≅ᵐ-sym (M.ⓜ-assoc _ _ _)))))
             (M.ⓜ-assoc _ _ _)
⟦ⓜ⟧-sound later^[ suc n ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantly =
  M.≅ᵐ-trans (M.ⓜ-congˡ _ (⟦ⓜ⟧-sound later^[ n ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantly)) (M.≅ᵐ-sym (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ zero  ] = M.≅ᵐ-sym (M.𝟙-identityʳ _)
⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ suc m ] =
  M.≅ᵐ-trans (⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ m ])
             (M.≅ᵐ-trans (M.ⓜ-congʳ _ (M.≅ᵐ-trans (M.ⓜ-congˡ _ (M.≅ᵐ-sym M.forever-later)) (M.≅ᵐ-sym (M.ⓜ-assoc _ _ _)))) (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ suc n ]ⓜconstantlyⓜforever later^[ m ] =
  M.≅ᵐ-trans (M.ⓜ-congˡ _ (⟦ⓜ⟧-sound later^[ n ]ⓜconstantlyⓜforever later^[ m ])) (M.≅ᵐ-sym (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ zero  ]ⓜconstantlyⓜforever =
  M.≅ᵐ-trans (M.ⓜ-congˡ _ (M.≅ᵐ-sym (M.≅ᵐ-trans (M.ⓜ-congʳ _ M.forever-constantly) (M.𝟙-identityˡ _))))
             (M.≅ᵐ-trans (M.ⓜ-congˡ _ (M.ⓜ-assoc _ _ _)) (M.≅ᵐ-sym (M.ⓜ-assoc _ _ _)))
⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ suc m ]ⓜconstantlyⓜforever =
  M.≅ᵐ-trans (⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantlyⓜforever)
             (M.≅ᵐ-trans (M.ⓜ-congʳ _ (M.≅ᵐ-trans (M.ⓜ-congˡ _ (M.≅ᵐ-sym M.forever-later)) (M.≅ᵐ-sym (M.ⓜ-assoc _ _ _)))) (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ suc n ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantlyⓜforever =
  M.≅ᵐ-trans (M.ⓜ-congˡ _ (⟦ⓜ⟧-sound later^[ n ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantlyⓜforever)) (M.≅ᵐ-sym (M.ⓜ-assoc _ _ _))

⟦_⟧two-cell : TwoCell μ κ → M.TwoCell ⟦ μ ⟧mod ⟦ κ ⟧mod
⟦ id-cell ⟧two-cell = M.id-cell
⟦ α ⓣ-vert β ⟧two-cell = ⟦ α ⟧two-cell M.ⓣ-vert ⟦ β ⟧two-cell
⟦ _ⓣ-hor_ {μ1 = μ1} {ρ1 = ρ1} {μ2 = μ2} {ρ2 = ρ2} α β ⟧two-cell =
  M.≅ᵐ-to-2-cell (M.≅ᵐ-sym (⟦ⓜ⟧-sound ρ1 ρ2)) M.ⓣ-vert (⟦ α ⟧two-cell M.ⓣ-hor ⟦ β ⟧two-cell) M.ⓣ-vert M.≅ᵐ-to-2-cell (⟦ⓜ⟧-sound μ1 μ2)
⟦ 𝟙≤later ⟧two-cell = M.≅ᵐ-to-2-cell (M.≅ᵐ-sym (M.𝟙-identityʳ _)) M.ⓣ-vert M.𝟙≤later
⟦ constantly∘forever≤𝟙 ⟧two-cell = M.constantly∘forever≤𝟙
