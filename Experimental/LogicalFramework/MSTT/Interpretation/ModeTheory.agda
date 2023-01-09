module Experimental.LogicalFramework.MSTT.Interpretation.ModeTheory where

open import Data.Nat

open import Model.BaseCategory as M using (BaseCategory)
open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.Modality as M using (_≅ᵐ_)

import Applications.GuardedRecursion.Model.Modalities as M

open import Experimental.LogicalFramework.MSTT.ModeTheory


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
⟦𝟙⟧-sound {★} = M.reflᵐ
⟦𝟙⟧-sound {ω} = M.reflᵐ

⟦ⓜ⟧-sound : (μ : Modality n o) (κ : Modality m n) → ⟦ μ ⓜ κ ⟧mod ≅ᵐ ⟦ μ ⟧mod M.ⓜ ⟦ κ ⟧mod
⟦ⓜ⟧-sound 𝟙★ κ = M.symᵐ (M.𝟙-identityˡ _)
⟦ⓜ⟧-sound forever later^[ zero  ]ⓜconstantly = M.symᵐ M.forever-constantly
⟦ⓜ⟧-sound forever later^[ suc n ]ⓜconstantly =
  M.transᵐ (M.transᵐ (⟦ⓜ⟧-sound forever later^[ n ]ⓜconstantly)
                     (M.ⓜ-congʳ _ (M.symᵐ M.forever-later)))
           (M.ⓜ-assoc _ _ _)
⟦ⓜ⟧-sound forever later^[ zero  ] = M.symᵐ (M.𝟙-identityʳ _)
⟦ⓜ⟧-sound forever later^[ suc n ] =
  M.transᵐ (M.transᵐ (⟦ⓜ⟧-sound forever later^[ n ])
                     (M.ⓜ-congʳ _ (M.symᵐ M.forever-later)))
           (M.ⓜ-assoc _ _ _)
⟦ⓜ⟧-sound forever later^[ zero  ]ⓜconstantlyⓜforever =
  M.transᵐ (M.transᵐ (M.symᵐ (M.𝟙-identityˡ _)) (M.ⓜ-congʳ _ (M.symᵐ M.forever-constantly))) (M.ⓜ-assoc _ _ _)
⟦ⓜ⟧-sound forever later^[ suc n ]ⓜconstantlyⓜforever =
  M.transᵐ (M.transᵐ (⟦ⓜ⟧-sound forever later^[ n ]ⓜconstantlyⓜforever)
                     (M.ⓜ-congʳ _ (M.symᵐ M.forever-later)))
           (M.ⓜ-assoc _ _ _)
⟦ⓜ⟧-sound later^[ n ]ⓜconstantly 𝟙★ = M.symᵐ (M.𝟙-identityʳ _)
⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantly forever = M.reflᵐ
⟦ⓜ⟧-sound later^[ suc n ]ⓜconstantly forever =
  M.transᵐ (M.ⓜ-congˡ _ (⟦ⓜ⟧-sound later^[ n ]ⓜconstantly forever)) (M.symᵐ (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ zero  ] later^[ m ]ⓜconstantly = M.symᵐ (M.𝟙-identityˡ _)
⟦ⓜ⟧-sound later^[ suc n ] later^[ m ]ⓜconstantly =
  M.transᵐ (M.ⓜ-congˡ _ (⟦ⓜ⟧-sound later^[ n ] later^[ m ]ⓜconstantly)) (M.symᵐ (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ zero  ] later^[ m ] = M.symᵐ (M.𝟙-identityˡ _)
⟦ⓜ⟧-sound later^[ suc n ] later^[ m ] =
  M.transᵐ (M.ⓜ-congˡ _ (⟦ⓜ⟧-sound later^[ n ] later^[ m ])) (M.symᵐ (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ zero  ] later^[ m ]ⓜconstantlyⓜforever = M.symᵐ (M.𝟙-identityˡ _)
⟦ⓜ⟧-sound later^[ suc n ] later^[ m ]ⓜconstantlyⓜforever =
  M.transᵐ (M.ⓜ-congˡ _ (⟦ⓜ⟧-sound later^[ n ] later^[ m ]ⓜconstantlyⓜforever)) (M.symᵐ (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ zero  ]ⓜconstantly =
  M.symᵐ (M.transᵐ (M.transᵐ (M.ⓜ-assoc _ _ _) (M.ⓜ-congˡ _ M.forever-constantly)) (M.𝟙-identityʳ _))
⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ suc m ]ⓜconstantly =
  M.transᵐ (M.transᵐ (⟦ⓜ⟧-sound later^[ zero ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantly)
                     (M.ⓜ-congʳ _ (M.transᵐ (M.ⓜ-congˡ _ (M.symᵐ M.forever-later)) (M.symᵐ (M.ⓜ-assoc _ _ _)))))
           (M.ⓜ-assoc _ _ _)
⟦ⓜ⟧-sound later^[ suc n ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantly =
  M.transᵐ (M.ⓜ-congˡ _ (⟦ⓜ⟧-sound later^[ n ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantly)) (M.symᵐ (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ zero  ] = M.symᵐ (M.𝟙-identityʳ _)
⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ suc m ] =
  M.transᵐ (⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ m ])
           (M.transᵐ (M.ⓜ-congʳ _ (M.transᵐ (M.ⓜ-congˡ _ (M.symᵐ M.forever-later)) (M.symᵐ (M.ⓜ-assoc _ _ _)))) (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ suc n ]ⓜconstantlyⓜforever later^[ m ] =
  M.transᵐ (M.ⓜ-congˡ _ (⟦ⓜ⟧-sound later^[ n ]ⓜconstantlyⓜforever later^[ m ])) (M.symᵐ (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ zero  ]ⓜconstantlyⓜforever =
  M.transᵐ (M.ⓜ-congˡ _ (M.symᵐ (M.transᵐ (M.ⓜ-congʳ _ M.forever-constantly) (M.𝟙-identityˡ _))))
           (M.transᵐ (M.ⓜ-congˡ _ (M.ⓜ-assoc _ _ _)) (M.symᵐ (M.ⓜ-assoc _ _ _)))
⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ suc m ]ⓜconstantlyⓜforever =
  M.transᵐ (⟦ⓜ⟧-sound later^[ zero  ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantlyⓜforever)
           (M.transᵐ (M.ⓜ-congʳ _ (M.transᵐ (M.ⓜ-congˡ _ (M.symᵐ M.forever-later)) (M.symᵐ (M.ⓜ-assoc _ _ _)))) (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound later^[ suc n ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantlyⓜforever =
  M.transᵐ (M.ⓜ-congˡ _ (⟦ⓜ⟧-sound later^[ n ]ⓜconstantlyⓜforever later^[ m ]ⓜconstantlyⓜforever)) (M.symᵐ (M.ⓜ-assoc _ _ _))

⟦_⟧two-cell : TwoCell μ κ → M.TwoCell ⟦ μ ⟧mod ⟦ κ ⟧mod
⟦ id𝟙★ ⟧two-cell = M.id-cell
⟦ ltrⓜcst {l = zero } z≤n ⟧two-cell = M.id-cell
⟦ ltrⓜcst {l = suc l} z≤n ⟧two-cell = (M.𝟙≤later M.ⓣ-hor ⟦ ltrⓜcst {l = l} z≤n ⟧two-cell) M.ⓣ-vert M.≅ᵐ-to-2-cell (M.symᵐ (M.𝟙-identityˡ _))
⟦ ltrⓜcst (s≤s k≤l) ⟧two-cell = M.id-cell M.ⓣ-hor ⟦ ltrⓜcst k≤l ⟧two-cell
⟦ id-frv ⟧two-cell = M.id-cell
⟦ ltr {l = zero } z≤n ⟧two-cell = M.id-cell
⟦ ltr {l = suc l} z≤n ⟧two-cell = (M.𝟙≤later M.ⓣ-hor ⟦ ltr {l = l} z≤n ⟧two-cell) M.ⓣ-vert M.≅ᵐ-to-2-cell (M.symᵐ (M.𝟙-identityˡ _))
⟦ ltr (s≤s k≤l) ⟧two-cell = M.id-cell M.ⓣ-hor ⟦ ltr k≤l ⟧two-cell
⟦ ltrⓜcstⓜfrv {l = zero } z≤n ⟧two-cell = M.id-cell
⟦ ltrⓜcstⓜfrv {l = suc l} z≤n ⟧two-cell = (M.𝟙≤later M.ⓣ-hor ⟦ ltrⓜcstⓜfrv {l = l} z≤n ⟧two-cell) M.ⓣ-vert M.≅ᵐ-to-2-cell (M.symᵐ (M.𝟙-identityˡ _))
⟦ ltrⓜcstⓜfrv (s≤s k≤l) ⟧two-cell = M.id-cell M.ⓣ-hor ⟦ ltrⓜcstⓜfrv k≤l ⟧two-cell
⟦ cstⓜfrv≤𝟙 {l = zero } z≤n ⟧two-cell = M.constantly∘forever≤𝟙
⟦ cstⓜfrv≤𝟙 {l = suc l} z≤n ⟧two-cell = (M.𝟙≤later M.ⓣ-hor ⟦ cstⓜfrv≤𝟙 {l = l} z≤n ⟧two-cell) M.ⓣ-vert M.≅ᵐ-to-2-cell (M.symᵐ (M.𝟙-identityˡ _))
⟦ cstⓜfrv≤𝟙 (s≤s k≤l) ⟧two-cell = M.id-cell M.ⓣ-hor ⟦ cstⓜfrv≤𝟙 k≤l ⟧two-cell
