-- Code to be reused later to implement a mode theory for guarded
-- recursion. Is not supposed to typecheck right now.

module Experimental.LogicalFramework.MSTT.Parameter.ModeTheorySemantics where

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
⟦ 𝟙 ⟧mod = M.𝟙
⟦ non-triv nt-forever ⟧mod = M.forever
⟦ non-triv later^[ zero  ]ⓜconstantly ⟧mod = M.constantly
⟦ non-triv later^[ suc n ]ⓜconstantly ⟧mod = M.later M.ⓜ ⟦ non-triv later^[ n ]ⓜconstantly ⟧mod
⟦ non-triv later^[1+ zero  ] ⟧mod = M.later
⟦ non-triv later^[1+ suc n ] ⟧mod = M.later M.ⓜ ⟦ non-triv later^[1+ n ] ⟧mod
⟦ non-triv later^[ zero  ]ⓜconstantlyⓜforever ⟧mod = M.constantly M.ⓜ M.forever
⟦ non-triv later^[ suc n ]ⓜconstantlyⓜforever ⟧mod = M.later M.ⓜ ⟦ non-triv later^[ n ]ⓜconstantlyⓜforever ⟧mod

⟦𝟙⟧-sound : ∀ {m} → ⟦ 𝟙 {m} ⟧mod ≅ᵐ M.𝟙
⟦𝟙⟧-sound = M.reflᵐ

⟦ⓜ⟧-sound : (μ : Modality n o) (κ : Modality m n) → ⟦ μ ⓜ κ ⟧mod ≅ᵐ ⟦ μ ⟧mod M.ⓜ ⟦ κ ⟧mod
⟦ⓜ⟧-sound 𝟙 κ = M.symᵐ (M.𝟙-unitˡ _)
⟦ⓜ⟧-sound (non-triv nt-forever) 𝟙 = M.symᵐ (M.𝟙-unitʳ _)
⟦ⓜ⟧-sound (non-triv nt-forever) (non-triv later^[ zero  ]ⓜconstantly) = M.symᵐ M.forever-constantly
⟦ⓜ⟧-sound (non-triv nt-forever) (non-triv later^[ suc n ]ⓜconstantly) =
  M.transᵐ (M.transᵐ (⟦ⓜ⟧-sound (non-triv nt-forever) (non-triv later^[ n ]ⓜconstantly))
                     (M.ⓜ-congˡ _ (M.symᵐ M.forever-later)))
           (M.ⓜ-assoc _ _ _)
⟦ⓜ⟧-sound (non-triv nt-forever) (non-triv later^[1+ zero  ]) = M.symᵐ M.forever-later
⟦ⓜ⟧-sound (non-triv nt-forever) (non-triv later^[1+ suc n ]) = 
  M.transᵐ (M.transᵐ (⟦ⓜ⟧-sound (non-triv nt-forever) (non-triv later^[1+ n ]))
                     (M.ⓜ-congˡ _ (M.symᵐ M.forever-later)))
           (M.ⓜ-assoc _ _ _)
⟦ⓜ⟧-sound (non-triv nt-forever) (non-triv later^[ zero  ]ⓜconstantlyⓜforever) =
  M.transᵐ (M.transᵐ (M.symᵐ (M.𝟙-unitˡ _)) (M.ⓜ-congˡ _ (M.symᵐ M.forever-constantly))) (M.ⓜ-assoc _ _ _)
⟦ⓜ⟧-sound (non-triv nt-forever) (non-triv later^[ suc n ]ⓜconstantlyⓜforever) =
  M.transᵐ (M.transᵐ (⟦ⓜ⟧-sound (non-triv nt-forever) (non-triv later^[ n ]ⓜconstantlyⓜforever))
                     (M.ⓜ-congˡ _ (M.symᵐ M.forever-later)))
           (M.ⓜ-assoc _ _ _)
⟦ⓜ⟧-sound (non-triv later^[ n ]ⓜconstantly) 𝟙 = M.symᵐ (M.𝟙-unitʳ _)
⟦ⓜ⟧-sound (non-triv later^[ zero  ]ⓜconstantly) (non-triv nt-forever) = M.reflᵐ
⟦ⓜ⟧-sound (non-triv later^[ suc n ]ⓜconstantly) (non-triv nt-forever) =
  M.transᵐ (M.ⓜ-congʳ _ (⟦ⓜ⟧-sound (non-triv later^[ n ]ⓜconstantly) forever)) (M.symᵐ (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound (non-triv later^[1+ n ]) 𝟙 = M.symᵐ (M.𝟙-unitʳ _)
⟦ⓜ⟧-sound (non-triv later^[1+ zero  ]) (non-triv later^[ m ]ⓜconstantly) = M.reflᵐ
⟦ⓜ⟧-sound (non-triv later^[1+ suc n ]) (non-triv later^[ m ]ⓜconstantly) =
  M.transᵐ (M.ⓜ-congʳ _ (⟦ⓜ⟧-sound (non-triv later^[1+ n ]) (non-triv later^[ m ]ⓜconstantly))) (M.symᵐ (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound (non-triv later^[1+ zero  ]) (non-triv later^[1+ m ]) = M.reflᵐ
⟦ⓜ⟧-sound (non-triv later^[1+ suc n ]) (non-triv later^[1+ m ]) =
  M.transᵐ (M.ⓜ-congʳ _ (⟦ⓜ⟧-sound (non-triv later^[1+ n ]) (non-triv later^[1+ m ]))) (M.symᵐ (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound (non-triv later^[1+ zero  ]) (non-triv later^[ m ]ⓜconstantlyⓜforever) = M.reflᵐ
⟦ⓜ⟧-sound (non-triv later^[1+ suc n ]) (non-triv later^[ m ]ⓜconstantlyⓜforever) =
  M.transᵐ (M.ⓜ-congʳ _ (⟦ⓜ⟧-sound (non-triv later^[1+ n ]) (non-triv later^[ m ]ⓜconstantlyⓜforever))) (M.symᵐ (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound (non-triv later^[ n ]ⓜconstantlyⓜforever) 𝟙 = M.symᵐ (M.𝟙-unitʳ _)
⟦ⓜ⟧-sound (non-triv later^[ zero ]ⓜconstantlyⓜforever) (non-triv later^[ zero  ]ⓜconstantly) =
  M.symᵐ (M.transᵐ (M.transᵐ (M.ⓜ-assoc _ _ _) (M.ⓜ-congʳ _ M.forever-constantly)) (M.𝟙-unitʳ _))
⟦ⓜ⟧-sound (non-triv later^[ zero ]ⓜconstantlyⓜforever) (non-triv later^[ suc m ]ⓜconstantly) =
  M.transᵐ (M.transᵐ (⟦ⓜ⟧-sound (non-triv later^[ zero ]ⓜconstantlyⓜforever) (non-triv later^[ m ]ⓜconstantly))
                     (M.ⓜ-congˡ _ (M.transᵐ (M.ⓜ-congʳ _ (M.symᵐ M.forever-later)) (M.symᵐ (M.ⓜ-assoc _ _ _)))))
           (M.ⓜ-assoc _ _ _)
⟦ⓜ⟧-sound (non-triv later^[ suc n ]ⓜconstantlyⓜforever) (non-triv later^[ m ]ⓜconstantly) =
  M.transᵐ (M.ⓜ-congʳ _ (⟦ⓜ⟧-sound (non-triv later^[ n ]ⓜconstantlyⓜforever) (non-triv later^[ m ]ⓜconstantly))) (M.symᵐ (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound (non-triv later^[ zero ]ⓜconstantlyⓜforever) (non-triv later^[1+ zero  ]) =
  M.symᵐ (M.transᵐ (M.ⓜ-assoc _ _ _) (M.ⓜ-congʳ _ M.forever-later))
⟦ⓜ⟧-sound (non-triv later^[ zero ]ⓜconstantlyⓜforever) (non-triv later^[1+ suc m ]) =
  M.transᵐ (⟦ⓜ⟧-sound (non-triv later^[ zero  ]ⓜconstantlyⓜforever) (non-triv later^[1+ m ]))
           (M.transᵐ (M.ⓜ-congˡ _ (M.transᵐ (M.ⓜ-congʳ _ (M.symᵐ M.forever-later)) (M.symᵐ (M.ⓜ-assoc _ _ _)))) (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound (non-triv later^[ suc n ]ⓜconstantlyⓜforever) (non-triv later^[1+ m ]) =
  M.transᵐ (M.ⓜ-congʳ _ (⟦ⓜ⟧-sound (non-triv later^[ n ]ⓜconstantlyⓜforever) (non-triv later^[1+ m ]))) (M.symᵐ (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound (non-triv later^[ zero ]ⓜconstantlyⓜforever) (non-triv later^[ zero  ]ⓜconstantlyⓜforever) =
  M.transᵐ (M.ⓜ-congʳ _ (M.symᵐ (M.transᵐ (M.ⓜ-congˡ _ M.forever-constantly) (M.𝟙-unitˡ _))))
           (M.transᵐ (M.ⓜ-congʳ _ (M.ⓜ-assoc _ _ _)) (M.symᵐ (M.ⓜ-assoc _ _ _)))
⟦ⓜ⟧-sound (non-triv later^[ zero ]ⓜconstantlyⓜforever) (non-triv later^[ suc m ]ⓜconstantlyⓜforever) =
  M.transᵐ (⟦ⓜ⟧-sound (non-triv later^[ zero  ]ⓜconstantlyⓜforever) (non-triv later^[ m ]ⓜconstantlyⓜforever))
           (M.transᵐ (M.ⓜ-congˡ _ (M.transᵐ (M.ⓜ-congʳ _ (M.symᵐ M.forever-later)) (M.symᵐ (M.ⓜ-assoc _ _ _)))) (M.ⓜ-assoc _ _ _))
⟦ⓜ⟧-sound (non-triv later^[ suc n ]ⓜconstantlyⓜforever) (non-triv later^[ m ]ⓜconstantlyⓜforever) =
  M.transᵐ (M.ⓜ-congʳ _ (⟦ⓜ⟧-sound (non-triv later^[ n ]ⓜconstantlyⓜforever) (non-triv later^[ m ]ⓜconstantlyⓜforever))) (M.symᵐ (M.ⓜ-assoc _ _ _))

⟦_⟧two-cell : TwoCell μ κ → M.TwoCell ⟦ μ ⟧mod ⟦ κ ⟧mod
⟦ id𝟙 ⟧two-cell = M.id-cell
⟦ ltrⓜcst {l = zero } z≤n ⟧two-cell = M.id-cell
⟦ ltrⓜcst {l = suc l} z≤n ⟧two-cell = (M.𝟙≤later M.ⓣ-hor ⟦ ltrⓜcst {l = l} z≤n ⟧two-cell) M.ⓣ-vert M.≅ᵐ-to-2-cell (M.symᵐ (M.𝟙-unitˡ _))
⟦ ltrⓜcst (s≤s k≤l) ⟧two-cell = M.id-cell M.ⓣ-hor ⟦ ltrⓜcst k≤l ⟧two-cell
⟦ id-frv ⟧two-cell = M.id-cell
⟦ ltr {l = zero } z≤n ⟧two-cell = M.id-cell
⟦ ltr {l = suc l} z≤n ⟧two-cell = (M.𝟙≤later M.ⓣ-hor ⟦ ltr {l = l} z≤n ⟧two-cell) M.ⓣ-vert M.≅ᵐ-to-2-cell (M.symᵐ (M.𝟙-unitˡ _))
⟦ ltr (s≤s k≤l) ⟧two-cell = M.id-cell M.ⓣ-hor ⟦ ltr k≤l ⟧two-cell
⟦ 𝟙≤ltr {k = zero } ⟧two-cell = M.𝟙≤later
⟦ 𝟙≤ltr {k = suc k} ⟧two-cell = (M.𝟙≤later M.ⓣ-hor ⟦ 𝟙≤ltr {k = k} ⟧two-cell) M.ⓣ-vert M.≅ᵐ-to-2-cell (M.symᵐ (M.𝟙-unitˡ _))
⟦ ltrⓜcstⓜfrv {l = zero } z≤n ⟧two-cell = M.id-cell
⟦ ltrⓜcstⓜfrv {l = suc l} z≤n ⟧two-cell = (M.𝟙≤later M.ⓣ-hor ⟦ ltrⓜcstⓜfrv {l = l} z≤n ⟧two-cell) M.ⓣ-vert M.≅ᵐ-to-2-cell (M.symᵐ (M.𝟙-unitˡ _))
⟦ ltrⓜcstⓜfrv (s≤s k≤l) ⟧two-cell = M.id-cell M.ⓣ-hor ⟦ ltrⓜcstⓜfrv k≤l ⟧two-cell
⟦ cstⓜfrv≤𝟙 ⟧two-cell = M.constantly∘forever≤𝟙
⟦ cstⓜfrv≤ltr {l = zero } z≤n ⟧two-cell = M.𝟙≤later M.ⓣ-vert M.constantly∘forever≤𝟙
⟦ cstⓜfrv≤ltr {l = suc l} z≤n ⟧two-cell = (M.𝟙≤later M.ⓣ-hor ⟦ cstⓜfrv≤ltr {l = l} z≤n ⟧two-cell) M.ⓣ-vert M.≅ᵐ-to-2-cell (M.symᵐ (M.𝟙-unitˡ _))
⟦ cstⓜfrv≤ltr {l = zero } (s≤s z≤n)   ⟧two-cell = M.≅ᵐ-to-2-cell (M.𝟙-unitʳ _) M.ⓣ-vert (M.id-cell M.ⓣ-hor M.constantly∘forever≤𝟙)
⟦ cstⓜfrv≤ltr {l = suc l} (s≤s k≤1+l) ⟧two-cell = M.id-cell M.ⓣ-hor ⟦ cstⓜfrv≤ltr {l = l} k≤1+l ⟧two-cell
