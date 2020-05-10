open import Categories

module Yoneda {o h} (C : Category {o}{h}) where

-- open import Data.Nat hiding (_⊔_)
-- open import Data.Nat.Properties
open import Function hiding (_⟨_⟩_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers
open import CwF-Structure.Contexts C

open Category C

-- Yoneda embedding
𝕪 : Ob → Ctx (h ⊔ ℓ)
set (𝕪 {ℓ} x) y = Lift ℓ (Hom y x)
rel (𝕪 x) f (lift g) = lift (g ∙ f)
rel-id (𝕪 x) (lift _) = cong lift hom-idʳ
rel-comp (𝕪 x) _ _ (lift _) = cong lift (sym ∙assoc)

𝕪[_]_ : ∀ ℓ → Ob → Ctx (h ⊔ ℓ)
𝕪[ ℓ ] x = 𝕪 {ℓ} x

-- The Yoneda lemma
to-𝕪⇒* : {Γ : Ctx (h ⊔ ℓ)} {x : Ob} → Γ ⟨ x ⟩ → 𝕪[ ℓ ] x ⇒ Γ
to-𝕪⇒* {Γ = Γ} γ = MkSubst (λ { (lift f) → Γ ⟪ f ⟫ γ })
                            (λ { (lift f) → sym (rel-comp Γ _ f γ) })

from-𝕪⇒* : {Γ : Ctx (h ⊔ ℓ)} {x : Ob} → 𝕪[ ℓ ] x ⇒ Γ → Γ ⟨ x ⟩
from-𝕪⇒* σ = func σ (lift hom-id)

𝕪-to-∘-from : {Γ : Ctx (h ⊔ ℓ)} {x : Ob} (σ : 𝕪[ ℓ ] x ⇒ Γ) → to-𝕪⇒* (from-𝕪⇒* σ) ≡ σ
𝕪-to-∘-from σ = cong₂-d MkSubst (funextI (funext λ { (lift f) → trans (naturality σ (lift hom-id))
                                                                        (cong (func σ ∘ lift) hom-idˡ) }))
                                (funextI (funextI (funextI (funext λ _ → uip _ _))))

𝕪-from-∘-to : {Γ : Ctx (h ⊔ ℓ)} {x : Ob} (γ : Γ ⟨ x ⟩) → from-𝕪⇒* {ℓ = ℓ} {Γ = Γ} (to-𝕪⇒* γ) ≡ γ
𝕪-from-∘-to {Γ = Γ} γ = rel-id Γ γ

-- Proving that the Yoneda embedding is fully faithful
to-𝕪⇒𝕪 : Hom x y → 𝕪[ ℓ ] x ⇒ 𝕪[ ℓ ] y
to-𝕪⇒𝕪 = to-𝕪⇒* ∘ lift

from-𝕪⇒𝕪 : 𝕪[ ℓ ] x ⇒ 𝕪[ ℓ ] y → Hom x y
from-𝕪⇒𝕪 = lower ∘ from-𝕪⇒*

𝕪-from-∘-to' : (f : Hom x y) → from-𝕪⇒𝕪 (to-𝕪⇒𝕪 {ℓ = ℓ} f) ≡ f
𝕪-from-∘-to' f = hom-idʳ

𝕪-to-∘-from' : (σ : 𝕪[ ℓ ] x ⇒ 𝕪 y) → to-𝕪⇒𝕪 (from-𝕪⇒𝕪 σ) ≡ σ
𝕪-to-∘-from' σ = 𝕪-to-∘-from σ

𝕪-refl : to-𝕪⇒𝕪 hom-id ≡ id-subst (𝕪[ ℓ ] x)
𝕪-refl = cong₂-d MkSubst (funextI (funext λ { (lift k≤m) → cong lift hom-idˡ }))
                          (funextI (funextI (funextI (funext λ _ → uip _ _))))

𝕪-comp : {Γ : Ctx (h ⊔ ℓ)} (f : Hom x y) (γ : Γ ⟨ y ⟩) → to-𝕪⇒* {ℓ = ℓ} {Γ = Γ} γ ⊚ to-𝕪⇒𝕪 f ≡ to-𝕪⇒* (Γ ⟪ f ⟫ γ)
𝕪-comp {Γ = Γ} ineq γ = cong₂-d MkSubst
                          (funextI (funext λ { (lift ineq') → rel-comp Γ ineq' ineq γ }))
                          (funextI (funextI (funextI (funext λ _ → uip _ _))))
