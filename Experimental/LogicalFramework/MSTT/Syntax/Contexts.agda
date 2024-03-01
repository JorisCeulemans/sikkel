--------------------------------------------------
-- Definition of MSTT contexts and telescopes
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension

module Experimental.LogicalFramework.MSTT.Syntax.Contexts
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (Name : Set)
  where

open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯

open ModeTheory ℳ

private variable
  m n o p : Mode
  μ ρ κ φ : Modality m n
  T S : Ty m
  x y : Name


infixl 6 _,,_∣_∈_ _,lock⟨_⟩
data Ctx (m : Mode) : Set where
  ◇ : Ctx m
  _,,_∣_∈_ : (Γ : Ctx m) (μ : Modality n m) (x : Name) (T : Ty n) → Ctx m
    -- ^ All variables have a name of type Name and appear under a modality.
  _,lock⟨_⟩ : (Γ : Ctx n) (μ : Modality m n) → Ctx m

_,,_∈_ : Ctx m → Name → Ty m → Ctx m
Γ ,, x ∈ T = Γ ,, 𝟙 ∣ x ∈ T


--------------------------------------------------
-- Telescopes of locks and/or variables

-- Telescopes can contain variables and locks.
-- They are defined as "well-moded" snoc lists (just like contexts).
data Telescope : Mode → Mode → Set where
  ◇ : Telescope m m
  _,,_∣_∈_ : Telescope m n → Modality o n → Name → Ty o → Telescope m n
  _,lock⟨_⟩ : Telescope m o → Modality n o → Telescope m n

_++tel_ : Ctx m → Telescope m n → Ctx n
Γ ++tel ◇ = Γ
Γ ++tel (Θ ,, μ ∣ x ∈ T) = (Γ ++tel Θ) ,, μ ∣ x ∈ T
Γ ++tel (Θ ,lock⟨ μ ⟩) = (Γ ++tel Θ) ,lock⟨ μ ⟩

locks-tel : Telescope m n → Modality n m
locks-tel ◇ = 𝟙
locks-tel (Θ ,, μ ∣ x ∈ T) = locks-tel Θ
locks-tel (Θ ,lock⟨ μ ⟩) = locks-tel Θ ⓜ μ


-- Lock telescopes consist of only locks (so no variables).
-- They are defined as "well-moded" cons lists which reflects their usage.
data LockTele (m : Mode) : Mode → Set where
  ◇ : LockTele m m
  lock⟨_⟩,_ : (μ : Modality o m) (Λ : LockTele o n) → LockTele m n

infixl 5 _,ˡᵗ_
_,ˡᵗ_ : Ctx m → LockTele m n → Ctx n
Γ ,ˡᵗ ◇ = Γ
Γ ,ˡᵗ (lock⟨ μ ⟩, Λ) = (Γ ,lock⟨ μ ⟩) ,ˡᵗ Λ

locksˡᵗ : LockTele m n → Modality n m
locksˡᵗ ◇ = 𝟙
locksˡᵗ (lock⟨ μ ⟩, Λ) = μ ⓜ locksˡᵗ Λ

infixl 6 _++ˡᵗ_
_++ˡᵗ_ : LockTele m n → LockTele n o → LockTele m o
◇ ++ˡᵗ Θ = Θ
(lock⟨ μ ⟩, Λ) ++ˡᵗ Θ = lock⟨ μ ⟩, (Λ ++ˡᵗ Θ)

++ˡᵗ-locks : (Λ : LockTele m n) {Θ : LockTele n o} → locksˡᵗ Λ ⓜ locksˡᵗ Θ ≡ locksˡᵗ (Λ ++ˡᵗ Θ)
++ˡᵗ-locks ◇ = mod-unitˡ
++ˡᵗ-locks (lock⟨ μ ⟩, Λ) {Θ = Θ} = trans (mod-assoc (locksˡᵗ Θ)) (cong (μ ⓜ_) (++ˡᵗ-locks Λ))

,ˡᵗ-++ˡᵗ : {Γ : Ctx m} (Λ : LockTele m n) {Θ : LockTele n o} →
         Γ ,ˡᵗ (Λ ++ˡᵗ Θ) ≡ Γ ,ˡᵗ Λ ,ˡᵗ Θ
,ˡᵗ-++ˡᵗ ◇ = refl
,ˡᵗ-++ˡᵗ (lock⟨ μ ⟩, Λ) = ,ˡᵗ-++ˡᵗ Λ

whiskerˡᵗ-left : (Λ : LockTele m n) {Θ Ψ : LockTele n o} → TwoCell (locksˡᵗ Θ) (locksˡᵗ Ψ) →
                 TwoCell (locksˡᵗ (Λ ++ˡᵗ Θ)) (locksˡᵗ (Λ ++ˡᵗ Ψ))
whiskerˡᵗ-left ◇ α = α
whiskerˡᵗ-left (lock⟨ μ ⟩, Λ) α = (id-cell {μ = μ}) ⓣ-hor (whiskerˡᵗ-left Λ α)

whiskerˡᵗ-right : (Θ Ψ : LockTele m n) {Λ : LockTele n o} → TwoCell (locksˡᵗ Θ) (locksˡᵗ Ψ) →
                  TwoCell (locksˡᵗ (Θ ++ˡᵗ Λ)) (locksˡᵗ (Ψ ++ˡᵗ Λ))
whiskerˡᵗ-right Θ Ψ {Λ} α = transp-cellʳ (++ˡᵗ-locks Ψ) (transp-cellˡ (++ˡᵗ-locks Θ) (α ⓣ-hor id-cell {μ = locksˡᵗ Λ}))
