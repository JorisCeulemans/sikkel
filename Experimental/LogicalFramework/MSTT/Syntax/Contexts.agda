--------------------------------------------------
-- Definition of MSTT contexts and telescopes
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension

module Experimental.LogicalFramework.MSTT.Syntax.Contexts
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (Name : Set)
  where

open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯

open ModeTheory ℳ

private variable
  m n o p : Mode
  μ ρ κ φ : Modality m n
  T S : Ty m
  x y : Name


infixl 4 _,,_∣_∈_ _,lock⟨_⟩
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
-- They are defined as "well-moded" cons lists since the cons
-- constructor is actually used in practice when implementing renaming
-- and substitution.
data LockTele (m : Mode) : Mode → Set where
  ◇ : LockTele m m
  lock⟨_⟩,_ : (μ : Modality o m) (Λ : LockTele o n) → LockTele m n

_,ˡᵗ_ : Ctx m → LockTele m n → Ctx n
Γ ,ˡᵗ ◇ = Γ
Γ ,ˡᵗ (lock⟨ μ ⟩, Λ) = (Γ ,lock⟨ μ ⟩) ,ˡᵗ Λ

locks-lt : LockTele m n → Modality n m
locks-lt ◇ = 𝟙
locks-lt (lock⟨ μ ⟩, ◇) = μ
locks-lt (lock⟨ μ ⟩, Λ) = μ ⓜ locks-lt Λ

data _≈_,ˡᵗ_ (Γ : Ctx n) : Ctx m → LockTele m n → Set where
  ◇ : Γ ≈ Γ ,ˡᵗ ◇
  lock⟨_⟩,_ : {Δ : Ctx o} {Λ : LockTele m n} (μ : Modality m o) → Γ ≈ Δ ,lock⟨ μ ⟩ ,ˡᵗ Λ → Γ ≈ Δ ,ˡᵗ (lock⟨ μ ⟩, Λ)
