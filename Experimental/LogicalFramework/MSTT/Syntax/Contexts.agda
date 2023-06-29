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

-- A telescope consisting of only locks, no variables.
-- TODO: we might be able to unify this definition with that of
-- Telescope, by constructing a general Telescope data type that is
-- parametrized by a "permission" to use variables and/or locks.
data LockTele : Mode → Mode → Set where
  ◇ : LockTele m m
  _,lock⟨_⟩ : LockTele m o → Modality n o → LockTele m n

_++ltel_ : Ctx m → LockTele m n → Ctx n
Γ ++ltel ◇ = Γ
Γ ++ltel (Θ ,lock⟨ μ ⟩) = (Γ ++ltel Θ) ,lock⟨ μ ⟩

locks-ltel : LockTele m n → Modality n m
locks-ltel ◇ = 𝟙
locks-ltel (Θ ,lock⟨ μ ⟩) = locks-ltel Θ ⓜ μ
