--------------------------------------------------
-- Definition of MSTT contexts and telescopes
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension

module Experimental.LogicalFramework.MSTT.Syntax.Contexts
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ)
  where

open import Data.Product
open import Data.String
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯
open import Experimental.LogicalFramework.Proof.CheckingMonad

open ModeTheory ℳ

private variable
  m n o p : Mode
  μ ρ κ φ : Modality m n
  T S : Ty m


-- Provide an alias for when strings are used as variable names
Name : Set
Name = String

private variable
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
data Telescope (m : Mode) : Mode → Set where
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

-- A nameless telescope with just information about annotation and type of variables
data NamelessTele (m : Mode) : Mode → Set where
  ◇ : NamelessTele m m
  _,,_∣_ : NamelessTele m n → Modality o n → Ty o → NamelessTele m n
  _,lock⟨_⟩ : NamelessTele m o → Modality n o → NamelessTele m n

Names : NamelessTele m n → Set
Names ◇ = ⊤
Names (Θ ,, μ ∣ T) = Names Θ × Name
Names (Θ ,lock⟨ μ ⟩) = Names Θ

add-names : (Θ : NamelessTele m n) → Names Θ → Telescope m n
add-names ◇              names = ◇
add-names (Θ ,, μ ∣ T)   (names , x) = (add-names Θ names) ,, μ ∣ x ∈ T
add-names (Θ ,lock⟨ μ ⟩) names = (add-names Θ names) ,lock⟨ μ ⟩


--------------------------------------------------
-- Lock telescopes consisting of only locks (so no variables)

-- Lock telescopes are defined as "well-moded" cons lists which reflects their usage.
data LockTele (m : Mode) : Mode → Set where
  ◇ : LockTele m m
  lock⟨_⟩,_ : (μ : Modality o m) (Λ : LockTele o n) → LockTele m n

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

infixl 5 _,ˡᵗ_
_,ˡᵗ_ : Ctx m → LockTele m n → Ctx n
Γ ,ˡᵗ ◇ = Γ
Γ ,ˡᵗ (lock⟨ μ ⟩, Λ) = (Γ ,lock⟨ μ ⟩) ,ˡᵗ Λ

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
whiskerˡᵗ-right Θ Ψ {Λ} α =
  eq-cell (++ˡᵗ-locks Ψ)
  ⓣ-vert ((α ⓣ-hor (id-cell {μ = locksˡᵗ Λ}))
  ⓣ-vert eq-cell (sym (++ˡᵗ-locks Θ)))


_≟ltel_ : (Λ1 Λ2 : LockTele m n) → PCM (Λ1 ≡ Λ2)
◇                ≟ltel ◇                = return refl
(lock⟨ μ1 ⟩, Λ1) ≟ltel (lock⟨ μ2 ⟩, Λ2) = do
  refl ← mod-dom μ1 ≟mode mod-dom μ2
  refl ← μ1 ≟mod μ2
  refl ← Λ1 ≟ltel Λ2
  return refl
_ ≟ltel _ = error "Lock telescopes are not equal"
