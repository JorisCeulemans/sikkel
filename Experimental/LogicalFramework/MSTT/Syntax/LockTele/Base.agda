open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory

-- Lock telescopes are defined in a seperate file (i.e. not in the
-- same one as contexts) because they do not depend on a type of
-- names. This module will be publicly exported by
-- Experimental.LogicalFramework.MSTT.Syntax.Context.
module Experimental.LogicalFramework.MSTT.Syntax.LockTele.Base
  (ℳ : ModeTheory)
  where

open import Relation.Binary.PropositionalEquality

open ModeTheory ℳ

private variable
  m n o : Mode


-- Lock telescopes consist of only locks (so no variables).
-- They are defined as "well-moded" cons lists which reflects their usage.
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
