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
-- They are defined as "well-moded" snoc lists.
data LockTele (m : Mode) : Mode → Set where
  ◇ : LockTele m m
  _,lock⟨_⟩ : (Λ : LockTele m o) (μ : Modality n o) → LockTele m n

lock⟨_⟩,_ : Modality o m → LockTele o n → LockTele m n
lock⟨ μ ⟩, ◇ = ◇ ,lock⟨ μ ⟩
lock⟨ μ ⟩, (Λ ,lock⟨ ρ ⟩) = (lock⟨ μ ⟩, Λ) ,lock⟨ ρ ⟩

infixl 5 _,ˡᵗ_
_,ˡᵗ_ : Ctx m → LockTele m n → Ctx n
Γ ,ˡᵗ ◇ = Γ
Γ ,ˡᵗ (Λ ,lock⟨ μ ⟩) = (Γ ,ˡᵗ Λ) ,lock⟨ μ ⟩

locksˡᵗ : LockTele m n → Modality n m
locksˡᵗ ◇ = 𝟙
locksˡᵗ (◇ ,lock⟨ μ ⟩) = μ
locksˡᵗ (Λ ,lock⟨ μ ⟩) = locksˡᵗ Λ ⓜ μ

infixl 6 _++ˡᵗ_
_++ˡᵗ_ : LockTele m n → LockTele n o → LockTele m o
Λ ++ˡᵗ ◇ = Λ
Λ ++ˡᵗ (Θ ,lock⟨ μ ⟩) = (Λ ++ˡᵗ Θ) ,lock⟨ μ ⟩

++ˡᵗ-locks : {Λ : LockTele m n} (Θ : LockTele n o) → locksˡᵗ Λ ⓜ locksˡᵗ Θ ≡ locksˡᵗ (Λ ++ˡᵗ Θ)
++ˡᵗ-locks ◇ = mod-unitʳ
++ˡᵗ-locks {Λ = ◇} (◇ ,lock⟨ μ ⟩) = refl
++ˡᵗ-locks {Λ = Λ@(_ ,lock⟨ _ ⟩)} (◇ ,lock⟨ μ ⟩) = refl
++ˡᵗ-locks {Λ = Λ} (Θ ,lock⟨ ρ ⟩ ,lock⟨ μ ⟩) =
  trans (sym (mod-assoc (locksˡᵗ Λ))) (cong (_ⓜ μ) (++ˡᵗ-locks (Θ ,lock⟨ ρ ⟩)))

,ˡᵗ-++ˡᵗ : {Γ : Ctx m} {Λ : LockTele m n} (Θ : LockTele n o) →
         Γ ,ˡᵗ (Λ ++ˡᵗ Θ) ≡ Γ ,ˡᵗ Λ ,ˡᵗ Θ
,ˡᵗ-++ˡᵗ ◇ = refl
,ˡᵗ-++ˡᵗ (Θ ,lock⟨ μ ⟩) = cong (_,lock⟨ μ ⟩) (,ˡᵗ-++ˡᵗ Θ)

whiskerˡᵗ-left : {Λ : LockTele m n} (Θ Ψ : LockTele n o) → TwoCell (locksˡᵗ Θ) (locksˡᵗ Ψ) →
                 TwoCell (locksˡᵗ (Λ ++ˡᵗ Θ)) (locksˡᵗ (Λ ++ˡᵗ Ψ))
whiskerˡᵗ-left {Λ = Λ} Θ Ψ α = transp-cellʳ (++ˡᵗ-locks Ψ) (transp-cellˡ (++ˡᵗ-locks Θ) (id-cell {μ = locksˡᵗ Λ} ⓣ-hor α))

whiskerˡᵗ-right : (Θ Ψ : LockTele m n) {Λ : LockTele n o} → TwoCell (locksˡᵗ Θ) (locksˡᵗ Ψ) →
                  TwoCell (locksˡᵗ (Θ ++ˡᵗ Λ)) (locksˡᵗ (Ψ ++ˡᵗ Λ))
whiskerˡᵗ-right Θ Ψ {Λ} α = transp-cellʳ (++ˡᵗ-locks Λ) (transp-cellˡ (++ˡᵗ-locks Λ) (α ⓣ-hor id-cell {μ = locksˡᵗ Λ}))


-- Instead of inductively defining the proposition Γ ≈ Δ ,ˡᵗ Λ  we
-- could make use of Agda's identity type and phrase it as Γ ≡ Δ ,ˡᵗ Λ.
-- However, the latter definition does not cooperate as smoothly
-- with unification and pattern matching.
infix 3 _≈_,ˡᵗ_
data _≈_,ˡᵗ_ : Ctx n → Ctx m → LockTele m n → Set where
  ◇ : {Γ : Ctx m} → Γ ≈ Γ ,ˡᵗ ◇
  _,lock⟨_⟩ : {Γ : Ctx n} {Δ : Ctx m} {Λ : LockTele m n} →
              Γ ≈ Δ ,ˡᵗ Λ →
              (μ : Modality o n) →
              Γ ,lock⟨ μ ⟩ ≈ Δ ,ˡᵗ (Λ ,lock⟨ μ ⟩)

≈,ˡᵗ-to-≡ : {Γ : Ctx n} {Δ : Ctx m} {Λ : LockTele m n} →
           Γ ≈ Δ ,ˡᵗ Λ → Γ ≡ Δ ,ˡᵗ Λ
≈,ˡᵗ-to-≡ ◇ = refl
≈,ˡᵗ-to-≡ (splitΓ ,lock⟨ μ ⟩) = cong (_,lock⟨ μ ⟩) (≈,ˡᵗ-to-≡ splitΓ)

split-refl : {Γ : Ctx m} {Λ : LockTele m n} → Γ ,ˡᵗ Λ ≈ Γ ,ˡᵗ Λ
split-refl {Λ = ◇} = ◇
split-refl {Λ = Λ ,lock⟨ μ ⟩} = split-refl {Λ = Λ} ,lock⟨ μ ⟩

split-append-locks : {Γ : Ctx n} {Δ : Ctx m} {Λ : LockTele m n} →
                     Γ ≈ Δ ,ˡᵗ Λ →
                     (Θ : LockTele n o) →
                     Γ ,ˡᵗ Θ ≈ Δ ,ˡᵗ (Λ ++ˡᵗ Θ)
split-append-locks splitΓ ◇ = splitΓ
split-append-locks splitΓ (Θ ,lock⟨ μ ⟩) = (split-append-locks splitΓ Θ) ,lock⟨ μ ⟩

split-move-right : {Γ : Ctx n} {Δ : Ctx m} {μ : Modality o m} {Λ : LockTele o n} →
                   Γ ≈ (Δ ,lock⟨ μ ⟩) ,ˡᵗ Λ → Γ ≈ Δ ,ˡᵗ (lock⟨ μ ⟩, Λ)
split-move-right ◇ = ◇ ,lock⟨ _ ⟩
split-move-right (splitΓ ,lock⟨ ρ ⟩) = (split-move-right splitΓ) ,lock⟨ ρ ⟩

split-move-left : {Γ : Ctx n} {Δ : Ctx m} {μ : Modality o m} {Λ : LockTele o n} →
                  Γ ≈ Δ ,ˡᵗ (lock⟨ μ ⟩, Λ) → Γ ≈ (Δ ,lock⟨ μ ⟩) ,ˡᵗ Λ
split-move-left {Λ = ◇} (◇ ,lock⟨ _ ⟩) = ◇
split-move-left {Λ = Λ ,lock⟨ μ ⟩} (splitΓ ,lock⟨ .μ ⟩) = (split-move-left splitΓ) ,lock⟨ μ ⟩

split-◇ : {Γ : Ctx n} {Δ : Ctx m} {Λ : LockTele m n} →
          Γ ≈ Δ ,ˡᵗ Λ → Γ ≈ (Δ ,ˡᵗ Λ) ,ˡᵗ ◇
split-◇ ◇ = ◇
split-◇ (splitΓ ,lock⟨ μ ⟩) = split-move-left (split-◇ splitΓ ,lock⟨ μ ⟩)

move-++ˡᵗ-right : {Γ : Ctx n} {Δ : Ctx m} {Λ : LockTele m o} {Θ : LockTele o n} →
                  Γ ≈ (Δ ,ˡᵗ Λ) ,ˡᵗ Θ →
                  Γ ≈ Δ ,ˡᵗ (Λ ++ˡᵗ Θ)
move-++ˡᵗ-right {Θ = ◇} ◇ = split-refl
move-++ˡᵗ-right {Θ = Θ ,lock⟨ μ ⟩} (splitΓ ,lock⟨ .μ ⟩) = move-++ˡᵗ-right splitΓ ,lock⟨ μ ⟩

move-++ˡᵗ-left : {Γ : Ctx n} {Δ : Ctx m} {Λ : LockTele m o} {Θ : LockTele o n} →
                 Γ ≈ Δ ,ˡᵗ (Λ ++ˡᵗ Θ) →
                 Γ ≈ (Δ ,ˡᵗ Λ) ,ˡᵗ Θ
move-++ˡᵗ-left {Θ = ◇} splitΓ = split-◇ splitΓ
move-++ˡᵗ-left {Θ = Θ ,lock⟨ μ ⟩} (splitΓ ,lock⟨ .μ ⟩) = move-++ˡᵗ-left splitΓ ,lock⟨ μ ⟩


-- Same remark as for _≈_,ˡᵗ_.
infix 3 _≈_++ˡᵗ_
data _≈_++ˡᵗ_ : LockTele m n → LockTele m o → LockTele o n → Set where
  ◇ : {Λ : LockTele m n} → Λ ≈ Λ ++ˡᵗ ◇
  _,lock⟨_⟩ : {Λ : LockTele m n} {Θ : LockTele m o} {Ψ : LockTele o n} →
              Λ ≈ Θ ++ˡᵗ Ψ →
              (μ : Modality p n) →
              Λ ,lock⟨ μ ⟩ ≈ Θ ++ˡᵗ (Ψ ,lock⟨ μ ⟩)

≈++ˡᵗ-to-≡ : {Λ : LockTele m n} {Θ : LockTele m o} {Ψ : LockTele o n} →
             Λ ≈ Θ ++ˡᵗ Ψ → Λ ≡ Θ ++ˡᵗ Ψ
≈++ˡᵗ-to-≡ ◇ = refl
≈++ˡᵗ-to-≡ (splitΛ ,lock⟨ μ ⟩) = cong (_,lock⟨ μ ⟩) (≈++ˡᵗ-to-≡ splitΛ)

≈++ˡᵗ-right-cell : {Λ : LockTele m n} {Θ : LockTele m o} {Ψ : LockTele o n} →
                   Λ ≈ Θ ++ˡᵗ Ψ →
                   TwoCell (locksˡᵗ Λ) (locksˡᵗ (Θ ++ˡᵗ Ψ))
≈++ˡᵗ-right-cell splitΛ = eq-cell (cong locksˡᵗ (≈++ˡᵗ-to-≡ splitΛ))

≈++ˡᵗ-left-cell : {Λ : LockTele m n} {Θ : LockTele m o} {Ψ : LockTele o n} →
                   Λ ≈ Θ ++ˡᵗ Ψ →
                   TwoCell (locksˡᵗ (Θ ++ˡᵗ Ψ)) (locksˡᵗ Λ)
≈++ˡᵗ-left-cell splitΛ = eq-cell (cong locksˡᵗ (sym (≈++ˡᵗ-to-≡ splitΛ)))


record SplitTeleVarResult (Γ : Ctx n) (Λ : LockTele n m) (Δ : Ctx o) (Θ : LockTele o m) : Set where
  constructor split-lt-var-res
  field
    Ψ : LockTele o n
    is-sub : Θ ≈ Ψ ++ˡᵗ Λ
    splitΓ : Γ ≈ Δ ,ˡᵗ Ψ

split-tele-var : {Γ : Ctx n} (Λ : LockTele n m) {Δ : Ctx o} {μ : Modality p o} {T : Ty p} {Θ : LockTele o m} →
                 Γ ,ˡᵗ Λ ≈ Δ ,, μ ∣ x ∈ T ,ˡᵗ Θ →
                 SplitTeleVarResult Γ Λ (Δ ,, μ ∣ x ∈ T) Θ
split-tele-var ◇ {Θ = Θ} splitΓ = split-lt-var-res Θ ◇ splitΓ
split-tele-var (Λ ,lock⟨ μ ⟩) {Θ = Θ ,lock⟨ .μ ⟩} (splitΓΛ ,lock⟨ .μ ⟩) =
  let split-lt-var-res Ψ is-sub splitΓ = split-tele-var Λ splitΓΛ
  in split-lt-var-res Ψ (is-sub ,lock⟨ μ ⟩) splitΓ
