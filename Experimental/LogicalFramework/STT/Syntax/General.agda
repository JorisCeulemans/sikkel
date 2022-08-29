--------------------------------------------------
-- Definition of MSTT contexts, terms and their associated operations
--   The general syntax is parametrised by a type of names to represent
--   variables. It is not recommended to directly import this module,
--   but rather use MSTT.Syntax.Named.
--------------------------------------------------

module Experimental.LogicalFramework.STT.Syntax.General (Name : Set) where

open import Data.Maybe
open import Relation.Binary.PropositionalEquality as Ag

open import Experimental.LogicalFramework.STT.ModeTheory
open import Experimental.LogicalFramework.STT.Syntax.Types

private variable
  m n o p : Mode
  μ ρ κ φ : Modality m n
  T S : Ty m
  x y : Name


--------------------------------------------------
-- Definition of MSTT contexts and terms

infixl 4 _,,_∣_∈_
data Ctx (m : Mode) : Set where
  ◇ : Ctx m
  _,,_∣_∈_ : (Γ : Ctx m) (μ : Modality n m) (x : Name) (T : Ty n) → Ctx m
    -- ^ All variables have a name of type Name and appear under a modality.
  _,lock⟨_⟩ : (Γ : Ctx n) (μ : Modality m n) → Ctx m

private variable
  Γ Δ Θ : Ctx m


-- The predicate Var x μ T κ Γ expresses that a variable named x is
-- present in context Γ under modality μ with type T and with κ the
-- composition of all locks to the right of x. In other words,
-- Γ = Δ ,, μ ∣ x ∈ T ,, Θ for some Δ and Θ with locks(Θ) = κ. Note
-- that this is a proof-relevant predicate and names in Γ may not be
-- unique (but this is of course discouraged).  As a result, MSTT terms
-- internally represent variables using De Bruijn indices, but we do
-- keep track of the names of the variables.
data Var (x : Name) (μ : Modality n o) (T : Ty n) : Modality m o → Ctx m → Set where
  vzero : Var x μ T 𝟙 (Γ ,, μ ∣ x ∈ T)
  vsuc : Var x μ T κ Γ → Var x μ T κ (Γ ,, ρ ∣ y ∈ S)
  skip-lock : (ρ : Modality m p) → Var x μ T κ Γ → Var x μ T (κ ⓜ ρ) (Γ ,lock⟨ ρ ⟩)

infixl 50 _∙_
data Tm (Γ : Ctx m) : Ty m → Set where
  var' : {μ : Modality m n} (x : Name) {v : Var x μ T κ Γ} → TwoCell μ κ → Tm Γ T
  -- ^ When writing programs, one should not directly use var' but rather combine
  --   it with a decision procedure for Var, which will resolve the name.
  mod⟨_⟩_ : (μ : Modality n m) → Tm (Γ ,lock⟨ μ ⟩) T → Tm Γ ⟨ μ ∣ T ⟩
  mod-elim : (ρ : Modality o m) (μ : Modality n o) (x : Name)
             (t : Tm (Γ ,lock⟨ ρ ⟩) ⟨ μ ∣ T ⟩) (s : Tm (Γ ,, ρ ⓜ μ ∣ x ∈ T) S) →
             Tm Γ S
  lam[_∈_]_ : (x : Name) (T : Ty m) → Tm (Γ ,, 𝟙 ∣ x ∈ T) S → Tm Γ (T ⇛ S)
  _∙_ : Tm Γ (T ⇛ S) → Tm Γ T → Tm Γ S
  zero : Tm Γ Nat'
  suc : Tm Γ (Nat' ⇛ Nat')
  nat-elim : {A : Ty m} → Tm Γ A → Tm Γ (A ⇛ A) → Tm Γ (Nat' ⇛ A)
  true false : Tm Γ Bool'
  if : {A : Ty m} → Tm Γ Bool' → (t f : Tm Γ A) → Tm Γ A
  pair : Tm Γ T → Tm Γ S → Tm Γ (T ⊠ S)
  fst : Tm Γ (T ⊠ S) → Tm Γ T
  snd : Tm Γ (T ⊠ S) → Tm Γ S

syntax mod-elim ρ μ x t s = let⟨ ρ ⟩ mod⟨ μ ⟩ x ← t in' s


--------------------------------------------------
-- Traversals of MSTT terms

-- An element of type Trav Δ Γ can be used to tranform terms in Γ to
-- terms in Δ. For this to work, we must specify how such a traversal
-- acts on variables and provide a weakening (of both domain and
-- codomain) and lock operation for such traversals.
record TravStruct (Trav : ∀ {m} → Ctx m → Ctx m → Set) : Set where
  field
    vr : Var x μ T κ Γ → TwoCell μ κ → Trav Δ Γ → Tm Δ T
    wk : Trav Δ Γ → Trav (Δ ,, μ ∣ x ∈ T) (Γ ,, μ ∣ x ∈ T)
    lck : Trav Δ Γ → Trav (Δ ,lock⟨ μ ⟩) (Γ ,lock⟨ μ ⟩)

module _ (Trav : ∀ {m} → Ctx m → Ctx m → Set) (TS : TravStruct Trav) where
  open TravStruct TS

  traverse-tm : Tm Γ T → Trav Δ Γ → Tm Δ T
  traverse-tm (var' x {v} α) σ = vr v α σ
  traverse-tm (mod⟨ μ ⟩ t) σ = mod⟨ μ ⟩ traverse-tm t (lck σ)
  traverse-tm (mod-elim ρ μ x t s) σ = mod-elim ρ μ x (traverse-tm t (lck σ)) (traverse-tm s (wk σ))
  traverse-tm (lam[ x ∈ T ] s) σ = lam[ x ∈ T ] traverse-tm s (wk σ)
  traverse-tm (f ∙ t) σ = traverse-tm f σ ∙ traverse-tm t σ
  traverse-tm zero σ = zero
  traverse-tm suc σ = suc
  traverse-tm (nat-elim z s) σ = nat-elim (traverse-tm z σ) (traverse-tm s σ)
  traverse-tm true σ = true
  traverse-tm false σ = false
  traverse-tm (if b t f) σ = if (traverse-tm b σ) (traverse-tm t σ) (traverse-tm f σ)
  traverse-tm (pair t s) σ = pair (traverse-tm t σ) (traverse-tm s σ)
  traverse-tm (fst p) σ = fst (traverse-tm p σ)
  traverse-tm (snd p) σ = snd (traverse-tm p σ)


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

skip-locks : {Γ : Ctx m} (Λ : LockTele m n) → Var x μ T κ Γ → Var x μ T (κ ⓜ locks-ltel Λ) (Γ ++ltel Λ)
skip-locks ◇ v = Ag.subst (λ - → Var _ _ _ - _) (sym mod-unitʳ) v
skip-locks {κ = κ} (Λ ,lock⟨ μ ⟩) v =
  Ag.subst (λ - → Var _ _ _ - _) (mod-assoc {μ = κ}) (skip-lock μ (skip-locks Λ v))

-- If we have a variable in Γ ++ltel Λ, we actually have a variable in
-- Γ with less locks to the right of it.
record SplitLtelVar (Γ : Ctx m) (Λ : LockTele m n) (x : Name) (μ : Modality o p) (T : Ty o) (κ : Modality n p) : Set where
  constructor ltel-splitting
  field
    κ' : Modality m p
    v' : Var x μ T κ' Γ
    same-locks : κ' ⓜ locks-ltel Λ ≡ κ

split-ltel-var : (Λ : LockTele m n) → Var x μ T κ (Γ ++ltel Λ) → SplitLtelVar Γ Λ x μ T κ
split-ltel-var {κ = κ} ◇ v = ltel-splitting κ v mod-unitʳ
split-ltel-var (Λ ,lock⟨ ρ ⟩) (skip-lock .ρ v) =
  let ltel-splitting κ' v' same-locks = split-ltel-var Λ v
  in ltel-splitting κ' v' (trans (sym (mod-assoc {μ = κ'})) (cong (_ⓜ ρ) same-locks))


--------------------------------------------------
-- Renamings of MSTT terms

-- In order to avoid termination issues, we first define atomic
-- renamings and specify how they can be applied to terms. A genuine
-- renaming will then consist of a (possibly empty) well-typed list of
-- atomic renamigs, representing the composition of these atomic
-- renamings. Note that in this way, renamings are not uniquely
-- represented by values of the data type Ren, which seems to be
-- impossible.
data AtomicRen : Ctx m → Ctx m → Set where
  [] : AtomicRen Γ ◇
  _∷_,_/_ : AtomicRen Γ Δ → (y : Name) → Var y μ T 𝟙 Γ → (x : Name) → AtomicRen Γ (Δ ,, μ ∣ x ∈ T)
  _⊚π : AtomicRen Γ Δ → AtomicRen (Γ ,, μ ∣ x ∈ T) Δ
  _,lock⟨_⟩ : AtomicRen Γ Δ → (μ : Modality n m) → AtomicRen (Γ ,lock⟨ μ ⟩) (Δ ,lock⟨ μ ⟩)
  atomic-key : (Λ₁ Λ₂ : LockTele n m) → TwoCell (locks-ltel Λ₂) (locks-ltel Λ₁) → AtomicRen (Γ ++ltel Λ₁) (Γ ++ltel Λ₂)

id-atomic-ren : AtomicRen Γ Γ
id-atomic-ren = atomic-key ◇ ◇ id-cell

lift-atomic-ren : AtomicRen Γ Δ → AtomicRen (Γ ,, μ ∣ x ∈ T) (Δ ,, μ ∣ x ∈ T)
lift-atomic-ren {x = x} σ = (σ ⊚π) ∷ x , vzero / x

-- When a (atomic) renaming acts on a variable, it does not need to
-- have the same name or the same locks to the right in the
-- context. However, when the locks change, we can provide a two-cell
-- between the old and new locks.
record RenVarResult (μ : Modality o n) (T : Ty o) (κ : Modality m n) (Γ : Ctx m) : Set where
  constructor renvar
  field
    new-name : Name
    new-locks : Modality m n
    two-cell : TwoCell κ new-locks
    v : Var new-name μ T new-locks Γ

atomic-ren-var' : Var x μ T κ Δ → AtomicRen Γ Δ → RenVarResult μ T κ Γ
atomic-ren-var' {x = x} v (atomic-key Λ₁ Λ₂ α) =
  let ltel-splitting κ' v' same-locks = split-ltel-var Λ₂ v
  in renvar x (κ' ⓜ locks-ltel Λ₁) (Ag.subst (λ - → TwoCell - (κ' ⓜ locks-ltel Λ₁)) same-locks (id-cell ⓣ-hor α)) (skip-locks Λ₁ v')
atomic-ren-var' vzero (σ ∷ y , w / x) = renvar y _ id-cell w
atomic-ren-var' (vsuc v) (σ ∷ y , w / x) = atomic-ren-var' v σ
atomic-ren-var' v (σ ⊚π) = let renvar y κ' α w = atomic-ren-var' v σ in renvar y κ' α (vsuc w)
atomic-ren-var' (skip-lock .μ v) (σ ,lock⟨ μ ⟩) =
  let renvar y κ' α w = atomic-ren-var' v σ
  in renvar y (κ' ⓜ μ) (α ⓣ-hor id-cell) (skip-lock μ w)

atomic-ren-var : Var x μ T κ Δ → TwoCell μ κ → AtomicRen Γ Δ → Tm Γ T
atomic-ren-var v α σ = let renvar y κ' β w = atomic-ren-var' v σ in var' y {w} (β ⓣ-vert α)

-- The type family AtomicRen has enough structure to traverse terms.
AtomicRenTrav : TravStruct AtomicRen
TravStruct.vr AtomicRenTrav = atomic-ren-var
TravStruct.wk AtomicRenTrav = lift-atomic-ren
TravStruct.lck AtomicRenTrav {μ = μ} σ = σ ,lock⟨ μ ⟩

atomic-rename-tm : Tm Δ T → AtomicRen Γ Δ → Tm Γ T
atomic-rename-tm = traverse-tm AtomicRen AtomicRenTrav


-- An actual renaming is a well-typed (snoc) list of atomic renamings.
data Ren : Ctx m → Ctx m → Set where
  id : Ren Γ Γ
  _⊚a_ : Ren Δ Θ → AtomicRen Γ Δ → Ren Γ Θ

rename-tm : Tm Δ T → Ren Γ Δ → Tm Γ T
rename-tm t id = t
rename-tm t (τ ⊚a σᵃ) = atomic-rename-tm (rename-tm t τ) σᵃ

lift-ren : Ren Γ Δ → Ren (Γ ,, μ ∣ x ∈ T) (Δ ,, μ ∣ x ∈ T)
lift-ren id = id
lift-ren (σ ⊚a τᵃ) = lift-ren σ ⊚a lift-atomic-ren τᵃ

-- All MTT constructors for producing renamings, can be implemented as
-- operations producing something of type Ren.
[]r : Ren Γ ◇
[]r = id ⊚a []

π-ren : Ren (Γ ,, μ ∣ x ∈ T) Γ
π-ren = id ⊚a (id-atomic-ren ⊚π)

_∷ʳ_,_/_ : Ren Γ Δ → (y : Name) → Var y μ T 𝟙 Γ → (x : Name) → Ren Γ (Δ ,, μ ∣ x ∈ T)
σ ∷ʳ y , w / x = lift-ren σ ⊚a (id-atomic-ren ∷ y , w / x)

_,rlock⟨_⟩ : Ren Γ Δ → (μ : Modality m n) → Ren (Γ ,lock⟨ μ ⟩) (Δ ,lock⟨ μ ⟩)
id ,rlock⟨ μ ⟩ = id
(σ ⊚a τᵃ) ,rlock⟨ μ ⟩ = (σ ,rlock⟨ μ ⟩) ⊚a (τᵃ ,lock⟨ μ ⟩)

key-ren : (Λ₁ Λ₂ : LockTele n m) → TwoCell (locks-ltel Λ₂) (locks-ltel Λ₁) → Ren (Γ ++ltel Λ₁) (Γ ++ltel Λ₂)
key-ren Λ₁ Λ₂ α = id ⊚a atomic-key Λ₁ Λ₂ α

_⊚r_ : Ren Δ Θ → Ren Γ Δ → Ren Γ Θ
τ ⊚r id = τ
τ ⊚r (σ ⊚a σᵃ) = (τ ⊚r σ) ⊚a σᵃ

rename-tm-⊚ : {τ : Ren Δ Θ} (σ : Ren Γ Δ) {t : Tm Θ T} → rename-tm (rename-tm t τ) σ ≡ rename-tm t (τ ⊚r σ)
rename-tm-⊚ id = refl
rename-tm-⊚ (σ ⊚a σᵃ) = cong (λ - → atomic-rename-tm - σᵃ) (rename-tm-⊚ σ)

-- Some special renamings for introducing/removing a trivial lock and
-- for (un)fusing locks.
lock𝟙-ren : Ren (Γ ,lock⟨ 𝟙 ⟩) Γ
lock𝟙-ren = id ⊚a atomic-key (◇ ,lock⟨ 𝟙 ⟩) ◇ (Ag.subst (TwoCell 𝟙) (sym mod-unitʳ) id-cell)

unlock𝟙-ren : Ren Γ (Γ ,lock⟨ 𝟙 ⟩)
unlock𝟙-ren = id ⊚a atomic-key ◇ (◇ ,lock⟨ 𝟙 ⟩) (Ag.subst (λ - → TwoCell - 𝟙) (sym mod-unitʳ) id-cell)

lockⓜ-ren : Ren (Γ ,lock⟨ μ ⓜ ρ ⟩) (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩)
lockⓜ-ren {μ = μ} {ρ = ρ} = id ⊚a atomic-key (◇ ,lock⟨ μ ⓜ ρ ⟩) (◇ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) (Ag.subst (TwoCell _) (mod-assoc {μ = 𝟙}) id-cell)

unlockⓜ-ren : Ren (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) (Γ ,lock⟨ μ ⓜ ρ ⟩)
unlockⓜ-ren {μ = μ} {ρ = ρ} = id ⊚a atomic-key (◇ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) (◇ ,lock⟨ μ ⓜ ρ ⟩) (Ag.subst (TwoCell _) (sym (mod-assoc {μ = 𝟙})) id-cell)

-- Specific opertations for weakening a term and for the functorial
-- behaviour of locks.
weaken-tm : Tm Γ T → Tm (Γ ,, μ ∣ x ∈ S) T
weaken-tm t = rename-tm t π-ren

lock𝟙-tm : Tm Γ T → Tm (Γ ,lock⟨ 𝟙 ⟩) T
lock𝟙-tm t = rename-tm t (lock𝟙-ren)

unlock𝟙-tm : Tm (Γ ,lock⟨ 𝟙 ⟩) T → Tm Γ T
unlock𝟙-tm t = rename-tm t (unlock𝟙-ren)

lockⓜ-tm : Tm (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) T → Tm (Γ ,lock⟨ μ ⓜ ρ ⟩) T
lockⓜ-tm t = rename-tm t lockⓜ-ren

unlockⓜ-tm : Tm (Γ ,lock⟨ μ ⓜ ρ ⟩) T → Tm (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) T
unlockⓜ-tm t = rename-tm t unlockⓜ-ren


{-

--------------------------------------------------
-- Syntactic substitutions

data LockFreeTele (m : Mode) : Set where
  ◇t : LockFreeTele m
  _,,_∣_∈_ : LockFreeTele m → Modality n m → Name → Ty n → LockFreeTele m

_++lft_ : Ctx m → LockFreeTele m → Ctx m
Γ ++lft ◇t = Γ
Γ ++lft (Δ ,, μ ∣ x ∈ T) = (Γ ++lft Δ) ,, μ ∣ x ∈ T

-- With the following data type, there are multiple ways to represent
-- the same substitution. This is not a problem since we will never
-- compare substitutions (only apply them to terms and compute
-- immediately). Having a constructor for e.g. the identity seems more
-- efficient than implementing it (but this claim needs justification).
data Subst : Ctx m → Ctx m → Set where
  [] : Subst Γ ◇
  _∷_/_ : Subst Δ Γ → Tm (Δ ,lock⟨ μ ⟩) T → (x : Name) → Subst Δ (Γ ,, μ ∣ x ∈ T)
  id-subst : (Γ : Ctx m) → Subst Γ Γ
  _⊚πs⟨_⟩ : Subst Δ Γ → (Θ : LockFreeTele m) → Subst (Δ ++lft Θ) Γ
  _,lock⟨_⟩ : Subst Δ Γ → (μ : Modality m n) → Subst (Δ ,lock⟨ μ ⟩) (Γ ,lock⟨ μ ⟩)
  key : TwoCell μ ρ → Subst (Γ ,lock⟨ ρ ⟩) (Γ ,lock⟨ μ ⟩)

π : Subst (Γ ,, μ ∣ x ∈ T) Γ
π = id-subst _ ⊚πs⟨ _ ⟩

_⊚π : Subst Δ Γ → Subst (Δ ,, μ ∣ x ∈ T) Γ
σ ⊚π = σ ⊚πs⟨ _ ⟩

_⊹⟨_⟩ : Subst Δ Γ → (x : Name) → Subst (Δ ,, μ ∣ x ∈ T) (Γ ,, μ ∣ x ∈ T)
σ ⊹⟨ x ⟩ = (σ ⊚π) ∷ var' x {skip-lock _ vzero} (Ag.subst (TwoCell _) (sym mod-unitˡ) id-cell) / x

_/_ : Tm (Γ ,lock⟨ μ ⟩) T → (x : Name) → Subst Γ (Γ ,, μ ∣ x ∈ T)
t / x = id-subst _ ∷ t / x


--------------------------------------------------
-- Applying a substitution to a term
--   Note that the operation _[_]tm is automatically capture-avoiding
--   since it only makes use of the De Bruijn indices, not of names.

-- We will use the following view pattern in the implementation of
-- substitution for terms, in order to treat some substitutions
-- specially.
data SpecialSubst : Subst Γ Δ → Set where
  id-subst : (Γ : Ctx m) → SpecialSubst (id-subst Γ)
  _⊚πs⟨_⟩ : {Γ Δ : Ctx m} (σ : Subst Γ Δ) → (Θ : LockFreeTele m) → SpecialSubst (σ ⊚πs⟨ Θ ⟩)

is-special-subst? : (σ : Subst Γ Δ) → Maybe (SpecialSubst σ)
is-special-subst? []           = nothing
is-special-subst? (σ ∷ t / x)  = nothing
is-special-subst? (id-subst Γ) = just (id-subst Γ)
is-special-subst? (σ ⊚πs⟨ Θ ⟩) = just (σ ⊚πs⟨ Θ ⟩)
is-special-subst? (σ ,lock⟨ μ ⟩) = nothing
is-special-subst? (key α) = nothing

subst-var : {Γ : Ctx m} {μ : Modality n o} {κ : Modality m o} (v : Var x μ T κ Γ) →
            (ρ : Modality n m) → TwoCell μ (κ ⓜ ρ) → Subst Δ Γ → Tm (Δ ,lock⟨ ρ ⟩) T
subst-var {x = x} v ρ α (id-subst _) = var' x {skip-lock ρ v} α
subst-var v ρ α (σ ⊚πs⟨ ◇t ⟩) = subst-var v ρ α σ
subst-var v ρ α (σ ⊚πs⟨ Θ ,, _ ∣ _ ∈ _ ⟩) = {!!}
subst-var vzero ρ α (σ ∷ t / x) = {!t [ key α ]tm!}
subst-var (vsuc v) ρ α (σ ∷ t / x) = subst-var v ρ α σ
subst-var (skip-lock .μ v) ρ α (σ ,lock⟨ μ ⟩) = {!subst-var v (μ ⓜ ρ) {!α!} σ!}
subst-var {x = x} (skip-lock _ v) ρ α (key β) = var' x {skip-lock _ (skip-lock _ v)} (((id-cell ⓣ-hor β) ⓣ-hor id-cell {_}{_}{ρ}) ⓣ-vert α)

{-
subst-var : (v : Var x μ T κ Γ) → TwoCell μ κ → Subst Δ Γ → Tm Δ T
subst-var {x = x} v α (id-subst _) = var' x {v = v} α
subst-var v α (σ ⊚πs⟨ ◇t ⟩) = subst-var v α σ
subst-var v α (σ ⊚πs⟨ Θ ,, _ ∣ _ ∈ _ ⟩) = {!!}
subst-var vzero α (σ ∷ t / x) = {!t [ key α ]tm!}
subst-var (vsuc v) α (σ ∷ t / x) = subst-var v α σ
subst-var (skip-lock .μ v) α (σ ,lock⟨ μ ⟩) = {!subst-var v ? ?!}
subst-var {x = x} (skip-lock μ v) α (key {ρ = ρ} β) = var' x {v = skip-lock ρ v} ((id-cell ⓣ-hor β) ⓣ-vert α)
-}
{-
subst-var {x = x} v (id-subst Γ) = var' x {v}
subst-var v         (σ ⊚πs⟨ ◇ ⟩) = subst-var v σ
subst-var v         (σ ⊚πs⟨ Δ ,, _ ∈ T ⟩) = weaken-tm (subst-var v (σ ⊚πs⟨ Δ ⟩))
subst-var vzero     (σ ∷ t / x) = t
subst-var (vsuc v)  (σ ∷ s / x) = subst-var v σ
-}
_[_]tm : Tm Γ T → Subst Δ Γ → Tm Δ T
t [ σ ]tm with is-special-subst? σ
(t [ .(id-subst Γ) ]tm)  | just (id-subst Γ) = t
(t [ .(σ ⊚πs⟨ Θ ⟩) ]tm)  | just (σ ⊚πs⟨ Θ ⟩) = {!multi-weaken-tm Θ (t [ σ ]tm)!}
(var' x {v} α) [ σ ]tm   | nothing = {!subst-var v α σ!}
(lam[ x ∈ T ] t) [ σ ]tm | nothing = lam[ x ∈ T ] (t [ σ ⊹⟨ x ⟩ ]tm)
(f ∙ t) [ σ ]tm          | nothing = (f [ σ ]tm) ∙ (t [ σ ]tm)
zero [ σ ]tm             | nothing = zero
suc [ σ ]tm              | nothing = suc
(nat-elim a f) [ σ ]tm   | nothing = nat-elim (a [ σ ]tm) (f [ σ ]tm)
true [ σ ]tm             | nothing = true
false [ σ ]tm            | nothing = false
(if b t f) [ σ ]tm       | nothing = if (b [ σ ]tm) (t [ σ ]tm) (f [ σ ]tm)
(pair t s) [ σ ]tm       | nothing = pair (t [ σ ]tm) (s [ σ ]tm)
(fst p) [ σ ]tm          | nothing = fst (p [ σ ]tm)
(snd p) [ σ ]tm          | nothing = snd (p [ σ ]tm)
(mod⟨ μ ⟩ t) [ σ ]tm      | nothing = mod⟨ μ ⟩ (t [ σ ,lock⟨ μ ⟩ ]tm)
(mod-elim ρ μ x t s) [ σ ]tm | nothing = mod-elim ρ μ x (t [ σ ,lock⟨ ρ ⟩ ]tm) (s [ σ ⊹⟨ x ⟩ ]tm)


--------------------------------------------------
-- Proving that substituting the most recently added variable in a
--   weakened term has no effect.

multi⊹ : (Θ : Ctx) → Subst Γ Δ → Subst (Γ ++tel Θ) (Δ ++tel Θ)
multi⊹ ◇            σ = σ
multi⊹ (Θ ,, x ∈ T) σ = (multi⊹ Θ σ) ⊹⟨ x ⟩

cong₃ : {A B C D : Set} (f : A → B → C → D)
        {a a' : A} {b b' : B} {c c' : C} →
        a ≡ a' → b ≡ b' → c ≡ c' →
        f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

var-weaken-subst-trivial-multi : (Θ : Ctx) (v : Var x (Γ ++tel Θ) T) {s : Tm Γ S} →
  (var' x {mid-weaken-var Θ v}) [ multi⊹ Θ (s / y) ]tm ≡ var' x {v}
var-weaken-subst-trivial-multi ◇ v = refl
var-weaken-subst-trivial-multi (Θ ,, x ∈ T) vzero = refl
var-weaken-subst-trivial-multi (◇ ,, x ∈ T) (vsuc v) = refl
var-weaken-subst-trivial-multi (Θ ,, x ∈ T ,, y ∈ S) (vsuc v) = cong weaken-tm (var-weaken-subst-trivial-multi (Θ ,, x ∈ T) v)

tm-weaken-subst-trivial-multi : (Θ : Ctx) (t : Tm (Γ ++tel Θ) T) {s : Tm Γ S} → (mid-weaken-tm Θ t) [ multi⊹ Θ (s / x) ]tm ≡ t
tm-weaken-subst-trivial-multi ◇ (var' x {_}) = refl
tm-weaken-subst-trivial-multi ◇ (lam[ _ ∈ _ ] t) = cong (lam[ _ ∈ _ ]_) (tm-weaken-subst-trivial-multi (◇ ,, _ ∈ _) t)
tm-weaken-subst-trivial-multi ◇ (f ∙ t) = cong₂ _∙_ (tm-weaken-subst-trivial-multi ◇ f) (tm-weaken-subst-trivial-multi ◇ t)
tm-weaken-subst-trivial-multi ◇ zero = refl
tm-weaken-subst-trivial-multi ◇ suc = refl
tm-weaken-subst-trivial-multi ◇ (nat-elim a f) = cong₂ nat-elim (tm-weaken-subst-trivial-multi ◇ a) (tm-weaken-subst-trivial-multi ◇ f)
tm-weaken-subst-trivial-multi ◇ true = refl
tm-weaken-subst-trivial-multi ◇ false = refl
tm-weaken-subst-trivial-multi ◇ (if b t f) =
  cong₃ if (tm-weaken-subst-trivial-multi ◇ b) (tm-weaken-subst-trivial-multi ◇ t) (tm-weaken-subst-trivial-multi ◇ f)
tm-weaken-subst-trivial-multi ◇ (pair t s) = cong₂ pair (tm-weaken-subst-trivial-multi ◇ t) (tm-weaken-subst-trivial-multi ◇ s)
tm-weaken-subst-trivial-multi ◇ (fst p) = cong fst (tm-weaken-subst-trivial-multi ◇ p)
tm-weaken-subst-trivial-multi ◇ (snd p) = cong snd (tm-weaken-subst-trivial-multi ◇ p)
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (var' _ {v}) = var-weaken-subst-trivial-multi (Θ ,, _ ∈ T) v
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (lam[ _ ∈ _ ] t) = cong (lam[ _ ∈ _ ]_) (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T ,, _ ∈ _) t)
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (f ∙ t) = cong₂ _∙_ (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) f) (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) t)
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) zero = refl
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) suc = refl
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (nat-elim a f) = cong₂ nat-elim (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) a) (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) f)
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) true = refl
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) false = refl
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (if b t f) =
  cong₃ if (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) b) (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) t) (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) f)
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (pair t s) = cong₂ pair (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) t) (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) s)
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (fst p) = cong fst (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) p)
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (snd p) = cong snd (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) p)

tm-weaken-subst-trivial : (t : Tm Γ T) (s : Tm Γ S) → (t [ π ]tm) [ s / x ]tm ≡ t
tm-weaken-subst-trivial t s = tm-weaken-subst-trivial-multi ◇ t
-}

{-
mod-elim' : (μ : Modality n m) (x : Name) (t : Tm Γ ⟨ μ ∣ T ⟩) (s : Tm (Γ ,, μ ∣ x ∈ T) S) → Tm Γ S
mod-elim' {Γ = Γ} {T = T} {S = S} μ x t s =
  mod-elim 𝟙 μ x {!!} (Ag.subst (λ - → Tm (Γ ,, - ∣ x ∈ T) S) (sym mod-unitˡ) s)

syntax mod-elim' μ x t s = let' mod⟨ μ ⟩ x ← t in' s
-}
