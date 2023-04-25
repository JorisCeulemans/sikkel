--------------------------------------------------
-- Definition of MSTT contexts, terms and their associated operations
--   The general syntax is parametrised by a type of names to represent
--   variables. It is not recommended to directly import this module,
--   but rather use MSTT.Syntax.Named.
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.ModeTheory

module Experimental.LogicalFramework.MSTT.Syntax.General (ℳ : ModeTheory) (Name : Set) where

open import Data.Maybe
open import Relation.Binary.PropositionalEquality as Ag

open ModeTheory ℳ

open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ

private variable
  m n o p : Mode
  μ ρ κ φ : Modality m n
  T S : Ty m
  x y : Name


--------------------------------------------------
-- Definition of MSTT contexts and terms

infixl 4 _,,_∣_∈_ _,lock⟨_⟩
data Ctx (m : Mode) : Set where
  ◇ : Ctx m
  _,,_∣_∈_ : (Γ : Ctx m) (μ : Modality n m) (x : Name) (T : Ty n) → Ctx m
    -- ^ All variables have a name of type Name and appear under a modality.
  _,lock⟨_⟩ : (Γ : Ctx n) (μ : Modality m n) → Ctx m

pattern _,,_∈_ Γ x T = Γ ,, 𝟙 ∣ x ∈ T

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
data Tm : Ctx m → Ty m → Set where
  var' : {μ : Modality m n} (x : Name) {v : Var x μ T κ Γ} → TwoCell μ κ → Tm Γ T
  -- ^ When writing programs, one should not directly use var' but rather combine
  --   it with a decision procedure for Var, which will resolve the name.
  mod⟨_⟩_ : (μ : Modality n m) → Tm (Γ ,lock⟨ μ ⟩) T → Tm Γ ⟨ μ ∣ T ⟩
  mod-elim : (ρ : Modality o m) (μ : Modality n o) (x : Name)
             (t : Tm (Γ ,lock⟨ ρ ⟩) ⟨ μ ∣ T ⟩) (s : Tm (Γ ,, ρ ⓜ μ ∣ x ∈ T) S) →
             Tm Γ S
  lam[_∣_∈_]_ : (μ : Modality n m) (x : Name) (T : Ty n) → Tm (Γ ,, μ ∣ x ∈ T) S → Tm Γ (⟨ μ ∣ T ⟩⇛ S)
  _∙_ : {μ : Modality n m} → Tm Γ (⟨ μ ∣ T ⟩⇛ S) → Tm (Γ ,lock⟨ μ ⟩) T → Tm Γ S
  zero : Tm Γ Nat'
  suc : Tm Γ Nat' → Tm Γ Nat'
  nat-elim : {A : Ty m} → Tm Γ A → Tm Γ (A ⇛ A) → Tm Γ Nat' → Tm Γ A
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
-- acts on variables and provide a lifting and lock operation for such
-- traversals.
record TravStruct (Trav : ∀ {m} → Ctx m → Ctx m → Set) : Set where
  field
    vr : Var x μ T κ Δ → TwoCell μ κ → Trav Γ Δ → Tm Γ T
    lift : Trav Γ Δ → Trav (Γ ,, μ ∣ x ∈ T) (Δ ,, μ ∣ x ∈ T)
    lock : Trav Γ Δ → Trav (Γ ,lock⟨ μ ⟩) (Δ ,lock⟨ μ ⟩)

  traverse-tm : Tm Δ T → Trav Γ Δ → Tm Γ T
  traverse-tm (var' x {v} α) σ = vr v α σ
  traverse-tm (mod⟨ μ ⟩ t) σ = mod⟨ μ ⟩ traverse-tm t (lock σ)
  traverse-tm (mod-elim ρ μ x t s) σ = mod-elim ρ μ x (traverse-tm t (lock σ)) (traverse-tm s (lift σ))
  traverse-tm (lam[ μ ∣ x ∈ T ] s) σ = lam[ μ ∣ x ∈ T ] traverse-tm s (lift σ)
  traverse-tm (f ∙ t) σ = traverse-tm f σ ∙ traverse-tm t (lock σ)
  traverse-tm zero σ = zero
  traverse-tm (suc t) σ = suc (traverse-tm t σ)
  traverse-tm (nat-elim z s n) σ = nat-elim (traverse-tm z σ) (traverse-tm s σ) (traverse-tm n σ)
  traverse-tm true σ = true
  traverse-tm false σ = false
  traverse-tm (if b t f) σ = if (traverse-tm b σ) (traverse-tm t σ) (traverse-tm f σ)
  traverse-tm (pair t s) σ = pair (traverse-tm t σ) (traverse-tm s σ)
  traverse-tm (fst p) σ = fst (traverse-tm p σ)
  traverse-tm (snd p) σ = snd (traverse-tm p σ)

open TravStruct using (traverse-tm)


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
  Ag.subst (λ - → Var _ _ _ - _) (mod-assoc κ) (skip-lock μ (skip-locks Λ v))

-- If we have a variable in Γ ++ltel Λ, we actually have a variable in
-- Γ with less locks to the right of it.
record SplitLtelVar (Γ : Ctx m) (Λ : LockTele m n) (x : Name) (μ : Modality o p) (T : Ty o) (κ : Modality n p) : Set where
  constructor ltel-splitting
  field
    κ/Λ : Modality m p
    v' : Var x μ T κ/Λ Γ
    lock-div : κ/Λ ⓜ locks-ltel Λ ≡ κ

split-ltel-var : (Λ : LockTele m n) → Var x μ T κ (Γ ++ltel Λ) → SplitLtelVar Γ Λ x μ T κ
split-ltel-var {κ = κ} ◇ v = ltel-splitting κ v mod-unitʳ
split-ltel-var (Λ ,lock⟨ ρ ⟩) (skip-lock {κ = κ} .ρ v) =
  let ltel-splitting κ/Λ v' lock-div = split-ltel-var Λ v
  in  ltel-splitting κ/Λ v' (trans (sym (mod-assoc κ/Λ)) (cong (_ⓜ ρ) lock-div))


--------------------------------------------------
-- Common structure of MSTT renaming and substitution Renaming and
--   substitution can be seen as very similar operations, where the
--   former assigns variables to variables and the latter terms to
--   variables (taking into account the modal structure of
--   contexts). Hence, we describe them at once with a parameter of
--   type RenSubData that will later be instatiated with variables to
--   obtain renamings and terms to obtain substitutions.

RenSubData : Set₁
RenSubData = {m n : Mode} → Modality n m → Ty n → Ctx m → Set

module AtomicRenSubDef (V : RenSubData) where

  -- In order to avoid termination issues, we first define atomic
  -- renamings/substitutions and specify how they can be applied to
  -- terms. A genuine renaming/substitution will then consist of a
  -- (possibly empty) well-typed list of atomic
  -- renamigs/substitutions, representing the composition of these
  -- atomic renamings/substitutions. Note that in this way,
  -- renamings/substitutions are not uniquely represented by values of
  -- the data type RenSub, which seems to be impossible.
  data AtomicRenSub : Ctx m → Ctx m → Set where
    [] : AtomicRenSub Γ ◇
    _∷_/_ : AtomicRenSub Γ Δ → V μ T Γ → (x : Name) → AtomicRenSub Γ (Δ ,, μ ∣ x ∈ T)
    _⊚π : AtomicRenSub Γ Δ → AtomicRenSub (Γ ,, μ ∣ x ∈ T) Δ
    _,lock⟨_⟩ : AtomicRenSub Γ Δ → (μ : Modality n m) → AtomicRenSub (Γ ,lock⟨ μ ⟩) (Δ ,lock⟨ μ ⟩)
    atomic-key : (Λ₁ Λ₂ : LockTele n m) → TwoCell (locks-ltel Λ₂) (locks-ltel Λ₁) → AtomicRenSub (Γ ++ltel Λ₁) (Γ ++ltel Λ₂)

-- In order to obtain useful results for renamings/substitutions, the
-- type family representing the data assigned to variables must be
-- equipped with some extra structure.
record RenSubDataStructure (V : RenSubData) : Set where
  field
    newV : ∀ {x m n} {μ : Modality n m} {T : Ty n} {Γ : Ctx m} → V μ T (Γ ,, μ ∣ x ∈ T)
    atomic-rensub-lookup-var : ∀ {x m n} {Γ Δ : Ctx m} {μ κ : Modality m n} {T : Ty m} →
                               Var x μ T κ Δ → TwoCell μ κ → AtomicRenSubDef.AtomicRenSub V Γ Δ → Tm Γ T

module AtomicRenSub
  (V : RenSubData)
  (rensub-struct : RenSubDataStructure V)
  where

  open AtomicRenSubDef V public
  open RenSubDataStructure rensub-struct

  id-atomic-rensub : AtomicRenSub Γ Γ
  id-atomic-rensub = atomic-key ◇ ◇ id-cell

  lift-atomic-rensub : AtomicRenSub Γ Δ → AtomicRenSub (Γ ,, μ ∣ x ∈ T) (Δ ,, μ ∣ x ∈ T)
  lift-atomic-rensub {x = x} σ = (σ ⊚π) ∷ newV / x

  AtomicRenSubTrav : TravStruct AtomicRenSub
  TravStruct.vr AtomicRenSubTrav = atomic-rensub-lookup-var
  TravStruct.lift AtomicRenSubTrav = lift-atomic-rensub
  TravStruct.lock AtomicRenSubTrav {μ = μ} σ = σ ,lock⟨ μ ⟩

  atomic-rensub-tm : Tm Δ T → AtomicRenSub Γ Δ → Tm Γ T
  atomic-rensub-tm = traverse-tm AtomicRenSubTrav


module RenSub
  (V : RenSubData)
  (rensub-struct : RenSubDataStructure V)
  where

  open AtomicRenSub V rensub-struct

  -- An actual renaming/substitution is a well-typed (snoc) list of atomic renamings/substitutions.
  data RenSub : Ctx m → Ctx m → Set where
    id : RenSub Γ Γ
    _⊚a_ : RenSub Δ Θ → AtomicRenSub Γ Δ → RenSub Γ Θ

  rensub-tm : Tm Δ T → RenSub Γ Δ → Tm Γ T
  rensub-tm t id = t
  rensub-tm t (τ ⊚a σᵃ) = atomic-rensub-tm (rensub-tm t τ) σᵃ

  lift-rensub : RenSub Γ Δ → RenSub (Γ ,, μ ∣ x ∈ T) (Δ ,, μ ∣ x ∈ T)
  lift-rensub id = id
  lift-rensub (σ ⊚a τᵃ) = lift-rensub σ ⊚a lift-atomic-rensub τᵃ

  -- All MTT constructors for producing renamings/substitutions, can
  -- be implemented as operations producing something of type RenSub.
  []rs : RenSub Γ ◇
  []rs = id ⊚a []

  π-rensub : RenSub (Γ ,, μ ∣ x ∈ T) Γ
  π-rensub = id ⊚a (id-atomic-rensub ⊚π)

  -- Case splitting on the first argument is not strictly necessary
  -- here, but it avoids 1 additional term traversal in the second case.
  _∷ʳˢ_/_ : RenSub Γ Δ → V μ T Γ → (x : Name) → RenSub Γ (Δ ,, μ ∣ x ∈ T)
  id        ∷ʳˢ v / x = id ⊚a (id-atomic-rensub ∷ v / x)
  (σ ⊚a τᵃ) ∷ʳˢ v / x = lift-rensub σ ⊚a (τᵃ ∷ v / x)

  _,rslock⟨_⟩ : RenSub Γ Δ → (μ : Modality m n) → RenSub (Γ ,lock⟨ μ ⟩) (Δ ,lock⟨ μ ⟩)
  id        ,rslock⟨ μ ⟩ = id
  (σ ⊚a τᵃ) ,rslock⟨ μ ⟩ = (σ ,rslock⟨ μ ⟩) ⊚a (τᵃ ,lock⟨ μ ⟩)

  key-rensub : (Λ₁ Λ₂ : LockTele n m) → TwoCell (locks-ltel Λ₂) (locks-ltel Λ₁) → RenSub (Γ ++ltel Λ₁) (Γ ++ltel Λ₂)
  key-rensub Λ₁ Λ₂ α = id ⊚a atomic-key Λ₁ Λ₂ α

  _⊚rs_ : RenSub Δ Θ → RenSub Γ Δ → RenSub Γ Θ
  τ ⊚rs id = τ
  τ ⊚rs (σ ⊚a σᵃ) = (τ ⊚rs σ) ⊚a σᵃ

  rensub-tm-⊚ : {τ : RenSub Δ Θ} (σ : RenSub Γ Δ) {t : Tm Θ T} → rensub-tm (rensub-tm t τ) σ ≡ rensub-tm t (τ ⊚rs σ)
  rensub-tm-⊚ id = refl
  rensub-tm-⊚ (σ ⊚a σᵃ) = cong (λ - → atomic-rensub-tm - σᵃ) (rensub-tm-⊚ σ)


--------------------------------------------------
-- Renaming for MSTT

record RenData (μ : Modality n m) (T : Ty n) (Γ : Ctx m) : Set where
  constructor rendata
  field
    new-name : Name
    new-var : Var new-name μ T 𝟙 Γ

newRenData : {μ : Modality n m} {T : Ty n} {Γ : Ctx m} → RenData μ T (Γ ,, μ ∣ x ∈ T)
newRenData = rendata _ vzero


module AtomicRenDef = AtomicRenSubDef RenData renaming (AtomicRenSub to AtomicRen)

module AtomicRenVar where
  open AtomicRenDef

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
    let ltel-splitting κ/Λ₂ v' lock-div = split-ltel-var Λ₂ v
    in renvar x (κ/Λ₂ ⓜ locks-ltel Λ₁) (transp-cellˡ lock-div (id-cell {μ = κ/Λ₂} ⓣ-hor α)) (skip-locks Λ₁ v')
  atomic-ren-var' vzero (σ ∷ rendata y w / x) = renvar y _ id-cell w
  atomic-ren-var' (vsuc v) (σ ∷ rendata y w / x) = atomic-ren-var' v σ
  atomic-ren-var' v (σ ⊚π) = let renvar y κ' α w = atomic-ren-var' v σ in renvar y κ' α (vsuc w)
  atomic-ren-var' (skip-lock .μ v) (σ ,lock⟨ μ ⟩) =
    let renvar y κ' α w = atomic-ren-var' v σ
    in renvar y (κ' ⓜ μ) (α ⓣ-hor id-cell) (skip-lock μ w)

  atomic-ren-var : Var x μ T κ Δ → TwoCell μ κ → AtomicRen Γ Δ → Tm Γ T
  atomic-ren-var v α σ = let renvar y κ' β w = atomic-ren-var' v σ in var' y {w} (β ⓣ-vert α)

  ren-data-struct : RenSubDataStructure RenData
  RenSubDataStructure.newV ren-data-struct = newRenData
  RenSubDataStructure.atomic-rensub-lookup-var ren-data-struct = atomic-ren-var

module AtomicRen = AtomicRenSub RenData AtomicRenVar.ren-data-struct
  renaming
    ( AtomicRenSub to AtomicRen
    ; [] to []ar
    ; _∷_/_ to _∷ᵃʳ_/_
    ; _⊚π to _⊚ᵃʳπ
    ; _,lock⟨_⟩ to _,arlock⟨_⟩
    ; atomic-key to atomic-key-ren
    ; id-atomic-rensub to id-atomic-ren
    ; atomic-rensub-tm to atomic-rename-tm
    ; lift-atomic-rensub to lift-atomic-ren)

module RenM = RenSub RenData AtomicRenVar.ren-data-struct

open RenM
  renaming
    ( RenSub to Ren
    ; id to id-ren
    ; rensub-tm to rename-tm
    ; lift-rensub to lift-ren
    ; []rs to []r
    ; π-rensub to π-ren
    ; _,rslock⟨_⟩ to _,rlock⟨_⟩
    ; key-rensub to key-ren
    ; _⊚rs_ to _⊚r_
    ; rensub-tm-⊚ to ren-tm-⊚)
  using (_⊚a_)
  public

_∷ʳ_,_/_ : Ren Γ Δ → (y : Name) → Var y μ T 𝟙 Γ → (x : Name) → Ren Γ (Δ ,, μ ∣ x ∈ T)
σ ∷ʳ y , v / x = σ RenM.∷ʳˢ rendata y v / x

-- Some special renamings for introducing/removing a trivial lock and
-- for (un)fusing locks.
lock𝟙-ren : Ren (Γ ,lock⟨ 𝟙 ⟩) Γ
lock𝟙-ren = key-ren (◇ ,lock⟨ 𝟙 ⟩) ◇ id-cell

unlock𝟙-ren : Ren Γ (Γ ,lock⟨ 𝟙 ⟩)
unlock𝟙-ren = key-ren ◇ (◇ ,lock⟨ 𝟙 ⟩) id-cell

fuselocks-ren : Ren (Γ ,lock⟨ μ ⓜ ρ ⟩) (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩)
fuselocks-ren {μ = μ} {ρ = ρ} = key-ren (◇ ,lock⟨ μ ⓜ ρ ⟩) (◇ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) id-cell

unfuselocks-ren : Ren (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) (Γ ,lock⟨ μ ⓜ ρ ⟩)
unfuselocks-ren {μ = μ} {ρ = ρ} = key-ren (◇ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) (◇ ,lock⟨ μ ⓜ ρ ⟩) id-cell

-- Specific opertations for weakening a term and for the functorial
-- behaviour of locks.
weaken-tm : Tm Γ T → Tm (Γ ,, μ ∣ x ∈ S) T
weaken-tm t = rename-tm t π-ren

lock𝟙-tm : Tm Γ T → Tm (Γ ,lock⟨ 𝟙 ⟩) T
lock𝟙-tm t = rename-tm t (lock𝟙-ren)

unlock𝟙-tm : Tm (Γ ,lock⟨ 𝟙 ⟩) T → Tm Γ T
unlock𝟙-tm t = rename-tm t (unlock𝟙-ren)

fuselocks-tm : Tm (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) T → Tm (Γ ,lock⟨ μ ⓜ ρ ⟩) T
fuselocks-tm t = rename-tm t fuselocks-ren

unfuselocks-tm : Tm (Γ ,lock⟨ μ ⓜ ρ ⟩) T → Tm (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) T
unfuselocks-tm t = rename-tm t unfuselocks-ren


-- Some simpler term formers than the ones in the original syntax. The
-- implementation depends on the functoriality of locks proved above.
mod-elim' : (μ : Modality n m) (x : Name) (t : Tm Γ ⟨ μ ∣ T ⟩) (s : Tm (Γ ,, μ ∣ x ∈ T) S) → Tm Γ S
mod-elim' {Γ = Γ} {T = T} {S = S} μ x t s =
  mod-elim 𝟙 μ x (lock𝟙-tm t) s

syntax mod-elim' μ x t s = let' mod⟨ μ ⟩ x ← t in' s

lam[_∈_]_ : (x : Name) (T : Ty m) → Tm (Γ ,, x ∈ T) S → Tm Γ (T ⇛ S)
lam[ x ∈ T ] b = lam[ 𝟙 ∣ x ∈ T ] b

infixl 50 _∙¹_
_∙¹_ : Tm Γ (T ⇛ S) → Tm Γ T → Tm Γ S
f ∙¹ t = f ∙ lock𝟙-tm t


--------------------------------------------------
-- MSTT substitutions

SubData : Modality n m → Ty n → Ctx m → Set
SubData μ T Γ = Tm (Γ ,lock⟨ μ ⟩) T

newSubData : {μ : Modality n m} {T : Ty n} {Γ : Ctx m} → SubData μ T (Γ ,, μ ∣ x ∈ T)
newSubData {x = x} = var' x {skip-lock _ vzero} id-cell


module AtomicSubDef = AtomicRenSubDef SubData renaming (AtomicRenSub to AtomicSub)

module AtomicSubVar where

  open AtomicSubDef

  -- TODO: possible performance optimizations
  --   * Use a "reverse LockTele" (i.e. a cons list instead of a snoc list of modalities) instead of the 1 modality ρ.
  --     This has the advantage that we do not fuse all the locks together in 1 modality, which is not really necessary,
  --     and that we do not lock the context with 𝟙 in the final function atomic-sub-var.
  --   * Instead of immediately applying a renaming, build up 1 renaming in the substitution process and apply it at the end.
  --     In this way, the number of term traversals is reduced.
  atomic-sub-var' : {Γ Δ : Ctx m} {μ : Modality n o} {κ : Modality m o} (v : Var x μ T κ Γ) →
                    (ρ : Modality n m) → TwoCell μ (κ ⓜ ρ) → AtomicSub Δ Γ → Tm (Δ ,lock⟨ ρ ⟩) T
  atomic-sub-var' {x = x} v ρ α (atomic-key Λ₁ Λ₂ β) =
    let ltel-splitting κ/Λ₂ w lock-div = split-ltel-var Λ₂ v
    in var' x {skip-lock ρ (skip-locks Λ₁ w)}
            (((id-cell {μ = κ/Λ₂}) ⓣ-hor β ⓣ-hor (id-cell {μ = ρ})) ⓣ-vert transp-cellʳ (cong (_ⓜ ρ) (sym lock-div)) α)
  atomic-sub-var' vzero    ρ α (σ ∷ t / x) = rename-tm t (key-ren (◇ ,lock⟨ ρ ⟩) (◇ ,lock⟨ _ ⟩) α)
  atomic-sub-var' (vsuc v) ρ α (σ ∷ t / x) = atomic-sub-var' v ρ α σ
  atomic-sub-var' v ρ α (σ ⊚π) = rename-tm (atomic-sub-var' v ρ α σ) (π-ren ,rlock⟨ _ ⟩)
  atomic-sub-var' (skip-lock {κ = κ} .μ v) ρ α (σ ,lock⟨ μ ⟩) = unfuselocks-tm (atomic-sub-var' v (μ ⓜ ρ) (transp-cellʳ (mod-assoc κ) α) σ)

  atomic-sub-var : Var x μ T κ Δ → TwoCell μ κ → AtomicSub Γ Δ → Tm Γ T
  atomic-sub-var v α σ = unlock𝟙-tm (atomic-sub-var' v 𝟙 (transp-cellʳ (sym mod-unitʳ) α) σ)

  sub-data-struct : RenSubDataStructure SubData
  RenSubDataStructure.newV sub-data-struct = newSubData
  RenSubDataStructure.atomic-rensub-lookup-var sub-data-struct = atomic-sub-var


module AtomicSub = AtomicRenSub SubData AtomicSubVar.sub-data-struct
  renaming
    ( AtomicRenSub to AtomicSub
    ; [] to []as
    ; _∷_/_ to _∷ᵃˢ_/_
    ; _⊚π to _⊚ᵃˢπ
    ; _,lock⟨_⟩ to _,aslock⟨_⟩
    ; atomic-key to atomic-key-sub
    ; id-atomic-rensub to id-atomic-sub
    ; atomic-rensub-tm to atomic-sub-tm
    ; lift-atomic-rensub to lift-atomic-sub)

module SubM = RenSub SubData AtomicSubVar.sub-data-struct

open SubM
  renaming
    ( RenSub to Sub
    ; id to id-sub
    ; rensub-tm to _[_]tm
    ; lift-rensub to lift-sub
    ; []rs to []s
    ; _∷ʳˢ_/_ to _∷ˢ_/_
    ; π-rensub to π
    ; _,rslock⟨_⟩ to _,slock⟨_⟩
    ; key-rensub to key-sub
    ; _⊚rs_ to _⊚s_
    ; rensub-tm-⊚ to sub-tm-⊚)
  using (_⊚a_)
  public

_/_ : Tm (Γ ,lock⟨ μ ⟩) T → (x : Name) → Sub Γ (Γ ,, μ ∣ x ∈ T)
t / x = id-sub ∷ˢ t / x

{-
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
