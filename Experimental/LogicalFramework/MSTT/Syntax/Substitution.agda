--------------------------------------------------
-- Definition and implementation of renaming and substitution for MSTT
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension using (TmExt)

module Experimental.LogicalFramework.MSTT.Syntax.Substitution
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯)
  where

open import Data.List
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open ModeTheory ℳ
open TmExt 𝓉

open Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯 hiding (TmExt)
open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Syntax.Terms ℳ 𝒯 𝓉 hiding (refl)

private variable
  m n o p : Mode
  μ ρ κ φ : Modality m n
  T S : Ty m
  x y : Name
  Γ Δ Θ : Ctx m
  Λ : LockTele m n


--------------------------------------------------
-- Traversals of MSTT terms

-- An element of type Trav Γ Δ can be used to tranform terms in Δ to
-- terms in Γ. For this to work, we must specify how such a traversal
-- acts on variables and provide a lifting and lock operation for such
-- traversals.
record TravStruct (Trav : ∀ {m} → Ctx m → Ctx m → Set) : Set where
  no-eta-equality
  field
    vr : {Γ Δ : Ctx m} {T : Ty m} →
         Var x T Δ ◇ → Trav Γ Δ → Tm Γ T
    lift : Trav Γ Δ → Trav (Γ ,, μ ∣ x ∈ T) (Δ ,, μ ∣ x ∈ T)
    lock : Trav Γ Δ → Trav (Γ ,lock⟨ μ ⟩) (Δ ,lock⟨ μ ⟩)

  lift-trav-tel : Trav Γ Δ → (Θ : Telescope m n) → Trav (Γ ++tel Θ) (Δ ++tel Θ)
  lift-trav-tel σ ◇ = σ
  lift-trav-tel σ (Θ ,, μ ∣ x ∈ T) = lift (lift-trav-tel σ Θ)
  lift-trav-tel σ (Θ ,lock⟨ μ ⟩) = lock (lift-trav-tel σ Θ)

  traverse-tm : Tm Δ T → Trav Γ Δ → Tm Γ T
  traverse-ext-tmargs : {arginfos : List (TmArgInfo m)} → ExtTmArgs arginfos Δ → Trav Γ Δ → ExtTmArgs arginfos Γ
  
  traverse-tm (var' x {v}) σ = vr v σ
  traverse-tm (mod⟨ μ ⟩ t) σ = mod⟨ μ ⟩ traverse-tm t (lock σ)
  traverse-tm (mod-elim ρ μ x t s) σ = mod-elim ρ μ x (traverse-tm t (lock σ)) (traverse-tm s (lift σ))
  traverse-tm (lam[ μ ∣ x ∈ T ] s) σ = lam[ μ ∣ x ∈ T ] traverse-tm s (lift σ)
  traverse-tm (f ∙ t) σ = traverse-tm f σ ∙ traverse-tm t (lock σ)
  traverse-tm zero σ = zero
  traverse-tm (suc t) σ = suc (traverse-tm t σ)
  traverse-tm (nat-rec z s n) σ = nat-rec (traverse-tm z σ) (traverse-tm s σ) (traverse-tm n σ)
  traverse-tm true σ = true
  traverse-tm false σ = false
  traverse-tm (if b t f) σ = if (traverse-tm b σ) (traverse-tm t σ) (traverse-tm f σ)
  traverse-tm (pair t s) σ = pair (traverse-tm t σ) (traverse-tm s σ)
  traverse-tm (fst p) σ = fst (traverse-tm p σ)
  traverse-tm (snd p) σ = snd (traverse-tm p σ)
  traverse-tm (ext c args ty-eq) σ = ext c (traverse-ext-tmargs args σ) ty-eq

  traverse-ext-tmargs {arginfos = []}                 _            σ = tt
  traverse-ext-tmargs {arginfos = arginfo ∷ arginfos} (arg , args) σ =
    (traverse-tm arg (lift-trav-tel σ (tmarg-tel arginfo))) , (traverse-ext-tmargs args σ)

open TravStruct using (traverse-tm)


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
    []ᵃ : AtomicRenSub Γ ◇
    idᵃ : AtomicRenSub Γ Γ
      -- ^ The identity atomic rensub could be implemented in multiple
      --    ways using the other constructors, but those are generally
      --    more expensive to apply to a term, and we don't have a
      --    unique representation of atomic rensubs anyway.
    _⊚πᵃ : AtomicRenSub Γ Δ → AtomicRenSub (Γ ,, μ ∣ x ∈ T) Δ
    _,lockᵃ⟨_⟩ : AtomicRenSub Γ Δ → (μ : Modality n m) → AtomicRenSub (Γ ,lock⟨ μ ⟩) (Δ ,lock⟨ μ ⟩)
    keyᵃ : (Λ₁ Λ₂ : LockTele n m) → TwoCell (locksˡᵗ Λ₂) (locksˡᵗ Λ₁) → AtomicRenSub (Γ ,ˡᵗ Λ₁) (Γ ,ˡᵗ Λ₂)
    _∷ᵃ_/_ : AtomicRenSub Γ Δ → V μ T Γ → (x : Name) → AtomicRenSub Γ (Δ ,, μ ∣ x ∈ T)

-- In order to obtain useful results for renamings/substitutions, the
-- type family representing the data assigned to variables must be
-- equipped with some extra structure.
record RenSubDataStructure (V : RenSubData) : Set where
  field
    newV : ∀ {x m n} {μ : Modality n m} {T : Ty n} {Γ : Ctx m} → V μ T (Γ ,, μ ∣ x ∈ T)
    atomic-rensub-lookup-var : ∀ {x m} {Γ Δ : Ctx m} {T : Ty m} →
                               Var x T Δ ◇ → AtomicRenSubDef.AtomicRenSub V Γ Δ → Tm Γ T

module AtomicRenSub
  (V : RenSubData)
  (rensub-struct : RenSubDataStructure V)
  where

  open AtomicRenSubDef V public
  open RenSubDataStructure rensub-struct

  πᵃ : AtomicRenSub (Γ ,, μ ∣ x ∈ T) Γ
  πᵃ = idᵃ ⊚πᵃ

  liftᵃ : AtomicRenSub Γ Δ → AtomicRenSub (Γ ,, μ ∣ x ∈ T) (Δ ,, μ ∣ x ∈ T)
  liftᵃ {x = x} σ = (σ ⊚πᵃ) ∷ᵃ newV / x

  _,locksᵃ⟨_⟩ : AtomicRenSub Γ Δ → (Λ : LockTele m n) → AtomicRenSub (Γ ,ˡᵗ Λ) (Δ ,ˡᵗ Λ)
  σ ,locksᵃ⟨ ◇ ⟩            = σ
  σ ,locksᵃ⟨ lock⟨ μ ⟩, Λ ⟩ = (σ ,lockᵃ⟨ μ ⟩) ,locksᵃ⟨ Λ ⟩

  AtomicRenSubTrav : TravStruct AtomicRenSub
  TravStruct.vr AtomicRenSubTrav = atomic-rensub-lookup-var
  TravStruct.lift AtomicRenSubTrav = liftᵃ
  TravStruct.lock AtomicRenSubTrav {μ = μ} σ = σ ,lockᵃ⟨ μ ⟩

  _[_]tmᵃ : Tm Δ T → AtomicRenSub Γ Δ → Tm Γ T
  _[_]tmᵃ = traverse-tm AtomicRenSubTrav


module RenSubDef (V : RenSubData) where
  open AtomicRenSubDef V

  -- An actual renaming/substitution is a well-typed (snoc) list of atomic renamings/substitutions.
  data RenSub : Ctx m → Ctx m → Set where
    id : RenSub Γ Γ
    _⊚a_ : RenSub Δ Θ → AtomicRenSub Γ Δ → RenSub Γ Θ


module RenSub
  (V : RenSubData)
  (rensub-struct : RenSubDataStructure V)
  where

  open AtomicRenSub V rensub-struct
  open RenSubDef V public

  _[_]tmʳˢ : Tm Δ T → RenSub Γ Δ → Tm Γ T
  t [ id ]tmʳˢ = t
  t [ τ ⊚a σᵃ ]tmʳˢ = (t [ τ ]tmʳˢ) [ σᵃ ]tmᵃ

  liftʳˢ : RenSub Γ Δ → RenSub (Γ ,, μ ∣ x ∈ T) (Δ ,, μ ∣ x ∈ T)
  liftʳˢ id = id
  liftʳˢ (σ ⊚a τᵃ) = liftʳˢ σ ⊚a liftᵃ τᵃ

  -- All MTT constructors for producing renamings/substitutions, can
  -- be implemented as operations producing something of type RenSub.
  []ʳˢ : RenSub Γ ◇
  []ʳˢ = id ⊚a []ᵃ

  πʳˢ : RenSub (Γ ,, μ ∣ x ∈ T) Γ
  πʳˢ = id ⊚a πᵃ

  -- Case splitting on the first argument is not strictly necessary
  -- here, but it avoids 1 additional term traversal in the second case.
  _∷ʳˢ_/_ : RenSub Γ Δ → V μ T Γ → (x : Name) → RenSub Γ (Δ ,, μ ∣ x ∈ T)
  id        ∷ʳˢ v / x = id ⊚a (idᵃ ∷ᵃ v / x)
  (σ ⊚a τᵃ) ∷ʳˢ v / x = liftʳˢ σ ⊚a (τᵃ ∷ᵃ v / x)

  _,lockʳˢ⟨_⟩ : RenSub Γ Δ → (μ : Modality m n) → RenSub (Γ ,lock⟨ μ ⟩) (Δ ,lock⟨ μ ⟩)
  id        ,lockʳˢ⟨ μ ⟩ = id
  (σ ⊚a τᵃ) ,lockʳˢ⟨ μ ⟩ = (σ ,lockʳˢ⟨ μ ⟩) ⊚a (τᵃ ,lockᵃ⟨ μ ⟩)

  _,locksʳˢ⟨_⟩ : RenSub Γ Δ → (Λ : LockTele m n) → RenSub (Γ ,ˡᵗ Λ) (Δ ,ˡᵗ Λ)
  σ ,locksʳˢ⟨ ◇ ⟩           = σ
  σ ,locksʳˢ⟨ lock⟨ μ ⟩, Λ ⟩ = (σ ,lockʳˢ⟨ μ ⟩) ,locksʳˢ⟨ Λ ⟩

  keyʳˢ : (Λ₁ Λ₂ : LockTele n m) → TwoCell (locksˡᵗ Λ₂) (locksˡᵗ Λ₁) → RenSub (Γ ,ˡᵗ Λ₁) (Γ ,ˡᵗ Λ₂)
  keyʳˢ Λ₁ Λ₂ α = id ⊚a keyᵃ Λ₁ Λ₂ α

  _⊚ʳˢ_ : RenSub Δ Θ → RenSub Γ Δ → RenSub Γ Θ
  τ ⊚ʳˢ id = τ
  τ ⊚ʳˢ (σ ⊚a σᵃ) = (τ ⊚ʳˢ σ) ⊚a σᵃ

  rensub-tm-⊚ : {τ : RenSub Δ Θ} (σ : RenSub Γ Δ) {t : Tm Θ T} → t [ τ ]tmʳˢ [ σ ]tmʳˢ ≡ t [ τ ⊚ʳˢ σ ]tmʳˢ
  rensub-tm-⊚ id = refl
  rensub-tm-⊚ (σ ⊚a σᵃ) = cong (_[ σᵃ ]tmᵃ) (rensub-tm-⊚ σ)


--------------------------------------------------
-- Prerequisite: applying a 2-cell to a variable

apply-2-cell-var : (Θ Ψ : LockTele n m) (α : TwoCell (locksˡᵗ Θ) (locksˡᵗ Ψ)) →
                   Var x T Γ Θ → Var x T Γ Ψ
apply-2-cell-var Θ Ψ α (vzero β) = vzero (α ⓣ-vert β)
apply-2-cell-var Θ Ψ α (vsuc v)  = vsuc (apply-2-cell-var Θ Ψ α v)
apply-2-cell-var Θ Ψ α (vlock v) = vlock (apply-2-cell-var _ _ (id-cell ⓣ-hor α) v)

apply-2-cell-var-lt : (Θ Ψ : LockTele n m) (α : TwoCell (locksˡᵗ Θ) (locksˡᵗ Ψ)) {Λ : LockTele m o} →
                      Var x T (Γ ,ˡᵗ Θ) Λ → Var x T (Γ ,ˡᵗ Ψ) Λ
apply-2-cell-var-lt Θ Ψ α {Λ} v =
  vlocks Ψ (apply-2-cell-var (Θ ++ˡᵗ Λ) (Ψ ++ˡᵗ Λ) (whiskerˡᵗ-right Θ Ψ α) (unvlocks Θ v))


--------------------------------------------------
-- Renaming for MSTT

-- A value of type SomeVar T Γ Λ represents a variable in Γ ,ˡᵗ Λ with
-- an unkown name.
record SomeVar (T : Ty n) (Γ : Ctx m) (Λ : LockTele m n) : Set where
  constructor somevar
  field
    {ren-name} : Name
    get-var : Var ren-name T Γ Λ
open SomeVar using (get-var)

RenData : RenSubData
RenData μ T Γ = SomeVar T Γ (lock⟨ μ ⟩, ◇)

newRenData : {μ : Modality n m} {T : Ty n} {Γ : Ctx m} → RenData μ T (Γ ,, μ ∣ x ∈ T)
newRenData = somevar vzero-id

module AtomicRenDef = AtomicRenSubDef RenData renaming (AtomicRenSub to AtomicRen)

module AtomicRenVar where
  open AtomicRenDef

  atomic-ren-var' : {Γ Δ : Ctx n} (Λ : LockTele n m) →
                    Var x T Δ Λ → AtomicRen Γ Δ → SomeVar T Γ Λ
  atomic-ren-var' Λ v         idᵃ                  = somevar v
  atomic-ren-var' Λ v         (σ ⊚πᵃ)              = somevar (vsuc (get-var (atomic-ren-var' Λ v σ)))
  atomic-ren-var' Λ (vlock v) (σ ,lockᵃ⟨ μ ⟩)      = somevar (vlock (get-var (atomic-ren-var' (lock⟨ μ ⟩, Λ) v σ)))
  atomic-ren-var' Λ v         (keyᵃ Θ Ψ α)         = somevar (apply-2-cell-var-lt Ψ Θ α v)
  atomic-ren-var' Λ (vzero α) (σ ∷ᵃ somevar w / x) = somevar (apply-2-cell-var (lock⟨ _ ⟩, ◇) Λ α w)
  atomic-ren-var' Λ (vsuc v)  (σ ∷ᵃ _ / y)         = atomic-ren-var' Λ v σ

  atomic-ren-var : Var x T Δ ◇ → AtomicRen Γ Δ → Tm Γ T
  atomic-ren-var v σ = var' _ {get-var (atomic-ren-var' ◇ v σ)}

  ren-data-struct : RenSubDataStructure RenData
  RenSubDataStructure.newV ren-data-struct = newRenData
  RenSubDataStructure.atomic-rensub-lookup-var ren-data-struct = atomic-ren-var

module AtomicRenM = AtomicRenSub RenData AtomicRenVar.ren-data-struct

open AtomicRenM public
  renaming
    ( AtomicRenSub to AtomicRen
    ; []ᵃ to []ᵃʳ
    ; _∷ᵃ_/_ to _∷ᵃʳ_/_
    ; _⊚πᵃ to _⊚πᵃʳ
    ; _,lockᵃ⟨_⟩ to _,lockᵃʳ⟨_⟩
    ; keyᵃ to keyᵃʳ
    ; idᵃ to idᵃʳ
    ; πᵃ to πᵃʳ
    ; _[_]tmᵃ to infixl 8 _[_]tmᵃʳ
    ; liftᵃ to liftᵃʳ
    ; _,locksᵃ⟨_⟩ to _,locksᵃʳ⟨_⟩)
  using ()

module RenM = RenSub RenData AtomicRenVar.ren-data-struct

open RenM
  renaming
    ( RenSub to Ren
    ; id to idʳ
    ; _[_]tmʳˢ to infixl 8 _[_]tmʳ
    ; liftʳˢ to liftʳ
    ; []ʳˢ to []ʳ
    ; πʳˢ to πʳ
    ; _,lockʳˢ⟨_⟩ to _,lockʳ⟨_⟩
    ; _,locksʳˢ⟨_⟩ to _,locksʳ⟨_⟩
    ; keyʳˢ to keyʳ
    ; _⊚ʳˢ_ to _⊚ʳ_
    ; rensub-tm-⊚ to ren-tm-⊚)
  using ()
  public

_∷ʳ_,_/_ : Ren Γ Δ → (y : Name) → Var y T (Γ ,lock⟨ μ ⟩) ◇ → (x : Name) → Ren Γ (Δ ,, μ ∣ x ∈ T)
σ ∷ʳ y , v / x = σ RenM.∷ʳˢ somevar (unvlock v) / x

-- Some special renamings for introducing/removing a trivial lock and
-- for (un)fusing locks.
lock𝟙-ren : Ren (Γ ,lock⟨ 𝟙 ⟩) Γ
lock𝟙-ren = keyʳ (lock⟨ 𝟙 ⟩, ◇) ◇ id-cell

unlock𝟙-ren : Ren Γ (Γ ,lock⟨ 𝟙 ⟩)
unlock𝟙-ren = keyʳ ◇ (lock⟨ 𝟙 ⟩, ◇) id-cell

fuselocks-ren : Ren (Γ ,lock⟨ μ ⓜ ρ ⟩) (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩)
fuselocks-ren {μ = μ} {ρ = ρ} = keyʳ (lock⟨ μ ⓜ ρ ⟩, ◇) (lock⟨ μ ⟩, lock⟨ ρ ⟩, ◇) id-cell

unfuselocks-ren : Ren (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) (Γ ,lock⟨ μ ⓜ ρ ⟩)
unfuselocks-ren {μ = μ} {ρ = ρ} = keyʳ (lock⟨ μ ⟩, lock⟨ ρ ⟩, ◇) (lock⟨ μ ⓜ ρ ⟩, ◇) id-cell

-- Specific opertations for weakening a term and for the functorial
-- behaviour of locks.
weaken-tm : Tm Γ T → Tm (Γ ,, μ ∣ x ∈ S) T
weaken-tm t = t [ πʳ ]tmʳ

lock𝟙-tm : Tm Γ T → Tm (Γ ,lock⟨ 𝟙 ⟩) T
lock𝟙-tm t = t [ lock𝟙-ren ]tmʳ

unlock𝟙-tm : Tm (Γ ,lock⟨ 𝟙 ⟩) T → Tm Γ T
unlock𝟙-tm t = t [ unlock𝟙-ren ]tmʳ

fuselocks-tm : Tm (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) T → Tm (Γ ,lock⟨ μ ⓜ ρ ⟩) T
fuselocks-tm t = t [ fuselocks-ren ]tmʳ

unfuselocks-tm : Tm (Γ ,lock⟨ μ ⓜ ρ ⟩) T → Tm (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) T
unfuselocks-tm t = t [ unfuselocks-ren ]tmʳ


-- Some simpler term formers than the ones in the original syntax. The
-- implementation depends on the functoriality of locks proved above.
mod-elim' : (μ : Modality n m) (x : Name) (t : Tm Γ ⟨ μ ∣ T ⟩) (s : Tm (Γ ,, μ ∣ x ∈ T) S) → Tm Γ S
mod-elim' {Γ = Γ} {T = T} {S = S} μ x t s =
  mod-elim 𝟙 μ x (lock𝟙-tm t) (subst (λ - → Tm (Γ ,, - ∣ x ∈ T) S) (sym mod-unitˡ) s)

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
newSubData {x = x} = v0


module AtomicSubDef = AtomicRenSubDef SubData renaming (AtomicRenSub to AtomicSub)

module AtomicSubVar where

  open AtomicSubDef

  -- TODO: possible performance optimization
  --   * Instead of immediately applying a renaming, build up 1 renaming in the substitution process and apply it at the end.
  --     In this way, the number of term traversals is reduced.
  atomic-sub-var' : {Γ Δ : Ctx n} (Λ : LockTele n m) (σ : AtomicSub Γ Δ) →
                    Var x T Δ Λ → Tm (Γ ,ˡᵗ Λ) T
  atomic-sub-var' Λ idᵃ             v         = var-lt Λ v
  atomic-sub-var' Λ (σ ⊚πᵃ)         v         = (atomic-sub-var' Λ σ v) [ πᵃʳ ,locksᵃʳ⟨ Λ ⟩ ]tmᵃʳ
  atomic-sub-var' Λ (σ ,lockᵃ⟨ μ ⟩) (vlock v) = atomic-sub-var' (lock⟨ μ ⟩, Λ) σ v
  atomic-sub-var' Λ (keyᵃ Θ Ψ α)    v         = var-lt Λ (apply-2-cell-var-lt Ψ Θ α v)
  atomic-sub-var' Λ (σ ∷ᵃ t / x)    (vzero α) = t [ keyᵃʳ Λ (lock⟨ _ ⟩, ◇) α ]tmᵃʳ
  atomic-sub-var' Λ (σ ∷ᵃ t / y)    (vsuc v)  = atomic-sub-var' Λ σ v

  atomic-sub-var : Var x T Δ ◇ → AtomicSub Γ Δ → Tm Γ T
  atomic-sub-var v σ = atomic-sub-var' ◇ σ v

  sub-data-struct : RenSubDataStructure SubData
  RenSubDataStructure.newV sub-data-struct = newSubData
  RenSubDataStructure.atomic-rensub-lookup-var sub-data-struct = atomic-sub-var


module AtomicSubM = AtomicRenSub SubData AtomicSubVar.sub-data-struct

open AtomicSubM
  renaming
    ( AtomicRenSub to AtomicSub
    ; []ᵃ to []ᵃˢ
    ; _∷ᵃ_/_ to _∷ᵃˢ_/_
    ; _⊚πᵃ to _⊚πᵃˢ
    ; _,lockᵃ⟨_⟩ to _,lockᵃˢ⟨_⟩
    ; keyᵃ to keyᵃˢ
    ; idᵃ to idᵃˢ
    ; πᵃ to πᵃˢ
    ; _[_]tmᵃ to _[_]tmᵃˢ
    ; liftᵃ to liftᵃˢ
    ; _,locksᵃ⟨_⟩ to _,locksᵃˢ⟨_⟩)
  using ()
  public

module SubM = RenSub SubData AtomicSubVar.sub-data-struct

open SubM
  renaming
    ( RenSub to Sub
    ; id to idˢ
    ; _[_]tmʳˢ to _[_]tmˢ
    ; liftʳˢ to liftˢ
    ; []ʳˢ to []ˢ
    ; _∷ʳˢ_/_ to _∷ˢ_/_
    ; πʳˢ to πˢ
    ; _,lockʳˢ⟨_⟩ to _,lockˢ⟨_⟩
    ; _,locksʳˢ⟨_⟩ to _,locksˢ⟨_⟩
    ; keyʳˢ to keyˢ
    ; _⊚ʳˢ_ to _⊚ˢ_
    ; rensub-tm-⊚ to sub-tm-⊚)
  using ()
  public

infix 19 _/_ _//_

_/_ : Tm (Γ ,lock⟨ μ ⟩) T → (x : Name) → Sub Γ (Γ ,, μ ∣ x ∈ T)
t / x = idˢ ∷ˢ t / x

_//_ : Tm (Γ ,, μ ∣ x ∈ T ,lock⟨ ρ ⟩) S → (y : Name) → Sub (Γ ,, μ ∣ x ∈ T) (Γ ,, ρ ∣ y ∈ S)
s // y = πˢ ∷ˢ s / y
