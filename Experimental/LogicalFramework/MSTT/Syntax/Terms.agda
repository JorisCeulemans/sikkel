--------------------------------------------------
-- Definition of MSTT terms
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension using (TmExt)

module Experimental.LogicalFramework.MSTT.Syntax.Terms
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯)
  where

open import Data.Empty
open import Data.List
open import Data.Maybe as Maybe hiding (Is-just; to-witness)
open import Data.Product
import Data.String as Name
open import Data.Unit
open import Relation.Nullary
import Relation.Binary.PropositionalEquality as PropEq
open PropEq hiding (refl)
open PropEq using (refl) public
-- ^ refl is re-exported so that it becomes available for instance
--   search when using the functions var and svar defined in this
--   module.

open ModeTheory ℳ
open TmExt 𝓉

open Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯 hiding (TmExt)
open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯

private variable
  m n o p : Mode
  μ ρ κ φ : Modality m n
  T S : Ty m
  x y : Name
  Γ Δ Θ : Ctx m
  Λ : LockTele m n


--------------------------------------------------
-- Definition of MSTT variables

-- A value of type Var x T Γ Λ expresses that there is a valid
-- variable (including the necessary 2-cell) with name x and type T in
-- the context Γ ,ˡᵗ Λ. We explicitly keep track of the lock telescope
-- Λ in order to match the recursion structure of many of the
-- variable-manipulating functions further in this file. Note that Λ
-- is required to be empty when constructing a term.
data Var (x : Name) (T : Ty n) : Ctx m → LockTele m n → Set where
  vzero : {μ : Modality n m} {Γ : Ctx m} {Λ : LockTele m n} →
          TwoCell μ (locksˡᵗ Λ) →
          Var x T (Γ ,, μ ∣ x ∈ T) Λ
  vsuc : {Γ : Ctx m} {Λ : LockTele m n} {ρ : Modality o m} {y : Name} {S : Ty o} →
         Var x T Γ Λ →
         Var x T (Γ ,, ρ ∣ y ∈ S) Λ
  vlock : {Γ : Ctx o} {ρ : Modality m o} {Λ : LockTele m n} →
          Var x T Γ (lock⟨ ρ ⟩, Λ) →
          Var x T (Γ ,lock⟨ ρ ⟩) Λ

vlocks : {x : Name} {T : Ty n} {Γ : Ctx o} (Θ : LockTele o m) {Λ : LockTele m n} →
         Var x T Γ (Θ ++ˡᵗ Λ) →
         Var x T (Γ ,ˡᵗ Θ) Λ
vlocks ◇             v = v
vlocks (lock⟨ μ ⟩, Θ) v = vlocks Θ (vlock v)

unvlock : {x : Name} {T : Ty n} {Γ : Ctx o} {μ : Modality m o} {Λ : LockTele m n} →
          Var x T (Γ ,lock⟨ μ ⟩) Λ →
          Var x T Γ (lock⟨ μ ⟩, Λ)
unvlock (vlock v) = v

unvlocks : {x : Name} {T : Ty n} {Γ : Ctx o} (Θ : LockTele o m) {Λ : LockTele m n} →
           Var x T (Γ ,ˡᵗ Θ) Λ →
           Var x T Γ (Θ ++ˡᵗ Λ)
unvlocks ◇             v = v
unvlocks (lock⟨ μ ⟩, Θ) v = unvlock (unvlocks Θ v)


--------------------------------------------------
-- Definition of MSTT terms

TmArgBoundNames : List (TmArgInfo m) → Set
TmArgBoundNames []                   = ⊤
TmArgBoundNames (arginfo ∷ arginfos) = Names (tmarg-tel arginfo) × TmArgBoundNames arginfos

infixl 50 _∙_
data Tm : Ctx m → Ty m → Set
ExtTmArgs : {m : Mode} (arginfos : List (TmArgInfo m)) → TmArgBoundNames arginfos → Ctx m → Set

data Tm where
  var' : (x : Name) {v : Var x T Γ ◇} → Tm Γ T
    -- ^ When writing programs, one should not directly use var' but rather combine
    --   it with a decision procedure for Var, which will resolve the name. See below.
  mod⟨_⟩_ : (μ : Modality n m) → Tm (Γ ,lock⟨ μ ⟩) T → Tm Γ ⟨ μ ∣ T ⟩
  mod-elim : (ρ : Modality o m) (μ : Modality n o) (x : Name)
             (t : Tm (Γ ,lock⟨ ρ ⟩) ⟨ μ ∣ T ⟩) (s : Tm (Γ ,, ρ ⓜ μ ∣ x ∈ T) S) →
             Tm Γ S
  lam[_∣_∈_]_ : (μ : Modality n m) (x : Name) (T : Ty n) → Tm (Γ ,, μ ∣ x ∈ T) S → Tm Γ (⟨ μ ∣ T ⟩⇛ S)
  _∙_ : {μ : Modality n m} → Tm Γ (⟨ μ ∣ T ⟩⇛ S) → Tm (Γ ,lock⟨ μ ⟩) T → Tm Γ S
  zero : Tm Γ Nat'
  suc : Tm Γ Nat' → Tm Γ Nat'
  nat-rec : {A : Ty m} → Tm Γ A → Tm Γ (A ⇛ A) → Tm Γ Nat' → Tm Γ A
  true false : Tm Γ Bool'
  if : {A : Ty m} → Tm Γ Bool' → (t f : Tm Γ A) → Tm Γ A
  pair : Tm Γ T → Tm Γ S → Tm Γ (T ⊠ S)
  fst : Tm Γ (T ⊠ S) → Tm Γ T
  snd : Tm Γ (T ⊠ S) → Tm Γ S
  ext : (c : TmExtCode m) (names : TmArgBoundNames (tm-code-arginfos c)) →
        ExtTmArgs (tm-code-arginfos c) names Γ →
        T ≡ tm-code-ty c →
        Tm Γ T
    -- ^ This constructor is not intended for direct use. An instantiation of MSTT with
    --   specific term extensions should rather provide more convenient term formers via pattern synonyms.

ExtTmArgs []                   _                        Γ = ⊤
ExtTmArgs (arginfo ∷ arginfos) (arg-names , args-names) Γ =
  Tm (Γ ++tel add-names (tmarg-tel arginfo) arg-names) (tmarg-ty arginfo) × ExtTmArgs arginfos args-names Γ


vzero-id : Var x T (Γ ,, μ ∣ x ∈ T) (lock⟨ μ ⟩, ◇)
vzero-id = vzero id-cell

v0 : Tm (Γ ,, μ ∣ x ∈ T ,lock⟨ μ ⟩) T
v0 = var' _ {vlock vzero-id}

v1 : Tm (Γ ,, μ ∣ x ∈ T ,, κ ∣ y ∈ S ,lock⟨ μ ⟩) T
v1 = var' _ {vlock (vsuc vzero-id)}

v0-nolock : Tm (Γ ,, 𝟙 ∣ x ∈ T) T
v0-nolock = var' _ {vzero id-cell}

v1-nolock : Tm (Γ ,, 𝟙 ∣ x ∈ T ,, μ ∣ y ∈ S) T
v1-nolock = var' _ {vsuc (vzero id-cell)}

syntax mod-elim ρ μ x t s = let⟨ ρ ⟩ mod⟨ μ ⟩ x ← t in' s

var-lt : (Λ : LockTele n m) → Var x T Γ Λ → Tm (Γ ,ˡᵗ Λ) T
var-lt ◇              v = var' _ {v}
var-lt (lock⟨ μ ⟩, Λ) v = var-lt Λ (vlock v)


--------------------------------------------------
-- Constructing a variable term by only mentioning the variable name
--   (i.e. resolving the De Bruijn index automatically).
--   This works via a (semi)decision procedure for RawVar x Γ Λ.


-- Preliminary work: we have to reimplement Is-just and from-witness
-- from Data.Maybe so that the definition does not use a data type and
-- hence satisfies η equality.
Is-just' : ∀ {ℓ} {A : Set ℓ} → Maybe A → Set _
Is-just' (just _) = ⊤
Is-just' nothing  = ⊥

to-witness' : ∀ {ℓ} {A : Set ℓ} {m : Maybe A} → Is-just' m → A
to-witness' {m = just a} _ = a


-- A value of type RawVar x Γ Λ means that there is an entry in
-- context Γ ,ˡᵗ Λ with the name x. It does however not provide the
-- necessary 2-cell, so this does not necessarily give rise to a valid
-- variable (we actually want to provide this *after* the right raw
-- variable has been found). Moreover, in the case of rvzero the
-- domain of μ does not necessarily correspond to the codomain of
-- Λ. This will be tested later, but it has to be done via instance
-- resolution rather than applying a (semi)decision procedure in order
-- to accomodate some form of mode polymorphism (m ≟mode m will be
-- stuck when m contains an Agda variable).
data RawVar (x : Name) : Ctx m → LockTele m n → Set where
  rvzero : {Γ : Ctx m} {μ : Modality o m} {T : Ty o} {Λ : LockTele m n} →
           RawVar x (Γ ,, μ ∣ x ∈ T) Λ
  rvsuc : {Γ : Ctx m} {Λ : LockTele m n} {ρ : Modality o m} {y : Name} {S : Ty o} →
          RawVar x Γ Λ →
          RawVar x (Γ ,, ρ ∣ y ∈ S) Λ
  rvlock : {Γ : Ctx o} {ρ : Modality m o} {Λ : LockTele m n} →
           RawVar x Γ (lock⟨ ρ ⟩, Λ) →
           RawVar x (Γ ,lock⟨ ρ ⟩) Λ

rawvar? : (x : Name) (Γ : Ctx m) (Λ : LockTele m n) → Maybe (RawVar x Γ Λ)
rawvar? x ◇                 Λ = nothing
rawvar? x (Γ ,, μ ∣ y ∈ T)  Λ with x Name.≟ y
rawvar? x (Γ ,, μ ∣ .x ∈ T) Λ | yes refl = just rvzero
rawvar? x (Γ ,, μ ∣ y ∈ T)  Λ | no _ = Maybe.map rvsuc (rawvar? x Γ Λ)
rawvar? x (Γ ,lock⟨ μ ⟩)    Λ = Maybe.map rvlock (rawvar? x Γ (lock⟨ μ ⟩, Λ))

rv-dom-mode : RawVar x Γ Λ → Mode
rv-dom-mode (rvzero {o = o}) = o
rv-dom-mode (rvsuc rv)       = rv-dom-mode rv
rv-dom-mode (rvlock rv)      = rv-dom-mode rv

rv-cod-mode : RawVar x Γ Λ → Mode
rv-cod-mode (rvzero {m = m}) = m
rv-cod-mode (rvsuc rv)       = rv-cod-mode rv
rv-cod-mode (rvlock rv)      = rv-cod-mode rv

rv-mod : (rv : RawVar x Γ Λ) → Modality (rv-dom-mode rv) (rv-cod-mode rv)
rv-mod (rvzero {μ = μ}) = μ
rv-mod (rvsuc rv)       = rv-mod rv
rv-mod (rvlock rv)      = rv-mod rv

rv-ty : (rv : RawVar x Γ Λ) → Ty (rv-dom-mode rv)
rv-ty (rvzero {T = T}) = T
rv-ty (rvsuc rv)       = rv-ty rv
rv-ty (rvlock rv)      = rv-ty rv

rv-lt : {Λ : LockTele m n} (rv : RawVar x Γ Λ) → LockTele (rv-cod-mode rv) n
rv-lt (rvzero {Λ = Λ}) = Λ
rv-lt (rvsuc rv)       = rv-lt rv
rv-lt (rvlock rv)      = rv-lt rv

create-var : {Γ : Ctx m} {Λ : LockTele m n}
             (rv : RawVar x Γ Λ)
             (e : n ≡ rv-dom-mode rv) →
             TwoCell (rv-mod rv) (subst (λ - → Modality - (rv-cod-mode rv)) e (locksˡᵗ (rv-lt rv))) →
             Var x (subst Ty (sym e) (rv-ty rv)) Γ Λ
create-var rvzero      refl α = vzero α
create-var (rvsuc rv)  e    α = vsuc (create-var rv e α)
create-var (rvlock rv) e    α = vlock (create-var rv e α)

-- The instance arguments in var and svar are intended to be solved as
-- refl by instance search.
var : (x : Name) {Γ : Ctx m} {i : Is-just' (rawvar? x Γ ◇)} →
      let rv = to-witness' i
      in {{ e : m ≡ rv-dom-mode rv }} →
         TwoCell (rv-mod rv) (subst (λ - → Modality - (rv-cod-mode rv)) e (locksˡᵗ (rv-lt rv))) →
         Tm Γ (subst Ty (sym e) (rv-ty rv))
var x {i = i} {{e}} α = var' _ {create-var (to-witness' i) e α}

svar : (x : Name) {Γ : Ctx m} {i : Is-just' (rawvar? x Γ ◇)} →
       let rv = to-witness' i
       in {{ e : m ≡ rv-dom-mode rv }} →
          {{ rv-mod rv ≡ subst (λ - → Modality - (rv-cod-mode rv)) e (locksˡᵗ (rv-lt rv)) }} →
          Tm Γ (subst Ty (sym e) (rv-ty rv))
svar x {i = i} {{emode}} {{emod}} = var' _ {create-var (to-witness' i) emode (eq-cell emod)}
