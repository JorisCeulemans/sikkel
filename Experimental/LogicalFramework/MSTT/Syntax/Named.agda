--------------------------------------------------
-- Instantiation of the general MSTT syntax with strings as names
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension
open import Data.String as Str

module Experimental.LogicalFramework.MSTT.Syntax.Named
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯 String)
  where

open import Data.Empty
open import Data.Maybe as Maybe hiding (Is-just; to-witness)
open import Data.Product
open import Data.Unit
open import Relation.Nullary
import Relation.Binary.PropositionalEquality as PropEq
open PropEq hiding (refl)
open PropEq using (refl) public
-- ^ refl is re-exported so that it becomes available for instance
--   search when using the functions var and svar defined in this
--   module.

open ModeTheory ℳ


--------------------------------------------------
-- Re-exporting the definitions of types, contexts, terms and associated operations.

open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯 public
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯 String public
open import Experimental.LogicalFramework.MSTT.Syntax.General ℳ 𝒯 String 𝓉 public

private variable
  m n o : Mode
  μ : Modality m n
  Γ : Ctx m
  Λ : LockTele m n
  T S : Ty m
  x y : String


--------------------------------------------------
-- Preliminary work: we have to reimplement Is-just and from-witness
-- from Data.Maybe so that the definition does not use a data type and
-- hence satisfies η equality.

Is-just' : ∀ {ℓ} {A : Set ℓ} → Maybe A → Set _
Is-just' (just _) = ⊤
Is-just' nothing  = ⊥

to-witness' : ∀ {ℓ} {A : Set ℓ} {m : Maybe A} → Is-just' m → A
to-witness' {m = just a} _ = a


--------------------------------------------------
-- Constructing a variable term by only mentioning the variable name
--   (i.e. resolving the De Bruijn index automatically).
--   This works via a (semi)decision procedure for RawVar x Γ Λ.


-- A value of type RawVar x Γ Λ means that there is an entry in
-- context Γ ,ˡᵗ Λ with the name x.  It does however not provide the
-- necessary 2-cell, so this does not necessarily give rise to a valid
-- variable. Moreover, in the case of rvzero the domain of μ does not
-- necessarily correspond to the codomain of Λ. This will be tested
-- later, but it has to be done via instance resolution rather than
-- applying a (semi)decision procedure in order to accomodate some
-- form of mode polymorphism (m ≟mode m will be stuck when m contains
-- an Agda variable).
data RawVar (x : String) : Ctx m → LockTele m n → Set where
  rvzero : {Γ : Ctx m} {μ : Modality o m} {T : Ty o} {Λ : LockTele m n} →
           RawVar x (Γ ,, μ ∣ x ∈ T) Λ
  rvsuc : {Γ : Ctx m} {Λ : LockTele m n} {ρ : Modality o m} {y : String} {S : Ty o} →
          RawVar x Γ Λ →
          RawVar x (Γ ,, ρ ∣ y ∈ S) Λ
  rvlock : {Γ : Ctx o} {ρ : Modality m o} {Λ : LockTele m n} →
           RawVar x Γ (lock⟨ ρ ⟩, Λ) →
           RawVar x (Γ ,lock⟨ ρ ⟩) Λ


rawvar? : (x : String) (Γ : Ctx m) (Λ : LockTele m n) → Maybe (RawVar x Γ Λ)
rawvar? x ◇                 Λ = nothing
rawvar? x (Γ ,, μ ∣ y ∈ T)  Λ with x Str.≟ y
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
var : (x : String) {Γ : Ctx m} {i : Is-just' (rawvar? x Γ ◇)} →
      let rv = to-witness' i
      in {{ e : m ≡ rv-dom-mode rv }} →
         TwoCell (rv-mod rv) (subst (λ - → Modality - (rv-cod-mode rv)) e (locksˡᵗ (rv-lt rv))) →
         Tm Γ (subst Ty (sym e) (rv-ty rv))
var x {i = i} {{e}} α = var' _ {create-var (to-witness' i) e α}

svar : (x : String) {Γ : Ctx m} {i : Is-just' (rawvar? x Γ ◇)} →
       let rv = to-witness' i
       in {{ e : m ≡ rv-dom-mode rv }} →
          {{ rv-mod rv ≡ subst (λ - → Modality - (rv-cod-mode rv)) e (locksˡᵗ (rv-lt rv)) }} →
          Tm Γ (subst Ty (sym e) (rv-ty rv))
svar x {i = i} {{emode}} {{emod}} = var' _ {create-var (to-witness' i) emode (eq-cell emod)}
