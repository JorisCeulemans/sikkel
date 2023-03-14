--------------------------------------------------
-- Instantiation of the general MSTT syntax with strings as names
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.ModeTheory

module Experimental.LogicalFramework.MSTT.Syntax.Named (ℳ : ModeTheory) where

open import Data.Empty
open import Data.Product
open import Data.String as Str
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
import Relation.Binary.PropositionalEquality as PropEq
open PropEq hiding (refl)
open PropEq using (refl) public
-- ^ refl is re-exported so that it becomes available for instance
--   search when using the functions var and svar defined in this
--   module.

open ModeTheory ℳ


--------------------------------------------------
-- Re-exporting the definitions of types, contexts, terms and associated operations.

open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ public
open import Experimental.LogicalFramework.MSTT.Syntax.General ℳ String public

private variable
  m n : Mode
  μ : Modality m n
  Γ : Ctx m
  T S : Ty m
  x y : String


--------------------------------------------------
-- Constructing a variable term by only mentioning the variable name
--   (i.e. resolving the De Bruijn index automatically).
--   This works via a decision procedure for Contains x Γ.

record Contains (x : String) (Γ : Ctx m) : Set where
  constructor contains
  field
    {o var-mode} : Mode
    mod : Modality var-mode o
    type : Ty var-mode
    locks : Modality m o
    v : Var x mod type locks Γ

contains-vsuc : Contains x Γ → Contains x (Γ ,, μ ∣ y ∈ S)
contains-vsuc (contains ρ T κ v) = contains ρ T κ (vsuc v)

contains-vpred : ¬ (x ≡ y) → Contains x (Γ ,, μ ∣ y ∈ S) → Contains x Γ
contains-vpred ¬x=y (contains ρ T .𝟙 vzero) = ⊥-elim (¬x=y refl)
contains-vpred ¬x=y (contains ρ T κ (vsuc v)) = contains ρ T κ v

contains-skip-lock : Contains x Γ → Contains x (Γ ,lock⟨ μ ⟩)
contains-skip-lock {μ = μ} (contains ρ T κ v) = contains ρ T (κ ⓜ μ) (skip-lock μ v)

contains-unskip-lock : Contains x (Γ ,lock⟨ μ ⟩) → Contains x Γ
contains-unskip-lock (contains ρ T .(κ ⓜ μ) (skip-lock {κ = κ} μ v)) = contains ρ T κ v

var? : (x : String) (Γ : Ctx m) → Dec (Contains x Γ)
var? x ◇ = no (λ ())
var? x (Γ ,, μ ∣ y ∈ T) with x Str.≟ y
var? x (Γ ,, μ ∣ .x ∈ T) | yes refl = yes (contains μ T 𝟙 vzero)
var? x (Γ ,, μ ∣ y  ∈ T) | no ¬x=y = map′ contains-vsuc (contains-vpred ¬x=y) (var? x Γ)
var? x (Γ ,lock⟨ μ ⟩) = map′ contains-skip-lock contains-unskip-lock (var? x Γ)

open Contains
var-helper : (x : String) {Γ : Ctx m} (c : Contains x Γ) (e : var-mode c ≡ m) →
             TwoCell (subst (λ - → Modality - (o c)) e (mod c)) (locks c) → Tm Γ (subst Ty e (type c))
var-helper x (contains μ T κ v) refl α = var' x {v} α

-- Note that the instance argument mode-eq is intended to be solved as
-- refl by instance search, and hence the two instances of subst in
-- the type will reduce.
var : (x : String) {Γ : Ctx m} {v : True (var? x Γ)} →
      let contains {o} {p} μ T κ w = toWitness v
      in {{mode-eq : p ≡ m}} → TwoCell (subst (λ - → Modality - o) mode-eq μ) κ → Tm Γ (subst Ty mode-eq T)
var x {v = v} {{e}} α = var-helper x (toWitness v) e α

svar-helper : (x : String) {Γ : Ctx m} (c : Contains x Γ) (e : var-mode c ≡ m) →
              subst (λ - → Modality - (o c)) e (mod c) ≡ locks c → Tm Γ (subst Ty e (type c))
svar-helper x c mode-eq mod-eq = var-helper x c mode-eq (subst (TwoCell _) mod-eq id-cell )

svar : (x : String) {Γ : Ctx m} {v : True (var? x Γ)} →
       let contains {o} {p} μ T κ w = toWitness v
       in {{mode-eq : p ≡ m}} → {{ subst (λ - → Modality - o) mode-eq μ ≡ κ }} → Tm Γ (subst Ty mode-eq T)
svar x {v = v} {{mode-eq}} {{mod-eq}} = svar-helper x (toWitness v) mode-eq mod-eq
