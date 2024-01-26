--------------------------------------------------
-- Definition of BiSikkel propositions and their substitution
--   Just as MSTT syntax, the general definition of propositions is
--   parametrised by a type of names to represent variables. It is not
--   recommended to directly import this module, but rather use
--   bProp.Named.
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension using (TmExt)
open import Experimental.LogicalFramework.Parameter.bPropExtension

module Experimental.LogicalFramework.bProp.General
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (Name : Set) (𝓉 : TmExt ℳ 𝒯 Name)
  (𝒷 : bPropExt ℳ 𝒯 Name 𝓉)
  where

open import Data.List
open import Data.Product renaming (_,_ to [_,_])
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open ModeTheory ℳ
open bPropExt 𝒷

open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯 Name
open import Experimental.LogicalFramework.MSTT.Syntax.General ℳ 𝒯 Name 𝓉

open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯 Name
open import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯 Name

private variable
  m n : Mode
  μ ρ : Modality m n
  x : Name
  Γ Δ : Ctx m
  T : Ty m


infixl 3 ∀[_∣_∈_]_
infixr 6 _⊃_
infixl 9 _∧_
infix 12 _≡ᵇ_


bPropExtTmArgs : {m : Mode} → List (TmArgInfo m) → Ctx m → Set
bPropExtTmArgs []               Γ = ⊤
bPropExtTmArgs (info ∷ tminfos) Γ = Tm (Γ ++tel tmarg-tel info) (tmarg-ty info) × bPropExtTmArgs tminfos Γ

-- TODO: include connective for disjunction and existential quantification.
data bProp {m} (Γ : Ctx m) : Set
bPropExtBPArgs : {m : Mode} → List (ArgInfo m) → Ctx m → Set

data bProp {m} Γ where
  ⊤ᵇ ⊥ᵇ : bProp Γ
  _≡ᵇ_ : {T : Ty m} (t1 t2 : Tm Γ T) → bProp Γ
  ⟨_∣_⟩⊃_ : (μ : Modality n m) (φ : bProp (Γ ,lock⟨ μ ⟩)) (ψ : bProp Γ) → bProp Γ
  _∧_ : (φ ψ : bProp Γ) → bProp Γ
  ∀[_∣_∈_]_ : (μ : Modality n m) (x : Name) (T : Ty n) → bProp (Γ ,, μ ∣ x ∈ T) → bProp Γ
  ⟨_∣_⟩ : (μ : Modality n m) → bProp (Γ ,lock⟨ μ ⟩) → bProp Γ
  ext : (c : bPropExtCode m) → bPropExtTmArgs (bp-code-tmarg-infos c) Γ → bPropExtBPArgs (bp-code-bparg-infos c) Γ → bProp Γ
    -- ^ This constructor is not intended for direct use. An instantiation of BiSikkel with
    --   specific proposition extensions should rather provide more convenient bProp formers
    --   via pattern synonyms.

bPropExtBPArgs []               Γ = ⊤
bPropExtBPArgs (info ∷ bpinfos) Γ = bProp (Γ ++tel arg-tel info) × bPropExtBPArgs bpinfos Γ


¬⟨_⟩_ : (μ : Modality m n) {Γ : Ctx n} → bProp (Γ ,lock⟨ μ ⟩) → bProp Γ
¬⟨ μ ⟩ φ = ⟨ μ ∣ φ ⟩⊃ ⊥ᵇ


-- A proposition can be traversed whenever terms can be traversed
record bPropTravStruct (Trav : ∀ {m} → Ctx m → Ctx m → Set) : Set where
  field
    trav-tm : Tm Δ T → Trav Γ Δ → Tm Γ T
    lift : Trav Γ Δ → Trav (Γ ,, μ ∣ x ∈ T) (Δ ,, μ ∣ x ∈ T)
    lock : Trav Γ Δ → Trav (Γ ,lock⟨ μ ⟩) (Δ ,lock⟨ μ ⟩)

  lift-trav-tel : Trav Γ Δ → (Θ : Telescope m n) → Trav (Γ ++tel Θ) (Δ ++tel Θ)
  lift-trav-tel σ ◇ = σ
  lift-trav-tel σ (Θ ,, μ ∣ x ∈ T) = lift (lift-trav-tel σ Θ)
  lift-trav-tel σ (Θ ,lock⟨ μ ⟩) = lock (lift-trav-tel σ Θ)

  traverse-ext-tm-args : {tminfos : List (TmArgInfo m)} → bPropExtTmArgs tminfos Δ → Trav Γ Δ → bPropExtTmArgs tminfos Γ
  traverse-ext-tm-args {tminfos = []}               _                  σ = tt
  traverse-ext-tm-args {tminfos = tminfo ∷ tminfos} [ tmarg , tmargs ] σ =
    [ trav-tm tmarg (lift-trav-tel σ (tmarg-tel tminfo)) , traverse-ext-tm-args tmargs σ ]

  traverse-bprop : bProp Δ → Trav Γ Δ → bProp Γ
  traverse-ext-bp-args : {bpinfos : List (ArgInfo m)} → bPropExtBPArgs bpinfos Δ → Trav Γ Δ → bPropExtBPArgs bpinfos Γ

  traverse-bprop ⊤ᵇ σ = ⊤ᵇ
  traverse-bprop ⊥ᵇ σ = ⊥ᵇ
  traverse-bprop (t1 ≡ᵇ t2) σ = trav-tm t1 σ ≡ᵇ trav-tm t2 σ
  traverse-bprop (⟨ μ ∣ φ ⟩⊃ ψ) σ = ⟨ μ ∣ traverse-bprop φ (lock σ) ⟩⊃ traverse-bprop ψ σ
  traverse-bprop (φ ∧ ψ) σ = traverse-bprop φ σ ∧ traverse-bprop ψ σ
  traverse-bprop (∀[ μ ∣ x ∈ T ] φ) σ = ∀[ μ ∣ x ∈ T ] traverse-bprop φ (lift σ)
  traverse-bprop ⟨ μ ∣ φ ⟩ σ = ⟨ μ ∣ traverse-bprop φ (lock σ) ⟩
  traverse-bprop (ext c tmargs bpargs) σ = ext c (traverse-ext-tm-args tmargs σ) (traverse-ext-bp-args bpargs σ)

  traverse-ext-bp-args {bpinfos = []}               _                  σ = tt
  traverse-ext-bp-args {bpinfos = bpinfo ∷ bpinfos} [ bparg , bpargs ] σ =
    [ traverse-bprop bparg (lift-trav-tel σ (arg-tel bpinfo)) , traverse-ext-bp-args bpargs σ ]

open bPropTravStruct using (traverse-bprop)


renbPropTrav : bPropTravStruct Ren
bPropTravStruct.trav-tm renbPropTrav = rename-tm
bPropTravStruct.lift renbPropTrav = lift-ren
bPropTravStruct.lock renbPropTrav = λ σ → σ ,rlock⟨ _ ⟩

rename-bprop : bProp Δ → Ren Γ Δ → bProp Γ
rename-bprop = traverse-bprop renbPropTrav


subbPropTrav : bPropTravStruct Sub
bPropTravStruct.trav-tm subbPropTrav = _[_]tm
bPropTravStruct.lift subbPropTrav = lift-sub
bPropTravStruct.lock subbPropTrav = λ σ → σ ,slock⟨ _ ⟩

_[_]bprop : bProp Δ → Sub Γ Δ → bProp Γ
φ [ σ ]bprop = traverse-bprop subbPropTrav φ σ


-- Isomorphisms witnessing the functoriality of locks (wrt propositions)
lock𝟙-bprop : bProp Γ → bProp (Γ ,lock⟨ 𝟙 ⟩)
lock𝟙-bprop t = rename-bprop t (lock𝟙-ren)

unlock𝟙-bprop : bProp (Γ ,lock⟨ 𝟙 ⟩) → bProp Γ
unlock𝟙-bprop t = rename-bprop t (unlock𝟙-ren)

fuselocks-bprop : bProp (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) → bProp (Γ ,lock⟨ μ ⓜ ρ ⟩)
fuselocks-bprop t = rename-bprop t fuselocks-ren

unfuselocks-bprop : bProp (Γ ,lock⟨ μ ⓜ ρ ⟩) → bProp (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩)
unfuselocks-bprop t = rename-bprop t unfuselocks-ren


_⊃_ : (φ ψ : bProp Γ) → bProp Γ
φ ⊃ ψ = ⟨ 𝟙 ∣ lock𝟙-bprop φ ⟩⊃ ψ

¬ : bProp Γ → bProp Γ
¬ φ = φ ⊃ ⊥ᵇ
