--------------------------------------------------
-- Definition of BiSikkel propositions and their substitution
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension using (bPropExt)

module Experimental.LogicalFramework.bProp.Syntax
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉)
  where

open import Data.List
open import Data.Product renaming (_,_ to [_,_])
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open bPropExt 𝒷

open import Experimental.LogicalFramework.MSTT.Syntax ℳ 𝒯 𝓉

open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯
open import Experimental.LogicalFramework.Parameter.bPropExtension ℳ 𝒯 𝓉
open import Experimental.LogicalFramework.Parameter.ArgInfo ℳ 𝒯

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


--------------------------------------------------
-- Definition of BiSikkel propositions

-- TODO: include connective for disjunction and existential quantification.
data bProp {m} (Γ : Ctx m) : Set
ExtBPArgs : {m : Mode} → List (ArgInfo m) → Ctx m → Set

data bProp {m} Γ where
  ⊤ᵇ ⊥ᵇ : bProp Γ
  _≡ᵇ_ : {T : Ty m} (t1 t2 : Tm Γ T) → bProp Γ
  ⟨_∣_⟩⊃_ : (μ : Modality n m) (φ : bProp (Γ ,lock⟨ μ ⟩)) (ψ : bProp Γ) → bProp Γ
  _∧_ : (φ ψ : bProp Γ) → bProp Γ
  ∀[_∣_∈_]_ : (μ : Modality n m) (x : Name) (T : Ty n) → bProp (Γ ,, μ ∣ x ∈ T) → bProp Γ
  ⟨_∣_⟩ : (μ : Modality n m) → bProp (Γ ,lock⟨ μ ⟩) → bProp Γ
  ext : (c : bPropExtCode m) → ExtTmArgs (bp-code-tmarg-infos c) Γ → ExtBPArgs (bp-code-bparg-infos c) Γ → bProp Γ
    -- ^ This constructor is not intended for direct use. An instantiation of BiSikkel with
    --   specific proposition extensions should rather provide more convenient bProp formers
    --   via pattern synonyms.

ExtBPArgs []               Γ = ⊤
ExtBPArgs (info ∷ bpinfos) Γ = bProp (Γ ++tel arg-tel info) × ExtBPArgs bpinfos Γ


¬⟨_⟩_ : (μ : Modality m n) {Γ : Ctx n} → bProp (Γ ,lock⟨ μ ⟩) → bProp Γ
¬⟨ μ ⟩ φ = ⟨ μ ∣ φ ⟩⊃ ⊥ᵇ


--------------------------------------------------
-- Renaming and substitution for BiSikkel propositions

-- A proposition can be traversed whenever terms can be traversed.
--   Note that this record has a special field specifying how a
--   traversal object acts on terms. This way, we can instantiate this
--   with the exact definition of substitution or renaming for terms,
--   rather than having some equivalent reimplementation of it.
record bPropTravStruct (Trav : ∀ {m} → Ctx m → Ctx m → Set) : Set where
  field
    trav-tm : Tm Δ T → Trav Γ Δ → Tm Γ T
    lift : Trav Γ Δ → Trav (Γ ,, μ ∣ x ∈ T) (Δ ,, μ ∣ x ∈ T)
    lock : Trav Γ Δ → Trav (Γ ,lock⟨ μ ⟩) (Δ ,lock⟨ μ ⟩)

  lift-trav-tel : Trav Γ Δ → (Θ : Telescope m n) → Trav (Γ ++tel Θ) (Δ ++tel Θ)
  lift-trav-tel σ ◇ = σ
  lift-trav-tel σ (Θ ,, μ ∣ x ∈ T) = lift (lift-trav-tel σ Θ)
  lift-trav-tel σ (Θ ,lock⟨ μ ⟩) = lock (lift-trav-tel σ Θ)

  trav-ext-tmargs : ∀ {infos} → ExtTmArgs infos Δ → Trav Γ Δ → ExtTmArgs infos Γ
  trav-ext-tmargs {infos = []}       _                  σ = tt
  trav-ext-tmargs {infos = info ∷ _} [ tmarg , tmargs ] σ =
    [ trav-tm tmarg (lift-trav-tel σ (tmarg-tel info)) , trav-ext-tmargs tmargs σ ]

  traverse-bprop : bProp Δ → Trav Γ Δ → bProp Γ
  traverse-ext-bpargs : {bpinfos : List (ArgInfo m)} → ExtBPArgs bpinfos Δ → Trav Γ Δ → ExtBPArgs bpinfos Γ

  traverse-bprop ⊤ᵇ σ = ⊤ᵇ
  traverse-bprop ⊥ᵇ σ = ⊥ᵇ
  traverse-bprop (t1 ≡ᵇ t2) σ = trav-tm t1 σ ≡ᵇ trav-tm t2 σ
  traverse-bprop (⟨ μ ∣ φ ⟩⊃ ψ) σ = ⟨ μ ∣ traverse-bprop φ (lock σ) ⟩⊃ traverse-bprop ψ σ
  traverse-bprop (φ ∧ ψ) σ = traverse-bprop φ σ ∧ traverse-bprop ψ σ
  traverse-bprop (∀[ μ ∣ x ∈ T ] φ) σ = ∀[ μ ∣ x ∈ T ] traverse-bprop φ (lift σ)
  traverse-bprop ⟨ μ ∣ φ ⟩ σ = ⟨ μ ∣ traverse-bprop φ (lock σ) ⟩
  traverse-bprop (ext c tmargs bpargs) σ = ext c (trav-ext-tmargs tmargs σ) (traverse-ext-bpargs bpargs σ)

  traverse-ext-bpargs {bpinfos = []}               _                  σ = tt
  traverse-ext-bpargs {bpinfos = bpinfo ∷ bpinfos} [ bparg , bpargs ] σ =
    [ traverse-bprop bparg (lift-trav-tel σ (arg-tel bpinfo)) , traverse-ext-bpargs bpargs σ ]

open bPropTravStruct using (traverse-bprop)


renbPropTrav : bPropTravStruct Ren
bPropTravStruct.trav-tm renbPropTrav = _[_]tmʳ
bPropTravStruct.lift renbPropTrav = liftʳ
bPropTravStruct.lock renbPropTrav {μ = μ} = _,lockʳ⟨ μ ⟩

_[_]bpropʳ : bProp Δ → Ren Γ Δ → bProp Γ
_[_]bpropʳ = traverse-bprop renbPropTrav


subbPropTrav : bPropTravStruct Sub
bPropTravStruct.trav-tm subbPropTrav = _[_]tmˢ
bPropTravStruct.lift subbPropTrav = liftˢ
bPropTravStruct.lock subbPropTrav {μ = μ} = _,lockˢ⟨ μ ⟩

_[_]bpropˢ : bProp Δ → Sub Γ Δ → bProp Γ
φ [ σ ]bpropˢ = traverse-bprop subbPropTrav φ σ


-- Isomorphisms witnessing the functoriality of locks (wrt propositions)
lock𝟙-bprop : bProp Γ → bProp (Γ ,lock⟨ 𝟙 ⟩)
lock𝟙-bprop t = t [ lock𝟙-ren ]bpropʳ

unlock𝟙-bprop : bProp (Γ ,lock⟨ 𝟙 ⟩) → bProp Γ
unlock𝟙-bprop t = t [ unlock𝟙-ren ]bpropʳ

fuselocks-bprop : bProp (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩) → bProp (Γ ,lock⟨ μ ⓜ ρ ⟩)
fuselocks-bprop t = t [ fuselocks-ren ]bpropʳ

unfuselocks-bprop : bProp (Γ ,lock⟨ μ ⓜ ρ ⟩) → bProp (Γ ,lock⟨ μ ⟩ ,lock⟨ ρ ⟩)
unfuselocks-bprop t = t [ unfuselocks-ren ]bpropʳ


_⊃_ : (φ ψ : bProp Γ) → bProp Γ
φ ⊃ ψ = ⟨ 𝟙 ∣ lock𝟙-bprop φ ⟩⊃ ψ

¬ : bProp Γ → bProp Γ
¬ φ = φ ⊃ ⊥ᵇ
