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
open import Data.Product
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
ExtBPArgs : {m : Mode} (arginfos : List (ArgInfo m)) → ArgBoundNames arginfos → Ctx m → Set

data bProp {m} Γ where
  ⊤ᵇ ⊥ᵇ : bProp Γ
  _≡ᵇ_ : {T : Ty m} (t1 t2 : Tm Γ T) → bProp Γ
  ⟨_∣_⟩⊃_ : (μ : Modality n m) (φ : bProp (Γ ,lock⟨ μ ⟩)) (ψ : bProp Γ) → bProp Γ
  _∧_ : (φ ψ : bProp Γ) → bProp Γ
  ∀[_∣_∈_]_ : (μ : Modality n m) (x : Name) (T : Ty n) → bProp (Γ ,, μ ∣ x ∈ T) → bProp Γ
  ⟨_∣_⟩ : (μ : Modality n m) → bProp (Γ ,lock⟨ μ ⟩) → bProp Γ
  ext : (c : bPropExtCode m)
        (tmarg-names : TmArgBoundNames (bp-code-tmarg-infos c)) (tmargs : ExtTmArgs (bp-code-tmarg-infos c) tmarg-names Γ)
        (bparg-names : ArgBoundNames (bp-code-bparg-infos c)) (bpargs : ExtBPArgs (bp-code-bparg-infos c) bparg-names Γ) →
        bProp Γ
    -- ^ This constructor is not intended for direct use. An instantiation of BiSikkel with
    --   specific proposition extensions should rather provide more convenient bProp formers
    --   via pattern synonyms.

ExtBPArgs []               _                        Γ = ⊤
ExtBPArgs (info ∷ bpinfos) (arg-names , args-names) Γ =
  bProp (Γ ++tel add-names (arg-tel info) arg-names) × ExtBPArgs bpinfos args-names Γ


¬⟨_⟩_ : (μ : Modality m n) {Γ : Ctx n} → bProp (Γ ,lock⟨ μ ⟩) → bProp Γ
¬⟨ μ ⟩ φ = ⟨ μ ∣ φ ⟩⊃ ⊥ᵇ


--------------------------------------------------
-- Renaming and substitution for BiSikkel propositions

module bPropTraversal
  (Trav : ∀ {m} → Ctx m → Ctx m → Set)
  (trav-struct : TravStruct Trav)
  where

  open TravStruct trav-struct

  traverse-bprop : bProp Δ → Trav Γ Δ → bProp Γ
  traverse-ext-bpargs : {bpinfos : List (ArgInfo m)} {names : ArgBoundNames bpinfos} →
                        ExtBPArgs bpinfos names Δ → Trav Γ Δ → ExtBPArgs bpinfos names Γ

  traverse-bprop ⊤ᵇ σ = ⊤ᵇ
  traverse-bprop ⊥ᵇ σ = ⊥ᵇ
  traverse-bprop (t1 ≡ᵇ t2) σ = traverse-tm t1 σ ≡ᵇ traverse-tm t2 σ
  traverse-bprop (⟨ μ ∣ φ ⟩⊃ ψ) σ = ⟨ μ ∣ traverse-bprop φ (lock σ) ⟩⊃ traverse-bprop ψ σ
  traverse-bprop (φ ∧ ψ) σ = traverse-bprop φ σ ∧ traverse-bprop ψ σ
  traverse-bprop (∀[ μ ∣ x ∈ T ] φ) σ = ∀[ μ ∣ x ∈ T ] traverse-bprop φ (lift σ)
  traverse-bprop ⟨ μ ∣ φ ⟩ σ = ⟨ μ ∣ traverse-bprop φ (lock σ) ⟩
  traverse-bprop (ext c tmarg-names tmargs bparg-names bpargs) σ =
    ext c tmarg-names (traverse-ext-tmargs tmargs σ) bparg-names (traverse-ext-bpargs bpargs σ)

  traverse-ext-bpargs {bpinfos = []}               _                σ = tt
  traverse-ext-bpargs {bpinfos = bpinfo ∷ bpinfos} (bparg , bpargs) σ =
    traverse-bprop bparg (lift-trav-tel σ (add-names (arg-tel bpinfo) _)) , traverse-ext-bpargs bpargs σ


module bPropRenSub
  (V : RenSubData)
  (rensub-struct : RenSubDataStructure V)
  where

  open AtomicRenSub V rensub-struct
  open RenSub V rensub-struct
  
  open bPropTraversal AtomicRenSub AtomicRenSubTrav

  _[_]bpropᵃ : bProp Δ → AtomicRenSub Γ Δ → bProp Γ
  φ [ σ ]bpropᵃ = traverse-bprop φ σ

  -- Similar to term renaming/substitution, this could be optimized
  -- for performance by pushing an entire rensub inside a bprop
  -- instead of every atomic rensub separately. However, composite
  -- rensubs do not occur in practice, so we do not implement this.
  _[_]bpropʳˢ : bProp Δ → RenSub Γ Δ → bProp Γ
  φ [ id ]bpropʳˢ      = φ
  φ [ σ ⊚a τᵃ ]bpropʳˢ = (φ [ σ ]bpropʳˢ) [ τᵃ ]bpropᵃ


module bPropRen = bPropRenSub RenData AtomicRenVar.ren-data-struct
open bPropRen renaming
  ( _[_]bpropᵃ to _[_]bpropᵃʳ
  ; _[_]bpropʳˢ to _[_]bpropʳ
  ) public

module bPropSub = bPropRenSub SubData AtomicSubVar.sub-data-struct
open bPropSub renaming
  ( _[_]bpropᵃ to _[_]bpropᵃˢ
  ; _[_]bpropʳˢ to _[_]bpropˢ
  ) public


-- Isomorphisms witnessing the functoriality of locks (with respect to propositions)
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
