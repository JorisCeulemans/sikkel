--------------------------------------------------
-- Checking equality for mode, modality and type expressions.
--------------------------------------------------

open import Applications.Parametricity.MSTT.Builtin

module Applications.Parametricity.MSTT.Equality (builtin : BuiltinTypes) where

open BuiltinTypes builtin

open import Data.String
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure as M hiding (◇)
open import Model.Type.Function as M hiding (_⇛_)
open import Model.Type.Product as M hiding (_⊠_)
open import Model.Modality as M hiding (𝟙; _ⓜ_; ⟨_∣_⟩)

open import Applications.Parametricity.MSTT.ModeTheory
open import Applications.Parametricity.MSTT.Syntax builtin
open import Applications.Parametricity.MSTT.TCMonad
open import Applications.Parametricity.MSTT.InterpretTypes builtin

private
  variable
    m m' : ModeExpr


--------------------------------------------------
-- (Semi-)decidable equality for mode, modality and type expressions
--   Requiring modalities and types to be truly identical is too restrictive,
--   therefore we have the decision procedures further below which allow for
--   more definitional equalities.

_≟mode_ : (m1 m2 : ModeExpr) → TCM (m1 ≡ m2)
★ ≟mode ★ = return refl
⋀ ≟mode ⋀ = return refl
m ≟mode m' = type-error ("Mode " ++ show-mode m ++ " is not equal to " ++ show-mode m')

_≟modality_ : (μ ρ : ModalityExpr m m') → TCM (μ ≡ ρ)
𝟙 ≟modality 𝟙 = return refl
forget-left ≟modality forget-left = return refl
forget-right ≟modality forget-right = return refl
μ ≟modality ρ = type-error ("Modality " ++ show-modality μ ++ " is not equal to " ++ show-modality ρ)

⟦_⟧≅mod?⟦_⟧ : (μ ρ : ModalityExpr m m') → TCM (⟦ μ ⟧modality ≅ᵐ ⟦ ρ ⟧modality)
⟦ μ ⟧≅mod?⟦ ρ ⟧ = do
  refl ← μ ≟modality ρ
  return ≅ᵐ-refl

reduce-comp-helper : ModalityExpr m m' → TyExpr m → TyExpr m'
reduce-comp-helper μ Nat' = ⟨ μ ∣ Nat' ⟩
reduce-comp-helper μ Bool' = ⟨ μ ∣ Bool' ⟩
reduce-comp-helper μ (T ⇛ S) = ⟨ μ ∣ T ⇛ S ⟩
reduce-comp-helper μ (T ⊠ S) = ⟨ μ ∣ T ⊠ S ⟩
reduce-comp-helper μ ⟨ ρ ∣ T ⟩ = ⟨ μ ⓜ ρ ∣ T ⟩
reduce-comp-helper μ (Builtin c) = ⟨ μ ∣ Builtin c ⟩

reduce-comp : TyExpr m → TyExpr m
reduce-comp Nat' = Nat'
reduce-comp Bool' = Bool'
reduce-comp (T ⇛ S) = reduce-comp T ⇛ reduce-comp S
reduce-comp (T ⊠ S) = reduce-comp T ⊠ reduce-comp S
reduce-comp ⟨ μ ∣ T ⟩ = reduce-comp-helper μ (reduce-comp T)
reduce-comp (Builtin c) = Builtin c

reduce-comp-helper-sound : (μ : ModalityExpr m m') (T : TyExpr m) → ∀ {Γ} →
                           ⟦ reduce-comp-helper μ T ⟧ty {Γ} ≅ᵗʸ ⟦ ⟨ μ ∣ T ⟩ ⟧ty
reduce-comp-helper-sound μ Nat' = ≅ᵗʸ-refl
reduce-comp-helper-sound μ Bool' = ≅ᵗʸ-refl
reduce-comp-helper-sound μ (T ⇛ S) = ≅ᵗʸ-refl
reduce-comp-helper-sound μ (T ⊠ S) = ≅ᵗʸ-refl
reduce-comp-helper-sound μ ⟨ ρ ∣ T ⟩ = eq-mod-closed (ⓜ-interpretation μ ρ) ⟦ T ⟧ty {{⟦⟧ty-natural T}}
reduce-comp-helper-sound μ (Builtin c) = ≅ᵗʸ-refl

reduce-comp-sound : (T : TyExpr m) → ∀ {Γ} → ⟦ reduce-comp T ⟧ty {Γ} ≅ᵗʸ ⟦ T ⟧ty
reduce-comp-sound Nat' = ≅ᵗʸ-refl
reduce-comp-sound Bool' = ≅ᵗʸ-refl
reduce-comp-sound (T ⇛ S) = ⇛-cong (reduce-comp-sound T) (reduce-comp-sound S)
reduce-comp-sound (T ⊠ S) = ⊠-cong (reduce-comp-sound T) (reduce-comp-sound S)
reduce-comp-sound ⟨ μ ∣ T ⟩ = ≅ᵗʸ-trans (reduce-comp-helper-sound μ (reduce-comp T))
                                        (mod-cong ⟦ μ ⟧modality (reduce-comp-sound T))
reduce-comp-sound (Builtin c) = ≅ᵗʸ-refl

reduce-unit-helper : ModalityExpr m m' → TyExpr m → TyExpr m'
reduce-unit-helper {m} {m'} μ T with m ≟mode m'
reduce-unit-helper {m} {m'} μ T | type-error _ = ⟨ μ ∣ T ⟩
reduce-unit-helper {m} {m'} μ T | ok refl with ⟦ 𝟙 ⟧≅mod?⟦ μ ⟧
reduce-unit-helper {m} {m'} μ T | ok refl | type-error _ = ⟨ μ ∣ T ⟩
reduce-unit-helper {m} {m'} μ T | ok refl | ok _ = T

reduce-unit : TyExpr m → TyExpr m
reduce-unit Nat' = Nat'
reduce-unit Bool' = Bool'
reduce-unit (T ⇛ S) = reduce-unit T ⇛ reduce-unit S
reduce-unit (T ⊠ S) = reduce-unit T ⊠ reduce-unit S
reduce-unit ⟨ μ ∣ T ⟩ = reduce-unit-helper μ (reduce-unit T)
reduce-unit (Builtin c) = Builtin c

reduce-unit-helper-sound : (μ : ModalityExpr m m') (T : TyExpr m) → ∀ {Γ} →
                           ⟦ reduce-unit-helper μ T ⟧ty {Γ} ≅ᵗʸ ⟦ ⟨ μ ∣ T ⟩ ⟧ty
reduce-unit-helper-sound {m} {m'} μ T with m ≟mode m'
reduce-unit-helper-sound {m} {m'} μ T | type-error _ = ≅ᵗʸ-refl
reduce-unit-helper-sound {m} {m'} μ T | ok refl with ⟦ 𝟙 ⟧≅mod?⟦ μ ⟧
reduce-unit-helper-sound {m} {m'} μ T | ok refl | type-error _ = ≅ᵗʸ-refl
reduce-unit-helper-sound {m} {m'} μ T | ok refl | ok 𝟙=μ = eq-mod-closed 𝟙=μ ⟦ T ⟧ty {{⟦⟧ty-natural T}}

reduce-unit-sound : (T : TyExpr m) → ∀ {Γ} → ⟦ reduce-unit T ⟧ty {Γ} ≅ᵗʸ ⟦ T ⟧ty
reduce-unit-sound Nat' = ≅ᵗʸ-refl
reduce-unit-sound Bool' = ≅ᵗʸ-refl
reduce-unit-sound (T ⇛ S) = ⇛-cong (reduce-unit-sound T) (reduce-unit-sound S)
reduce-unit-sound (T ⊠ S) = ⊠-cong (reduce-unit-sound T) (reduce-unit-sound S)
reduce-unit-sound ⟨ μ ∣ T ⟩ = ≅ᵗʸ-trans (reduce-unit-helper-sound μ (reduce-unit T))
                                        (mod-cong ⟦ μ ⟧modality (reduce-unit-sound T))
reduce-unit-sound (Builtin c) = ≅ᵗʸ-refl

reduce-ty : TyExpr m → TyExpr m
reduce-ty = reduce-unit ∘ reduce-comp

reduce-ty-sound : (T : TyExpr m) → ∀ {Γ} → ⟦ reduce-ty T ⟧ty {Γ} ≅ᵗʸ ⟦ T ⟧ty
reduce-ty-sound T = ≅ᵗʸ-trans (reduce-unit-sound (reduce-comp T))
                              (reduce-comp-sound T)

⟦_⟧≅ty-strict?⟦_⟧ : (T S : TyExpr m) → TCM (∀ {Γ} → ⟦ T ⟧ty {Γ} ≅ᵗʸ ⟦ S ⟧ty)
⟦ Nat' ⟧≅ty-strict?⟦ Nat' ⟧ = return ≅ᵗʸ-refl
⟦ Bool' ⟧≅ty-strict?⟦ Bool' ⟧ = return ≅ᵗʸ-refl
⟦ T1 ⇛ S1 ⟧≅ty-strict?⟦ T2 ⇛ S2 ⟧ = do
  T1=T2 ← ⟦ T1 ⟧≅ty-strict?⟦ T2 ⟧
  S1=S2 ← ⟦ S1 ⟧≅ty-strict?⟦ S2 ⟧
  return (⇛-cong T1=T2 S1=S2)
⟦ T1 ⊠ S1 ⟧≅ty-strict?⟦ T2 ⊠ S2 ⟧ = do
  T1=T2 ← ⟦ T1 ⟧≅ty-strict?⟦ T2 ⟧
  S1=S2 ← ⟦ S1 ⟧≅ty-strict?⟦ S2 ⟧
  return (⊠-cong T1=T2 S1=S2)
⟦ ⟨_∣_⟩ {mT} μ T ⟧≅ty-strict?⟦ ⟨_∣_⟩ {mS} ρ S ⟧ = do
  refl ← mT ≟mode mS
  μ=ρ ← ⟦ μ ⟧≅mod?⟦ ρ ⟧
  T=S ← ⟦ T ⟧≅ty-strict?⟦ S ⟧
  return (≅ᵗʸ-trans (eq-mod-closed μ=ρ ⟦ T ⟧ty {{⟦⟧ty-natural T}})
                    (mod-cong ⟦ ρ ⟧modality T=S))
⟦ Builtin c1 ⟧≅ty-strict?⟦ Builtin c2 ⟧ = do
  refl ← c1 ≟code c2
  return ≅ᵗʸ-refl
⟦ T ⟧≅ty-strict?⟦ S ⟧ = type-error ("Type " ++ show-type T ++ " is not equal to " ++ show-type S)

ty-reflect : (T S : TyExpr m) → (∀ {Γ} → ⟦ reduce-ty T ⟧ty {Γ} ≅ᵗʸ ⟦ reduce-ty S ⟧ty) →
             ∀ {Γ} → ⟦ T ⟧ty {Γ} ≅ᵗʸ ⟦ S ⟧ty
ty-reflect T S e = ≅ᵗʸ-trans (≅ᵗʸ-trans (≅ᵗʸ-sym (reduce-ty-sound T))
                                        e)
                             (reduce-ty-sound S)

reduce-compare-ty : (T S : TyExpr m) → TCM (∀ {Γ} → ⟦ T ⟧ty {Γ} ≅ᵗʸ ⟦ S ⟧ty)
reduce-compare-ty T S =
  let T' = reduce-ty T
      S' = reduce-ty S
  in with-error-msg ("Type " ++ show-type T ++ " is not equal to " ++ show-type S ++ ", reduced the equality to " ++
                      show-type T' ++ " =?= " ++ show-type S') (
    (⟦ T' ⟧≅ty-strict?⟦ S' ⟧) >>= λ T'=S' → return (ty-reflect T S T'=S'))

⟦_⟧≅ty?⟦_⟧ : (T S : TyExpr m) → TCM (∀ {Γ} → ⟦ T ⟧ty {Γ} ≅ᵗʸ ⟦ S ⟧ty)
⟦ T ⟧≅ty?⟦ S ⟧ = ⟦ T ⟧≅ty-strict?⟦ S ⟧ <∣> reduce-compare-ty T S
