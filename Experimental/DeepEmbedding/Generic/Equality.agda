open import Experimental.DeepEmbedding.Generic.Builtin.ModeTheory

module Experimental.DeepEmbedding.Generic.Equality (mt : ModeTheory) where


open import Data.String
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import CwF-Structure hiding (_++_)
open import Modalities as M hiding (⟨_∣_⟩; 𝟙; _ⓜ_)
open import Types.Functions as M hiding (_⇛_)
open import Types.Products as M hiding (_⊠_)

open import Experimental.DeepEmbedding.Generic.TCMonad
open import Experimental.DeepEmbedding.Generic.Syntax mt
open import Experimental.DeepEmbedding.Generic.InterpretTypes mt

open ModeTheory mt

private
  variable
    m m' : ModeExpr


reduce-comp-helper : ModalityExpr m m' → TyExpr m → TyExpr m'
reduce-comp-helper μ Nat' = ⟨ μ ∣ Nat' ⟩
reduce-comp-helper μ Bool' = ⟨ μ ∣ Bool' ⟩
reduce-comp-helper μ (T ⇛ S) = ⟨ μ ∣ T ⇛ S ⟩
reduce-comp-helper μ (T ⊠ S) = ⟨ μ ∣ T ⊠ S ⟩
reduce-comp-helper μ ⟨ ρ ∣ T ⟩ = ⟨ μ ⓜ ρ ∣ T ⟩

reduce-comp : TyExpr m → TyExpr m
reduce-comp Nat' = Nat'
reduce-comp Bool' = Bool'
reduce-comp (T ⇛ S) = reduce-comp T ⇛ reduce-comp S
reduce-comp (T ⊠ S) = reduce-comp T ⊠ reduce-comp S
reduce-comp ⟨ μ ∣ T ⟩ = reduce-comp-helper μ (reduce-comp T)

reduce-comp-helper-sound : (μ : ModalityExpr m m') (T : TyExpr m) → ∀ {Γ} →
                           ⟦ reduce-comp-helper μ T ⟧ty {Γ} ≅ᵗʸ ⟦ ⟨ μ ∣ T ⟩ ⟧ty
reduce-comp-helper-sound μ Nat' = ≅ᵗʸ-refl
reduce-comp-helper-sound μ Bool' = ≅ᵗʸ-refl
reduce-comp-helper-sound μ (T ⇛ S) = ≅ᵗʸ-refl
reduce-comp-helper-sound μ (T ⊠ S) = ≅ᵗʸ-refl
reduce-comp-helper-sound μ ⟨ ρ ∣ T ⟩ = eq-mod-closed (ⓜ-interpretation μ ρ) ⟦ T ⟧ty {{⟦⟧ty-natural T}}

reduce-comp-sound : (T : TyExpr m) → ∀ {Γ} → ⟦ reduce-comp T ⟧ty {Γ} ≅ᵗʸ ⟦ T ⟧ty
reduce-comp-sound Nat' = ≅ᵗʸ-refl
reduce-comp-sound Bool' = ≅ᵗʸ-refl
reduce-comp-sound (T ⇛ S) = ⇛-cong (reduce-comp-sound T) (reduce-comp-sound S)
reduce-comp-sound (T ⊠ S) = ⊠-cong (reduce-comp-sound T) (reduce-comp-sound S)
reduce-comp-sound ⟨ μ ∣ T ⟩ = ≅ᵗʸ-trans (reduce-comp-helper-sound μ (reduce-comp T))
                                        (mod-cong ⟦ μ ⟧modality (reduce-comp-sound T))

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

reduce-unit-helper-sound : (μ : ModalityExpr m m') (T : TyExpr m) → ∀ {Γ} →
                           ⟦ reduce-unit-helper μ T ⟧ty {Γ} ≅ᵗʸ ⟦ ⟨ μ ∣ T ⟩ ⟧ty
reduce-unit-helper-sound {m} {m'} μ T with m ≟mode m'
reduce-unit-helper-sound {m} {m'} μ T | type-error _ = ≅ᵗʸ-refl
reduce-unit-helper-sound {m} {m'} μ T | ok refl with ⟦ 𝟙 ⟧≅mod?⟦ μ ⟧
reduce-unit-helper-sound {m} {m'} μ T | ok refl | type-error _ = ≅ᵗʸ-refl
reduce-unit-helper-sound {m} {m'} μ T | ok refl | ok 𝟙=μ = eq-mod-closed (≅ᵐ-trans (≅ᵐ-sym 𝟙-interpretation) 𝟙=μ)
                                                                         ⟦ T ⟧ty {{⟦⟧ty-natural T}}

reduce-unit-sound : (T : TyExpr m) → ∀ {Γ} → ⟦ reduce-unit T ⟧ty {Γ} ≅ᵗʸ ⟦ T ⟧ty
reduce-unit-sound Nat' = ≅ᵗʸ-refl
reduce-unit-sound Bool' = ≅ᵗʸ-refl
reduce-unit-sound (T ⇛ S) = ⇛-cong (reduce-unit-sound T) (reduce-unit-sound S)
reduce-unit-sound (T ⊠ S) = ⊠-cong (reduce-unit-sound T) (reduce-unit-sound S)
reduce-unit-sound ⟨ μ ∣ T ⟩ = ≅ᵗʸ-trans (reduce-unit-helper-sound μ (reduce-unit T))
                                        (mod-cong ⟦ μ ⟧modality (reduce-unit-sound T))

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
