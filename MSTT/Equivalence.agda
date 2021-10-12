--------------------------------------------------
-- Decision procedure for equivalence of types
--------------------------------------------------

open import MSTT.Parameter.ModeTheory
open import MSTT.Parameter.TypeExtension using (TyExt)

module MSTT.Equivalence (mt : ModeTheory) (ty-ext : TyExt mt) where

open import Data.List hiding (_++_)
open import Data.Product using (_×_; _,_)
open import Data.String
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure
open import Model.Modality as M hiding (⟨_∣_⟩; 𝟙; _ⓜ_)
open import Model.Type.Function as M hiding (_⇛_)
open import Model.Type.Product as M hiding (_⊠_)

open import MSTT.TCMonad
open import MSTT.Syntax.Type mt ty-ext
open import MSTT.InterpretTypes mt ty-ext

open ModeTheory mt
open TyExt ty-ext
open MSTT.Parameter.TypeExtension mt hiding (TyExt)

private
  variable
    m m' : ModeExpr
    margs : List ModeExpr


-- The idea is to reduce a type expression to a canonical equivalent one in two steps.
-- 1. Reduce all occurrences of ⟨ μ ∣ ⟨ ρ ∣ T ⟩ ⟩ to ⟨ μ ⓜ ρ ∣ T ⟩. The resulting type
--    will not have a subexpression consisting of a double modality application.
-- 2. Reduce all occurrences of ⟨ μ ∣ T ⟩ for which μ ≃ 𝟙 to T.
-- Two types that are literally equal (up to equivalence of modalities determined by
-- the mode theory) after this reduction are considered equivalent by the decision
-- procedure _≃ᵗʸ?_.

--------------------------------------------------
-- Reduction step 1, implemented by reduce-comp

reduce-comp-helper : ModalityExpr m m' → TyExpr m → TyExpr m'
reduce-comp-helper μ Nat' = ⟨ μ ∣ Nat' ⟩
reduce-comp-helper μ Bool' = ⟨ μ ∣ Bool' ⟩
reduce-comp-helper μ (T ⇛ S) = ⟨ μ ∣ T ⇛ S ⟩
reduce-comp-helper μ (T ⊠ S) = ⟨ μ ∣ T ⊠ S ⟩
reduce-comp-helper μ ⟨ ρ ∣ T ⟩ = ⟨ μ ⓜ ρ ∣ T ⟩
reduce-comp-helper μ (Ext c args) = ⟨ μ ∣ Ext c args ⟩

reduce-comp : TyExpr m → TyExpr m
reduce-comp-ext-args : TyExtArgs margs → TyExtArgs margs

reduce-comp Nat' = Nat'
reduce-comp Bool' = Bool'
reduce-comp (T ⇛ S) = reduce-comp T ⇛ reduce-comp S
reduce-comp (T ⊠ S) = reduce-comp T ⊠ reduce-comp S
reduce-comp ⟨ μ ∣ T ⟩ = reduce-comp-helper μ (reduce-comp T)
reduce-comp (Ext c args) = Ext c (reduce-comp-ext-args args)

reduce-comp-ext-args {[]}        args       = args
reduce-comp-ext-args {m ∷ margs} (T , args) = reduce-comp T , reduce-comp-ext-args args

reduce-comp-helper-sound : (μ : ModalityExpr m m') (T : TyExpr m) → ∀ {Γ} →
                           ⟦ reduce-comp-helper μ T ⟧ty {Γ} ≅ᵗʸ ⟦ ⟨ μ ∣ T ⟩ ⟧ty
reduce-comp-helper-sound μ Nat' = ≅ᵗʸ-refl
reduce-comp-helper-sound μ Bool' = ≅ᵗʸ-refl
reduce-comp-helper-sound μ (T ⇛ S) = ≅ᵗʸ-refl
reduce-comp-helper-sound μ (T ⊠ S) = ≅ᵗʸ-refl
reduce-comp-helper-sound μ ⟨ ρ ∣ T ⟩ = eq-mod-closed (ⓜ-interpretation μ ρ) ⟦ T ⟧ty {{⟦⟧ty-natural T}}
reduce-comp-helper-sound μ (Ext c args) = ≅ᵗʸ-refl

reduce-comp-sound : (T : TyExpr m) → ∀ {Γ} → ⟦ reduce-comp T ⟧ty {Γ} ≅ᵗʸ ⟦ T ⟧ty
reduce-comp-sound-ext-args : {F G : TyConstructor margs m} → TyConstructorEquiv F G → (args : TyExtArgs margs) →
                             ∀ {Γ} → interpret-ext-ty F (reduce-comp-ext-args args) {Γ} ≅ᵗʸ interpret-ext-ty G args

reduce-comp-sound Nat' = ≅ᵗʸ-refl
reduce-comp-sound Bool' = ≅ᵗʸ-refl
reduce-comp-sound (T ⇛ S) = ⇛-cong (reduce-comp-sound T) (reduce-comp-sound S)
reduce-comp-sound (T ⊠ S) = ⊠-cong (reduce-comp-sound T) (reduce-comp-sound S)
reduce-comp-sound ⟨ μ ∣ T ⟩ = ≅ᵗʸ-trans (reduce-comp-helper-sound μ (reduce-comp T))
                                        (mod-cong ⟦ μ ⟧modality (reduce-comp-sound T))
reduce-comp-sound (Ext c args) = reduce-comp-sound-ext-args (interpret-code-cong c) args

reduce-comp-sound-ext-args {[]}        is-equiv args       = is-equiv
reduce-comp-sound-ext-args {m ∷ margs} is-equiv (T , args) = reduce-comp-sound-ext-args (is-equiv (reduce-comp-sound T)) args


--------------------------------------------------
-- Reduction step 2, implemented by reduce-unit

reduce-unit-helper : ModalityExpr m m' → TyExpr m → TyExpr m'
reduce-unit-helper {m} {m'} μ T with m ≟mode m'
reduce-unit-helper {m} {m'} μ T | type-error _ = ⟨ μ ∣ T ⟩
reduce-unit-helper {m} {m'} μ T | ok refl with 𝟙 ≃ᵐ? μ
reduce-unit-helper {m} {m'} μ T | ok refl | type-error _ = ⟨ μ ∣ T ⟩
reduce-unit-helper {m} {m'} μ T | ok refl | ok _ = T

reduce-unit : TyExpr m → TyExpr m
reduce-unit-ext-args : TyExtArgs margs → TyExtArgs margs

reduce-unit Nat' = Nat'
reduce-unit Bool' = Bool'
reduce-unit (T ⇛ S) = reduce-unit T ⇛ reduce-unit S
reduce-unit (T ⊠ S) = reduce-unit T ⊠ reduce-unit S
reduce-unit ⟨ μ ∣ T ⟩ = reduce-unit-helper μ (reduce-unit T)
reduce-unit (Ext c args) = Ext c (reduce-unit-ext-args args)

reduce-unit-ext-args {[]}        args       = args
reduce-unit-ext-args {m ∷ margs} (T , args) = reduce-unit T , reduce-unit-ext-args args

reduce-unit-helper-sound : (μ : ModalityExpr m m') (T : TyExpr m) → ∀ {Γ} →
                           ⟦ reduce-unit-helper μ T ⟧ty {Γ} ≅ᵗʸ ⟦ ⟨ μ ∣ T ⟩ ⟧ty
reduce-unit-helper-sound {m} {m'} μ T with m ≟mode m'
reduce-unit-helper-sound {m} {m'} μ T | type-error _ = ≅ᵗʸ-refl
reduce-unit-helper-sound {m} {m'} μ T | ok refl with 𝟙 ≃ᵐ? μ
reduce-unit-helper-sound {m} {m'} μ T | ok refl | type-error _ = ≅ᵗʸ-refl
reduce-unit-helper-sound {m} {m'} μ T | ok refl | ok 𝟙=μ = eq-mod-closed (≅ᵐ-trans (≅ᵐ-sym 𝟙-interpretation) 𝟙=μ)
                                                                         ⟦ T ⟧ty {{⟦⟧ty-natural T}}

reduce-unit-sound : (T : TyExpr m) → ∀ {Γ} → ⟦ reduce-unit T ⟧ty {Γ} ≅ᵗʸ ⟦ T ⟧ty
reduce-unit-sound-ext-args : {F G : TyConstructor margs m} → TyConstructorEquiv F G → (args : TyExtArgs margs) →
                             ∀ {Γ} → interpret-ext-ty F (reduce-unit-ext-args args) {Γ} ≅ᵗʸ interpret-ext-ty G args

reduce-unit-sound Nat' = ≅ᵗʸ-refl
reduce-unit-sound Bool' = ≅ᵗʸ-refl
reduce-unit-sound (T ⇛ S) = ⇛-cong (reduce-unit-sound T) (reduce-unit-sound S)
reduce-unit-sound (T ⊠ S) = ⊠-cong (reduce-unit-sound T) (reduce-unit-sound S)
reduce-unit-sound ⟨ μ ∣ T ⟩ = ≅ᵗʸ-trans (reduce-unit-helper-sound μ (reduce-unit T))
                                        (mod-cong ⟦ μ ⟧modality (reduce-unit-sound T))
reduce-unit-sound (Ext c args) = reduce-unit-sound-ext-args (interpret-code-cong c) args

reduce-unit-sound-ext-args {[]}        is-equiv args       = is-equiv
reduce-unit-sound-ext-args {m ∷ margs} is-equiv (T , args) = reduce-unit-sound-ext-args (is-equiv (reduce-unit-sound T)) args


--------------------------------------------------
-- The full reduction function

reduce-ty : TyExpr m → TyExpr m
reduce-ty = reduce-unit ∘ reduce-comp

reduce-ty-sound : (T : TyExpr m) → ∀ {Γ} → ⟦ reduce-ty T ⟧ty {Γ} ≅ᵗʸ ⟦ T ⟧ty
reduce-ty-sound T = ≅ᵗʸ-trans (reduce-unit-sound (reduce-comp T))
                              (reduce-comp-sound T)


--------------------------------------------------
-- The final decision procedure for type equivalence

_≟list-mode_ : (ms1 ms2 : List ModeExpr) → TCM (ms1 ≡ ms2)
[] ≟list-mode [] = return refl
[] ≟list-mode (_ ∷ _) = type-error ""
(_ ∷ _) ≟list-mode [] = type-error ""
(m1 ∷ ms1) ≟list-mode (m2 ∷ ms2) = do
  refl ← m1 ≟mode m2
  refl ← ms1 ≟list-mode ms2
  return refl

-- Are two types identical up to equivalence of modalities?
_≟ty_ : (T S : TyExpr m) → TCM (∀ {Γ} → ⟦ T ⟧ty {Γ} ≅ᵗʸ ⟦ S ⟧ty)
≟ty-ext-args : {F G : TyConstructor margs m} → TyConstructorEquiv F G → (args1 args2 : TyExtArgs margs) →
               TCM (∀ {Γ} → interpret-ext-ty F args1 {Γ} ≅ᵗʸ interpret-ext-ty G args2)

Nat' ≟ty Nat' = return ≅ᵗʸ-refl
Bool' ≟ty Bool' = return ≅ᵗʸ-refl
(T1 ⇛ S1) ≟ty (T2 ⇛ S2) = do
  T1=T2 ← T1 ≟ty T2
  S1=S2 ← S1 ≟ty S2
  return (⇛-cong T1=T2 S1=S2)
(T1 ⊠ S1) ≟ty (T2 ⊠ S2) = do
  T1=T2 ← T1 ≟ty T2
  S1=S2 ← S1 ≟ty S2
  return (⊠-cong T1=T2 S1=S2)
(⟨_∣_⟩ {mT} μ T) ≟ty (⟨_∣_⟩ {mS} ρ S) = do
  refl ← mT ≟mode mS
  μ=ρ ← μ ≃ᵐ? ρ
  T=S ← T ≟ty S
  return (≅ᵗʸ-trans (eq-mod-closed μ=ρ ⟦ T ⟧ty {{⟦⟧ty-natural T}})
                    (mod-cong ⟦ ρ ⟧modality T=S))
(Ext {margs1} c1 args1) ≟ty (Ext {margs2} c2 args2) = do
  refl ← margs1 ≟list-mode margs2
  refl ← c1 ≟code c2
  ≟ty-ext-args (interpret-code-cong c1) args1 args2
T ≟ty S = type-error ("Type " ++ show-type T ++ " is not equal to " ++ show-type S)

≟ty-ext-args {[]}        is-equiv args1 args2 = return is-equiv
≟ty-ext-args {m ∷ margs} is-equiv (T1 , args1) (T2 , args2) = do
  T1=T2 ← T1 ≟ty T2
  ≟ty-ext-args (is-equiv T1=T2) args1 args2


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
    (T' ≟ty S') >>= λ T'=S' → return (ty-reflect T S T'=S'))

-- The final decision procedure. Note that we first check whether two types
-- are identical and only compare their reductions if they are not.
-- The reason is that the former condition generates smaller equivalence
-- proofs for the interpretations as presheaves.
_≃ᵗʸ?_ : (T S : TyExpr m) → TCM (∀ {Γ} → ⟦ T ⟧ty {Γ} ≅ᵗʸ ⟦ S ⟧ty)
T ≃ᵗʸ? S = (T ≟ty S) <∣> reduce-compare-ty T S
