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
open import Model.Modality as M hiding (⟨_∣_⟩; 𝟙)
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


_≟list-mode_ : (ms1 ms2 : List ModeExpr) → TCM (ms1 ≡ ms2)
[]         ≟list-mode []         = return refl
[]         ≟list-mode (_ ∷ _)    = type-error ""
(_ ∷ _)    ≟list-mode []         = type-error ""
(m1 ∷ ms1) ≟list-mode (m2 ∷ ms2) = do
  refl ← m1 ≟mode m2
  refl ← ms1 ≟list-mode ms2
  return refl

-- The equivalence relation on types is the smallest congruence on types that
-- respects equivalence of modalities (expressed by ≃ᵐ? in the mode theory).
_≃ᵗʸ?_ : (T S : TyExpr m) → TCM (∀ {Γ} → ⟦ T ⟧ty {Γ} ≅ᵗʸ ⟦ S ⟧ty)
≃ᵗʸ?-ext-args : {F G : TyConstructor margs m} → TyConstructorEquiv F G → (args1 args2 : TyExtArgs margs) →
               TCM (∀ {Γ} → interpret-ext-ty F args1 {Γ} ≅ᵗʸ interpret-ext-ty G args2)

Nat' ≃ᵗʸ? Nat' = return reflᵗʸ
Bool' ≃ᵗʸ? Bool' = return reflᵗʸ
(T1 ⇛ S1) ≃ᵗʸ? (T2 ⇛ S2) = do
  T1=T2 ← T1 ≃ᵗʸ? T2
  S1=S2 ← S1 ≃ᵗʸ? S2
  return (⇛-cong T1=T2 S1=S2)
(T1 ⊠ S1) ≃ᵗʸ? (T2 ⊠ S2) = do
  T1=T2 ← T1 ≃ᵗʸ? T2
  S1=S2 ← S1 ≃ᵗʸ? S2
  return (⊠-cong T1=T2 S1=S2)
(⟨_∣_⟩ {mT} μ T) ≃ᵗʸ? (⟨_∣_⟩ {mS} ρ S) = do
  refl ← mT ≟mode mS
  μ=ρ ← μ ≃ᵐ? ρ
  T=S ← T ≃ᵗʸ? S
  return (transᵗʸ (eq-dra-closed μ=ρ (⟦⟧ty-natural T))
                  (dra-cong ⟦ ρ ⟧modality T=S))
(Ext {margs1} c1 args1) ≃ᵗʸ? (Ext {margs2} c2 args2) = do
  refl ← margs1 ≟list-mode margs2
  refl ← c1 ≟code c2
  ≃ᵗʸ?-ext-args (interpret-code-cong c1) args1 args2
T ≃ᵗʸ? S = type-error ("Type " ++ show-type T ++ " is not equal to " ++ show-type S)

≃ᵗʸ?-ext-args {[]}        is-equiv args1 args2 = return is-equiv
≃ᵗʸ?-ext-args {m ∷ margs} is-equiv (T1 , args1) (T2 , args2) = do
  T1=T2 ← T1 ≃ᵗʸ? T2
  ≃ᵗʸ?-ext-args (is-equiv T1=T2) args1 args2
