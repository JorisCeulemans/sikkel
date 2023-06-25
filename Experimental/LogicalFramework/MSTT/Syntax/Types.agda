--------------------------------------------------
-- Definition of MSTT types
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension

module Experimental.LogicalFramework.MSTT.Syntax.Types
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ)
  where

open import Data.List
open import Data.Product
open import Data.Unit

open TyExt 𝒯
open ModeTheory ℳ


private variable
  m n : Mode


infixr 6 ⟨_∣_⟩⇛_
infixl 5 _⊠_

data Ty (m : Mode) : Set
TyExtArgs : List Mode → Set

data Ty m where
  Nat' : Ty m
  Bool' : Ty m
  ⟨_∣_⟩⇛_ : Modality n m → Ty n → Ty m → Ty m
  _⊠_ : Ty m → Ty m → Ty m
  ⟨_∣_⟩ : Modality n m → Ty n → Ty m
  Ext : ∀ {margs} → TyExtCode margs m → TyExtArgs margs → Ty m

TyExtArgs [] = ⊤
TyExtArgs (m ∷ margs) = Ty m × TyExtArgs margs


infixr 6 _⇛_
_⇛_ : Ty m → Ty m → Ty m
T ⇛ S = ⟨ 𝟙 ∣ T ⟩⇛ S

{-# DISPLAY ⟨_∣_⟩⇛_ 𝟙 T S = _⇛_ T S #-}
