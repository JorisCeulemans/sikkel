--------------------------------------------------
-- Definition of MSTT types
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory

module Experimental.LogicalFramework.MSTT.Syntax.Types (ℳ : ModeTheory) where

open ModeTheory ℳ

private variable
  m n : Mode


infixr 6 ⟨_∣_⟩⇛_
infixl 5 _⊠_
data Ty (m : Mode) : Set where
  Nat' : Ty m
  Bool' : Ty m
  ⟨_∣_⟩⇛_ : Modality n m → Ty n → Ty m → Ty m
  _⊠_ : Ty m → Ty m → Ty m
  ⟨_∣_⟩ : Modality n m → Ty n → Ty m

infixr 6 _⇛_
_⇛_ : Ty m → Ty m → Ty m
T ⇛ S = ⟨ 𝟙 ∣ T ⟩⇛ S

{-# DISPLAY ⟨_∣_⟩⇛_ 𝟙 T S = _⇛_ T S #-}
