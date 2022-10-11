--------------------------------------------------
-- Definition of MSTT types
--------------------------------------------------

module Experimental.LogicalFramework.MSTT.Syntax.Types where

open import Experimental.LogicalFramework.MSTT.ModeTheory

private variable
  m n : Mode


infixr 6 _⇛_
infixl 5 _⊠_
data Ty : Mode → Set where
  Nat' : Ty m
  Bool' : Ty m
  _⇛_ : Ty m → Ty m → Ty m
  _⊠_ : Ty m → Ty m → Ty m
  ⟨_∣_⟩ : Modality n m → Ty n → Ty m 
  GStream : Ty ★ → Ty ω
