--------------------------------------------------
-- Definition of STT types
--------------------------------------------------

module Experimental.LogicalFramework.STT.Syntax.Types where

open import Experimental.LogicalFramework.STT.ModeTheory

private variable
  m n : Mode


infixr 6 _⇛_
infixl 5 _⊠_
data Ty (m : Mode) : Set where
  Nat' : Ty m
  Bool' : Ty m
  _⇛_ : Ty m → Ty m → Ty m
  _⊠_ : Ty m → Ty m → Ty m
  ⟨_∣_⟩ : Modality n m → Ty n → Ty m 
