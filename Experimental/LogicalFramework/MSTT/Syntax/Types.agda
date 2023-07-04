--------------------------------------------------
-- Definition of MSTT types
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension

module Experimental.LogicalFramework.MSTT.Syntax.Types
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ)
  where

open import Data.List hiding (_++_)
open import Data.Product
open import Data.String
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.Proof.CheckingMonad

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


_=list-mode?_ : (ms ns : List Mode) → PCM (ms ≡ ns)
[]       =list-mode? []       = return refl
[]       =list-mode? (n ∷ ns) = throw-error ""
(m ∷ ms) =list-mode? []       = throw-error ""
(m ∷ ms) =list-mode? (n ∷ ns) = do
  refl ← m ≟mode n
  refl ← ms =list-mode? ns
  return refl


show-ty : Ty m → String
show-ext : ∀ {margs} → TyExtShow ℳ margs → TyExtArgs margs → String

show-ty Nat' = "ℕ"
show-ty Bool' = "Bool"
show-ty (⟨ μ ∣ T ⟩⇛ S) = "⟨ _ ∣ " ++ show-ty T ++ " ⟩→ " ++ show-ty S
show-ty (T ⊠ S) = show-ty T ++ " × " ++ show-ty S
show-ty ⟨ μ ∣ T ⟩ = "⟨ _ ∣ " ++ show-ty T ++ " ⟩"
show-ty (Ext c Args) = show-ext (show-ty-code c) Args

show-ext {[]}        s Args       = s
show-ext {m ∷ margs} f (A , Args) = show-ext (f (show-ty A)) Args


_≟ty_ : (T S : Ty m) → PCM (T ≡ S)
_=Args?_ : ∀ {margs} → (Args1 Args2 : TyExtArgs margs) → PCM (Args1 ≡ Args2)

Nat' ≟ty Nat' = return refl
Bool' ≟ty Bool' = return refl
(⟨ μ ∣ T1 ⟩⇛ T2) ≟ty (⟨ ρ ∣ S1 ⟩⇛ S2) = do
  refl ← mod-dom μ ≟mode mod-dom ρ
  refl ← μ ≟mod ρ
  refl ← T1 ≟ty S1
  refl ← T2 ≟ty S2
  return refl
(T1 ⊠ T2) ≟ty (S1 ⊠ S2) =  do
  refl ← T1 ≟ty S1
  refl ← T2 ≟ty S2
  return refl
⟨_∣_⟩ {n = n} μ T ≟ty ⟨_∣_⟩ {n = n'} κ S = do
  refl ← n ≟mode n'
  refl ← μ ≟mod κ
  refl ← T ≟ty S
  return refl
(Ext {margs1} c1 Args1) ≟ty (Ext {margs2} c2 Args2) = do
  refl ← margs1 =list-mode? margs2
  refl ← c1 ≟ty-code c2
  refl ← Args1 =Args? Args2
  return refl
T ≟ty S = throw-error ("Types are not equal: " ++ show-ty T ++ " != " ++ show-ty S)

_=Args?_ {[]}        Args1        Args2        = return refl
_=Args?_ {m ∷ margs} (A1 , Args1) (A2 , Args2) = do
  refl ← A1 ≟ty A2
  refl ← Args1 =Args? Args2
  return refl
