{-# OPTIONS --omega-in-omega #-}

open import Categories

module Reflection.Naturality {C : Category} where

open import Level

open import CwF-Structure.Contexts
open import CwF-Structure.Types

open import Types.Discrete
open import Types.Products

record NullaryTypeOp (ℓ : Level) : Setω where
  field
    ⟦_⟧nop : ∀ {ℓc} {Γ : Ctx C ℓc} → Ty Γ ℓ
    naturality : ∀ {ℓc ℓc'} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} (σ : Δ ⇒ Γ) →
                 ⟦_⟧nop [ σ ] ≅ᵗʸ ⟦_⟧nop

open NullaryTypeOp public

record BinaryTypeOp : Setω where
  field
    ⟦_⟧bop_$_ : ∀ {ℓc ℓt ℓt'} {Γ : Ctx C ℓc} → Ty Γ ℓt → Ty Γ ℓt' → Ty Γ (ℓt ⊔ ℓt')
    naturality : ∀ {ℓc ℓc' ℓt ℓt'} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} (σ : Δ ⇒ Γ) →
                 {T : Ty Γ ℓt} {S : Ty Γ ℓt'} →
                 (⟦_⟧bop_$_ T S) [ σ ] ≅ᵗʸ ⟦_⟧bop_$_ (T [ σ ]) (S [ σ ])

open BinaryTypeOp public

bool-nullary : NullaryTypeOp 0ℓ
bool-nullary = record { ⟦_⟧nop = Bool' ; naturality = Discr-subst _ }

prod-binary : BinaryTypeOp
prod-binary = record { ⟦_⟧bop_$_ = _⊠_ ; naturality = λ σ → ⊠-natural σ }


data Exp : {ℓc : Level} (Γ : Ctx C ℓc) (ℓ : Level) → Setω where
  var : ∀ {ℓc ℓ} {Γ : Ctx C ℓc} →
        Ty Γ ℓ → Exp Γ ℓ
  nul : ∀ {ℓc ℓ} {Γ : Ctx C ℓc} →
        NullaryTypeOp ℓ → Exp Γ ℓ
  bin : ∀ {ℓc ℓt ℓt'} {Γ : Ctx C ℓc} →
        BinaryTypeOp → Exp Γ ℓt → Exp Γ ℓt' → Exp Γ (ℓt ⊔ ℓt')
  sub : ∀ {ℓc ℓc' ℓt} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'}
        (σ : Δ ⇒ Γ) → Exp Γ ℓt → Exp Δ ℓt

⟦_⟧exp : ∀ {ℓc ℓ} {Γ : Ctx C ℓc} → Exp Γ ℓ → Ty Γ ℓ
⟦ var T ⟧exp = T
⟦ nul x ⟧exp = ⟦ x ⟧nop
⟦ bin x e1 e2 ⟧exp = ⟦ x ⟧bop ⟦ e1 ⟧exp $ ⟦ e2 ⟧exp
⟦ sub σ e ⟧exp = ⟦ e ⟧exp [ σ ]
