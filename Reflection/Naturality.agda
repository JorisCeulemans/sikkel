{-# OPTIONS --omega-in-omega #-}

open import Categories

module Reflection.Naturality {C : Category} where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import Reflection.Helpers


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
    congruence : ∀ {ℓc ℓt ℓt' ℓs ℓs'} {Γ : Ctx C ℓc}
                 {T : Ty Γ ℓt} {T' : Ty Γ ℓt'} {S : Ty Γ ℓs} {S' : Ty Γ ℓs'} →
                 T ≅ᵗʸ T' → S ≅ᵗʸ S' → ⟦_⟧bop_$_ T S ≅ᵗʸ ⟦_⟧bop_$_ T' S'

open BinaryTypeOp public


data ExpSkeleton : Set where
  svar : ExpSkeleton
  snul : ExpSkeleton
  sbin : ExpSkeleton → ExpSkeleton → ExpSkeleton
  ssub : ExpSkeleton → ExpSkeleton

data Exp : {ℓc : Level} (Γ : Ctx C ℓc) (ℓ : Level) {_ : ExpSkeleton} → Setω where
  var : ∀ {ℓc ℓ} {Γ : Ctx C ℓc} →
        (T : Ty Γ ℓ) → Exp Γ ℓ {svar}
  nul : ∀ {ℓc ℓ} {Γ : Ctx C ℓc} →
        NullaryTypeOp ℓ → Exp Γ ℓ {snul}
  bin : ∀ {ℓc ℓt ℓt' s s'} {Γ : Ctx C ℓc} →
        BinaryTypeOp → (e1 : Exp Γ ℓt {s}) (e2 : Exp Γ ℓt' {s'}) → Exp Γ (ℓt ⊔ ℓt') {sbin s s'}
  sub : ∀ {ℓc ℓc' ℓt s} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} →
        Exp Γ ℓt {s} → (σ : Δ ⇒ Γ) → Exp Δ ℓt {ssub s}

⟦_⟧exp : ∀ {ℓc ℓ s} {Γ : Ctx C ℓc} → Exp Γ ℓ {s} → Ty Γ ℓ
⟦ var T ⟧exp = T
⟦ nul x ⟧exp = ⟦ x ⟧nop
⟦ bin x e1 e2 ⟧exp = ⟦ x ⟧bop ⟦ e1 ⟧exp $ ⟦ e2 ⟧exp
⟦ sub e σ ⟧exp = ⟦ e ⟧exp [ σ ]

reduce-skeleton : ExpSkeleton → ExpSkeleton
reduce-skeleton svar = svar
reduce-skeleton snul = snul
reduce-skeleton (sbin s1 s2) = sbin (reduce-skeleton s1) (reduce-skeleton s2)
reduce-skeleton (ssub svar) = ssub svar
reduce-skeleton (ssub snul) = snul
reduce-skeleton (ssub (sbin s1 s2)) = sbin (reduce-skeleton (ssub s1)) (reduce-skeleton (ssub s2))
reduce-skeleton (ssub (ssub s)) = reduce-skeleton (ssub s)

reduce : ∀ {ℓc ℓ s} {Γ : Ctx C ℓc} → Exp Γ ℓ {s} → Exp Γ ℓ {reduce-skeleton s}
reduce (var T) = var T
reduce (nul x) = nul x
reduce (bin x e1 e2) = bin x (reduce e1) (reduce e2)
reduce (sub (var T) σ) = sub (var T) σ
reduce (sub (nul x) σ) = nul x
reduce (sub (bin x e1 e2) σ) = bin x (reduce (sub e1 σ)) (reduce (sub e2 σ))
reduce (sub (sub e τ) σ) = reduce (sub e (τ ⊚ σ))

reduce-sound : ∀ {ℓc ℓ s} {Γ : Ctx C ℓc} (e : Exp Γ ℓ {s}) →
               ⟦ e ⟧exp ≅ᵗʸ ⟦ reduce e ⟧exp
reduce-sound (var T) = ≅ᵗʸ-refl
reduce-sound (nul x) = ≅ᵗʸ-refl
reduce-sound (bin x e1 e2) = congruence x (reduce-sound e1) (reduce-sound e2)
reduce-sound (sub (var T) σ) = ≅ᵗʸ-refl
reduce-sound (sub (nul x) σ) = naturality x σ
reduce-sound (sub (bin x e1 e2) σ) =
  begin
    (⟦ x ⟧bop ⟦ e1 ⟧exp $ ⟦ e2 ⟧exp) [ σ ]
  ≅⟨ naturality x σ ⟩
    ⟦ x ⟧bop (⟦ e1 ⟧exp [ σ ]) $ (⟦ e2 ⟧exp [ σ ])
  ≅⟨⟩
    ⟦ x ⟧bop ⟦ sub e1 σ ⟧exp $ ⟦ sub e2 σ ⟧exp
  ≅⟨ congruence x (reduce-sound (sub e1 σ)) (reduce-sound (sub e2 σ)) ⟩
    ⟦ x ⟧bop ⟦ reduce (sub e1 σ) ⟧exp $ ⟦ reduce (sub e2 σ) ⟧exp ∎
  where open ≅ᵗʸ-Reasoning
reduce-sound (sub (sub e τ) σ) =
  begin
    (⟦ e ⟧exp [ τ ]) [ σ ]
  ≅⟨ ty-subst-comp ⟦ e ⟧exp τ σ ⟩
    ⟦ e ⟧exp [ τ ⊚ σ ]
  ≅⟨⟩
    ⟦ sub e (τ ⊚ σ) ⟧exp
  ≅⟨ reduce-sound (sub e (τ ⊚ σ)) ⟩
    ⟦ reduce (sub e (τ ⊚ σ)) ⟧exp ∎
  where open ≅ᵗʸ-Reasoning

⟦⟧exp-cong : ∀ {ℓc ℓ s s'} {Γ : Ctx C ℓc} →
             {e : Exp Γ ℓ {s}} {e' : Exp Γ ℓ {s'}} →
             (p : s ≡ s') →
             ω-transp (λ z → Exp Γ ℓ {z}) p e ≡ω e' →
             ⟦ e ⟧exp ≅ᵗʸ ⟦ e' ⟧exp
⟦⟧exp-cong refl refl = ≅ᵗʸ-refl

type-naturality-reflect : ∀ {ℓc ℓ s s'} {Γ : Ctx C ℓc} →
                          (e : Exp Γ ℓ {s}) (e' : Exp Γ ℓ {s'}) →
                          (p : reduce-skeleton s ≡ reduce-skeleton s') →
                          ω-transp (λ z → Exp Γ ℓ {z}) p (reduce e) ≡ω reduce e' →
                          ⟦ e ⟧exp ≅ᵗʸ ⟦ e' ⟧exp
type-naturality-reflect e e' p q =
  begin
    ⟦ e ⟧exp
  ≅⟨ reduce-sound e ⟩
    ⟦ reduce e ⟧exp
  ≅⟨ ⟦⟧exp-cong p q ⟩
    ⟦ reduce e' ⟧exp
  ≅˘⟨ reduce-sound e' ⟩
    ⟦ e' ⟧exp ∎
  where open ≅ᵗʸ-Reasoning

private
  open import Types.Discrete
  open import Types.Products

  bool-nullary : NullaryTypeOp 0ℓ
  bool-nullary = record { ⟦_⟧nop = Bool' ; naturality = Discr-subst _ }

  prod-binary : BinaryTypeOp
  prod-binary = record { ⟦_⟧bop_$_ = _⊠_ ; naturality = λ σ → ⊠-natural σ ; congruence = ⊠-cong }

  example : ∀ {ℓ ℓ' ℓ''} {Δ : Ctx C ℓ} {Γ : Ctx C ℓ'} {Θ : Ctx C ℓ''} →
            (σ : Δ ⇒ Γ) (τ : Γ ⇒ Θ) →
            (Bool' ⊠ (Bool' [ τ ])) [ σ ] ≅ᵗʸ (Bool' [ σ ]) ⊠ Bool'
  example σ τ = type-naturality-reflect (sub (bin prod-binary (nul bool-nullary) (sub (nul bool-nullary) τ)) σ)
                                        (bin prod-binary (sub (nul bool-nullary) σ) (nul bool-nullary))
                                        refl
                                        refl

{-
-- Failed attempt to define reduce using sized types
data Exp : {ℓc : Level} (Γ : Ctx C ℓc) (ℓ : Level) {_ : Size} → Setω where
  var : ∀ {ℓc ℓ i} {Γ : Ctx C ℓc} →
        Ty Γ ℓ → Exp Γ ℓ {↑ i}
  nul : ∀ {ℓc ℓ i} {Γ : Ctx C ℓc} →
        NullaryTypeOp ℓ → Exp Γ ℓ {↑ i}
  bin : ∀ {ℓc ℓt ℓt' i} {Γ : Ctx C ℓc} →
        BinaryTypeOp → Exp Γ ℓt {i} → Exp Γ ℓt' {i} → Exp Γ (ℓt ⊔ ℓt') {↑ i}
  sub : ∀ {ℓc ℓc' ℓt i} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} →
        Exp Γ ℓt {i} → (σ : Δ ⇒ Γ) → Exp Δ ℓt {↑ i}

⟦_⟧exp : ∀ {ℓc ℓ i} {Γ : Ctx C ℓc} → Exp Γ ℓ {i} → Ty Γ ℓ
⟦ var T ⟧exp = T
⟦ nul x ⟧exp = ⟦ x ⟧nop
⟦ bin x e1 e2 ⟧exp = ⟦ x ⟧bop ⟦ e1 ⟧exp $ ⟦ e2 ⟧exp
⟦ sub e σ ⟧exp = ⟦ e ⟧exp [ σ ]

reduce : ∀ {ℓc ℓ i} {Γ : Ctx C ℓc} → Exp Γ ℓ {i} → Exp Γ ℓ {i}
reduce (var T) = var T
reduce (nul x) = nul x
reduce (bin x e1 e2) = bin x (reduce e1) (reduce e2)
reduce (sub (var T) σ) = sub (var T) σ
reduce (sub (nul x) σ) = nul x
reduce (sub (bin x e1 e2) σ) = bin x (reduce (sub e1 σ)) (reduce (sub e2 σ))
reduce .{i = ↑ (↑ _)} (sub (sub e τ) σ) = reduce {i = ↑ _} (sub {!e!} (τ ⊚ σ))
-}
