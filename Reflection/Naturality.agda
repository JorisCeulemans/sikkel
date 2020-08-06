{-# OPTIONS --omega-in-omega #-}

open import Categories

module Reflection.Naturality {C : Category} where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import Reflection.Helpers public


-- TODO:
--  *) Provide also unary type operations (first step towards support for ▻ modality).
--  *) Make unay + binary operations more general in the type level (to support for instance _⇛_).
--  *) Allow operations that can change the context the type lives in using a certain endofunctor
--     on the category of contexts (needed for ▻). Later, more general functors might as well be interesting.

record NullaryTypeOp (ℓ : Level) : Setω where
  field
    ⟦_⟧nop : ∀ {ℓc} {Γ : Ctx C ℓc} → Ty Γ ℓ
    naturality : ∀ {ℓc ℓc'} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} (σ : Δ ⇒ Γ) →
                 ⟦_⟧nop [ σ ] ≅ᵗʸ ⟦_⟧nop

open NullaryTypeOp public

record UnaryTypeOp (f : Level → Level → Level) : Setω where
  field
    ⟦_⟧uop_ : ∀ {ℓc ℓt} {Γ : Ctx C ℓc} → Ty Γ ℓt → Ty Γ (f ℓc ℓt)
    naturality : ∀ {ℓc ℓc' ℓt} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} (σ : Δ ⇒ Γ) {T : Ty Γ ℓt} →
                 (⟦_⟧uop_ T) [ σ ] ≅ᵗʸ ⟦_⟧uop_ (T [ σ ])
    congruence : ∀ {ℓc ℓt ℓt'} {Γ : Ctx C ℓc}
                 {T : Ty Γ ℓt} {T' : Ty Γ ℓt'} →
                 T ≅ᵗʸ T' → ⟦_⟧uop_ T ≅ᵗʸ ⟦_⟧uop_ T'

open UnaryTypeOp public

record BinaryTypeOp (f : Level → Level → Level → Level) : Setω where
  field
    ⟦_⟧bop_$_ : ∀ {ℓc ℓt ℓt'} {Γ : Ctx C ℓc} → Ty Γ ℓt → Ty Γ ℓt' → Ty Γ (f ℓc ℓt ℓt')
    naturality : ∀ {ℓc ℓc' ℓt ℓt'} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} (σ : Δ ⇒ Γ) →
                 {T : Ty Γ ℓt} {S : Ty Γ ℓt'} →
                 (⟦_⟧bop_$_ T S) [ σ ] ≅ᵗʸ ⟦_⟧bop_$_ (T [ σ ]) (S [ σ ])
    congruence : ∀ {ℓc ℓt ℓt' ℓs ℓs'} {Γ : Ctx C ℓc}
                 {T : Ty Γ ℓt} {T' : Ty Γ ℓt'} {S : Ty Γ ℓs} {S' : Ty Γ ℓs'} →
                 T ≅ᵗʸ T' → S ≅ᵗʸ S' → ⟦_⟧bop_$_ T S ≅ᵗʸ ⟦_⟧bop_$_ T' S'

open BinaryTypeOp public


data ExpSkeleton : Set where
  svar : Level → ExpSkeleton
  snul : Level → ExpSkeleton
  sun  : (f : Level → Level → Level) (ℓc : Level) →
         ExpSkeleton → ExpSkeleton
  sbin : (f : Level → Level → Level → Level) (ℓc : Level) →
         ExpSkeleton → ExpSkeleton → ExpSkeleton
  ssub : (ℓc : Level) → ExpSkeleton → ExpSkeleton

level : ExpSkeleton → Level
level (svar ℓ) = ℓ
level (snul ℓ) = ℓ
level (sun f ℓc s) = f ℓc (level s)
level (sbin f ℓc s1 s2) = f ℓc (level s1) (level s2)
level (ssub ℓc s) = level s

data Exp : {ℓc : Level} (Γ : Ctx C ℓc) → ExpSkeleton → Setω where
  var : ∀ {ℓc ℓ} {Γ : Ctx C ℓc} →
        (T : Ty Γ ℓ) → Exp Γ (svar ℓ)
  nul : ∀ {ℓc ℓ} {Γ : Ctx C ℓc} →
        NullaryTypeOp ℓ → Exp Γ (snul ℓ)
  un  : ∀ {ℓc f s} {Γ : Ctx C ℓc} →
        UnaryTypeOp f → (e : Exp Γ s) → Exp Γ (sun f ℓc s)
  bin : ∀ {ℓc f s s'} {Γ : Ctx C ℓc} →
        BinaryTypeOp f → (e1 : Exp Γ s) (e2 : Exp Γ s') → Exp Γ (sbin f ℓc s s')
  sub : ∀ {ℓc ℓc' s} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} →
        Exp Γ s → (σ : Δ ⇒ Γ) → Exp Δ (ssub ℓc s)

⟦_⟧exp : ∀ {ℓc s} {Γ : Ctx C ℓc} → Exp Γ s → Ty Γ (level s)
⟦ var T ⟧exp = T
⟦ nul x ⟧exp = ⟦ x ⟧nop
⟦ un x e ⟧exp = ⟦ x ⟧uop ⟦ e ⟧exp
⟦ bin x e1 e2 ⟧exp = ⟦ x ⟧bop ⟦ e1 ⟧exp $ ⟦ e2 ⟧exp
⟦ sub e σ ⟧exp = ⟦ e ⟧exp [ σ ]

reduce-skeleton : ExpSkeleton → ExpSkeleton
reduce-skeleton (svar ℓ) = svar ℓ
reduce-skeleton (snul ℓ) = snul ℓ
reduce-skeleton (sun f ℓc s) = sun f ℓc (reduce-skeleton s)
reduce-skeleton (sbin f ℓc s1 s2) = sbin f ℓc (reduce-skeleton s1) (reduce-skeleton s2)
reduce-skeleton (ssub ℓc (svar ℓ)) = ssub ℓc (svar ℓ)
reduce-skeleton (ssub ℓc (snul ℓ)) = snul ℓ
reduce-skeleton (ssub ℓc (sun f ℓc' s)) = sun f ℓc (reduce-skeleton (ssub ℓc s))
reduce-skeleton (ssub ℓc (sbin f ℓc' s1 s2)) = sbin f ℓc (reduce-skeleton (ssub ℓc s1)) (reduce-skeleton (ssub ℓc s2))
reduce-skeleton (ssub ℓc (ssub ℓc' s)) = reduce-skeleton (ssub ℓc s)

reduce : ∀ {ℓc s} {Γ : Ctx C ℓc} → Exp Γ s → Exp Γ (reduce-skeleton s)
reduce (var T) = var T
reduce (nul x) = nul x
reduce (un x e) = un x (reduce e)
reduce (bin x e1 e2) = bin x (reduce e1) (reduce e2)
reduce (sub (var T) σ) = sub (var T) σ
reduce (sub (nul x) σ) = nul x
reduce (sub (un x e) σ) = un x (reduce (sub e σ))
reduce (sub (bin x e1 e2) σ) = bin x (reduce (sub e1 σ)) (reduce (sub e2 σ))
reduce (sub (sub e τ) σ) = reduce (sub e (τ ⊚ σ))

reduce-sound : ∀ {ℓc s} {Γ : Ctx C ℓc} (e : Exp Γ s) →
               ⟦ e ⟧exp ≅ᵗʸ ⟦ reduce e ⟧exp
reduce-sound (var T) = ≅ᵗʸ-refl
reduce-sound (nul x) = ≅ᵗʸ-refl
reduce-sound (un x e) = congruence x (reduce-sound e)
reduce-sound (bin x e1 e2) = congruence x (reduce-sound e1) (reduce-sound e2)
reduce-sound (sub (var T) σ) = ≅ᵗʸ-refl
reduce-sound (sub (nul x) σ) = naturality x σ
reduce-sound (sub (un x e) σ) =
  begin
    (⟦ x ⟧uop ⟦ e ⟧exp) [ σ ]
  ≅⟨ naturality x σ ⟩
    ⟦ x ⟧uop (⟦ e ⟧exp [ σ ])
  ≅⟨⟩
    ⟦ x ⟧uop ⟦ sub e σ ⟧exp
  ≅⟨ congruence x (reduce-sound (sub e σ)) ⟩
    ⟦ x ⟧uop ⟦ reduce (sub e σ ) ⟧exp ∎
  where open ≅ᵗʸ-Reasoning
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

⟦⟧exp-cong : ∀ {ℓc s s'} {Γ : Ctx C ℓc} →
             {e : Exp Γ s} {e' : Exp Γ s'} →
             (p : s ≡ s') →
             ω-transp (Exp Γ) p e ≡ω e' →
             ⟦ e ⟧exp ≅ᵗʸ ⟦ e' ⟧exp
⟦⟧exp-cong refl refl = ≅ᵗʸ-refl

type-naturality-reflect : ∀ {ℓc s s'} {Γ : Ctx C ℓc} →
                          (e : Exp Γ s) (e' : Exp Γ s') →
                          (p : reduce-skeleton s ≡ reduce-skeleton s') →
                          ω-transp (Exp Γ) p (reduce e) ≡ω reduce e' →
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

module Operations where
  open import Types.Discrete
  open import Types.Functions
  open import Types.Products
  open import Types.Sums

  discr-nul : ∀ {ℓ} {A : Set ℓ} → NullaryTypeOp ℓ
  discr-nul {A = A} = record { ⟦_⟧nop = Discr A ; naturality = λ σ → Discr-natural A σ }

  fun-bin : BinaryTypeOp (λ ℓc ℓ1 ℓ2 → ℓc ⊔ ℓ1 ⊔ ℓ2)
  fun-bin = record { ⟦_⟧bop_$_ = _⇛_ ; naturality = λ σ → ⇛-natural σ ; congruence = ⇛-cong }

  prod-bin : BinaryTypeOp (λ _ ℓ1 ℓ2 → ℓ1 ⊔ ℓ2)
  prod-bin = record { ⟦_⟧bop_$_ = _⊠_ ; naturality = λ σ → ⊠-natural σ ; congruence = ⊠-cong }

  sum-bin : BinaryTypeOp (λ _ ℓ1 ℓ2 → ℓ1 ⊔ ℓ2)
  sum-bin = record { ⟦_⟧bop_$_ = _⊞_ ; naturality = λ σ → ⊞-natural σ ; congruence = ⊞-cong }

open Operations public

private
  open import Types.Discrete
  open import Types.Functions
  open import Types.Products

  example : ∀ {ℓ ℓ' ℓ''} {Δ : Ctx C ℓ} {Γ : Ctx C ℓ'} {Θ : Ctx C ℓ''} →
            (σ : Δ ⇒ Γ) (τ : Γ ⇒ Θ) →
            ((Bool' ⇛ Bool') ⊠ (Bool' [ τ ])) [ σ ] ≅ᵗʸ ((Bool' ⇛ Bool') [ σ ]) ⊠ Bool'
  example σ τ = type-naturality-reflect (sub (bin prod-bin (bin fun-bin (nul discr-nul) (nul discr-nul)) (sub (nul discr-nul) τ)) σ)
                                        (bin prod-bin (sub (bin fun-bin (nul discr-nul) (nul discr-nul)) σ) (nul discr-nul))
                                        refl
                                        refl
