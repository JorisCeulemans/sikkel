{-# OPTIONS --without-K #-}

--------------------------------------------------
-- Contexts and substitutions + category structure
--------------------------------------------------

module CwF-Structure.Contexts where

open import Data.Unit using (⊤; tt)
open import Function using (id; _∘_; Congruent)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality
  hiding (naturality) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; setoid to ≡-setoid)

open import Categories
open import Helpers

private
  variable
    r r' : Level


--------------------------------------------------
-- Definition of contexts and substitutions as presheaves over C

record Ctx (C : Category) ℓ r : Set (lsuc ℓ ⊔ lsuc r) where
  constructor MkCtx
  no-eta-equality

  open Category C
  open Setoid

  field
    setoid : Ob → Setoid ℓ r

  _⟨_⟩ : Ob → Set ℓ
  _⟨_⟩ x = Carrier (setoid x)

  ctx≈ : (x : Ob) → _⟨_⟩ x → _⟨_⟩ x → Set r
  ctx≈ x = _≈_ (setoid x)

  field
    rel : ∀ {x y} → Hom x y → _⟨_⟩ y → _⟨_⟩ x
    rel-cong : ∀ {x y} (f : Hom x y) →
                Congruent (ctx≈ y) (ctx≈ x) (rel f)
    rel-id : ∀ {x} (γ : _⟨_⟩ x) → ctx≈ x (rel hom-id γ) γ
    rel-comp : ∀ {x y z} (f : Hom x y) (g : Hom y z) (γ : _⟨_⟩ z) →
               ctx≈ x (rel (g ∙ f) γ) (rel f (rel g γ))

  ctx≈-refl : {x : Ob} {γ : _⟨_⟩ x} → ctx≈ x γ γ
  ctx≈-refl {x} = refl (setoid x)

  ctx≈-sym : {x : Ob} {γ1 γ2 : _⟨_⟩ x} → ctx≈ x γ1 γ2 → ctx≈ x γ2 γ1
  ctx≈-sym {x} = sym (setoid x)

  ctx≈-trans : {x : Ob} {γ1 γ2 γ3 : _⟨_⟩ x} → ctx≈ x γ1 γ2 → ctx≈ x γ2 γ3 → ctx≈ x γ1 γ3
  ctx≈-trans {x} = trans (setoid x)

open Ctx public

ctx≈-syntax : {C : Category} (Γ : Ctx C ℓ r) {x : Category.Ob C} (γ1 γ2 : Γ ⟨ x ⟩) → Set r
ctx≈-syntax Γ {x} = ctx≈ Γ x

infix 1 ctx≈-syntax
syntax ctx≈-syntax Γ γ1 γ2 = γ1 ≈[ Γ ]≈ γ2

module _ {C : Category} where
  infix 10 _⇒_
  infix 1 _≅ˢ_
  infixl 20 _⊚_

  open Category C

  private
    variable
      x y z : Ob
      Δ Γ Θ : Ctx C ℓ r

  _⟪_⟫_ : (Γ : Ctx C ℓ r) (f : Hom x y) → Γ ⟨ y ⟩ → Γ ⟨ x ⟩
  Γ ⟪ f ⟫ γ = rel Γ f γ

  rel-hom-cong : (Γ : Ctx C ℓ r) {f f' : Hom x y} {γy : Γ ⟨ y ⟩} →
                 f ≡ f' → Γ ⟪ f ⟫ γy ≈[ Γ ]≈ Γ ⟪ f' ⟫ γy
  rel-hom-cong Γ ≡-refl = ctx≈-refl Γ

  -- The following proof is needed to define composition of morphisms in the category of elements
  -- of Γ and is used e.g. in the definition of types (in CwF-Structure.Types) and the definition
  -- of function types.
  strong-rel-comp : (Γ : Ctx C ℓ r) {f : Hom x y} {g : Hom y z} {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} →
                    (eq-zy : Γ ⟪ g ⟫ γz ≈[ Γ ]≈ γy) (eq-yx : Γ ⟪ f ⟫ γy ≈[ Γ ]≈ γx) →
                    Γ ⟪ g ∙ f ⟫ γz ≈[ Γ ]≈ γx
  strong-rel-comp {x = x} Γ {f}{g}{γz}{γy}{γx} eq-zy eq-yx =
    begin
      Γ ⟪ g ∙ f ⟫ γz
    ≈⟨ rel-comp Γ f g γz ⟩
      Γ ⟪ f ⟫ (Γ ⟪ g ⟫ γz)
    ≈⟨ rel-cong Γ f eq-zy ⟩
      Γ ⟪ f ⟫ γy
    ≈⟨ eq-yx ⟩
      γx ∎
    where open SetoidReasoning (setoid Γ x)

  -- The type of substitutions from context Δ to context Γ
  record _⇒_ (Δ : Ctx C ℓ r) (Γ : Ctx C ℓ' r') : Set (ℓ ⊔ ℓ' ⊔ r ⊔ r') where
    constructor MkSubst
    no-eta-equality
    field
      func : ∀ {x} → Δ ⟨ x ⟩ → Γ ⟨ x ⟩
      func-cong : ∀ {x} → Congruent (ctx≈ Δ x) (ctx≈ Γ x) func
      naturality : ∀ {x y} {f : Hom x y} (δ : Δ ⟨ y ⟩) → Γ ⟪ f ⟫ (func δ) ≈[ Γ ]≈ func (Δ ⟪ f ⟫ δ)
  open _⇒_ public

  id-subst : (Γ : Ctx C ℓ r) → Γ ⇒ Γ
  func (id-subst Γ) = id
  func-cong (id-subst Γ) e = e
  naturality (id-subst Γ) = λ _ → ctx≈-refl Γ

  -- Composition of substitutions
  _⊚_ : Γ ⇒ Θ → Δ ⇒ Γ → Δ ⇒ Θ
  func (τ ⊚ σ) = func τ ∘ func σ
  func-cong (τ ⊚ σ) = func-cong τ ∘ func-cong σ
  naturality (_⊚_ {Γ = Γ}{Θ = Θ}{Δ = Δ} τ σ) {f = f} δ =
    begin
      Θ ⟪ f ⟫ (func τ (func σ δ))
    ≈⟨ naturality τ (func σ δ) ⟩
      func τ (Γ ⟪ f ⟫ func σ δ)
    ≈⟨ func-cong τ (naturality σ δ) ⟩
      func τ (func σ (Δ ⟪ f ⟫ δ)) ∎
    where open SetoidReasoning (setoid Θ _)


  --------------------------------------------------
  -- Equivalence of substitutions

  -- Two substitutions σ, τ : Δ ⇒ Γ are equivalent if they map every value of
  -- Δ ⟨ x ⟩ (for any object x) to equivalent values of Γ ⟨ x ⟩.
  record _≅ˢ_ {ℓ ℓ'} {Δ : Ctx C ℓ r} {Γ : Ctx C ℓ' r'} (σ τ : Δ ⇒ Γ) : Set (ℓ ⊔ r') where
    field
      eq : ∀ {x} δ → func σ {x} δ ≈[ Γ ]≈ func τ δ
  open _≅ˢ_ public

  ≅ˢ-refl : {σ : Δ ⇒ Γ} → σ ≅ˢ σ
  eq (≅ˢ-refl {Γ = Γ}) _ = ctx≈-refl Γ

  ≅ˢ-sym : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → τ ≅ˢ σ
  eq (≅ˢ-sym {Γ = Γ} σ=τ) δ = ctx≈-sym Γ (eq σ=τ δ)

  ≅ˢ-trans : {σ τ ψ : Δ ⇒ Γ} → σ ≅ˢ τ → τ ≅ˢ ψ → σ ≅ˢ ψ
  eq (≅ˢ-trans {Γ = Γ} σ=τ τ=ψ) δ = ctx≈-trans Γ (eq σ=τ δ) (eq τ=ψ δ)

  module ≅ˢ-Reasoning where
    infix  3 _∎
    infixr 2 _≅⟨⟩_ step-≅ step-≅˘
    infix  1 begin_

    begin_ : ∀ {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → σ ≅ˢ τ
    begin_ σ=τ = σ=τ

    _≅⟨⟩_ : ∀ (σ {τ} : Δ ⇒ Γ) → σ ≅ˢ τ → σ ≅ˢ τ
    _ ≅⟨⟩ σ=τ = σ=τ

    step-≅ : ∀ (σ {τ ψ} : Δ ⇒ Γ) → τ ≅ˢ ψ → σ ≅ˢ τ → σ ≅ˢ ψ
    step-≅ _ τ≅ψ σ≅τ = ≅ˢ-trans σ≅τ τ≅ψ

    step-≅˘ : ∀ (σ {τ ψ} : Δ ⇒ Γ) → τ ≅ˢ ψ → τ ≅ˢ σ → σ ≅ˢ ψ
    step-≅˘ _ τ≅ψ τ≅σ = ≅ˢ-trans (≅ˢ-sym τ≅σ) τ≅ψ

    _∎ : ∀ (σ : Δ ⇒ Γ) → σ ≅ˢ σ
    _∎ _ = ≅ˢ-refl

    syntax step-≅  σ τ≅ψ σ≅τ = σ ≅⟨  σ≅τ ⟩ τ≅ψ
    syntax step-≅˘ σ τ≅ψ τ≅σ = σ ≅˘⟨ τ≅σ ⟩ τ≅ψ


  --------------------------------------------------
  -- Laws for the category of contexts

  ⊚-id-substʳ : (σ : Δ ⇒ Γ) → σ ⊚ id-subst Δ ≅ˢ σ
  eq (⊚-id-substʳ {Γ = Γ} σ) _ = ctx≈-refl Γ

  ⊚-id-substˡ : (σ : Δ ⇒ Γ) → id-subst Γ ⊚ σ ≅ˢ σ
  eq (⊚-id-substˡ {Γ = Γ} σ) _ = ctx≈-refl Γ

  ⊚-assoc : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ r₁ r₂ r₃ r₄}
             {Γ₁ : Ctx C ℓ₁ r₁} {Γ₂ : Ctx C ℓ₂ r₂} {Γ₃ : Ctx C ℓ₃ r₃} {Γ₄ : Ctx C ℓ₄ r₄}
             (σ₃₄ : Γ₃ ⇒ Γ₄) (σ₂₃ : Γ₂ ⇒ Γ₃) (σ₁₂ : Γ₁ ⇒ Γ₂) →
             (σ₃₄ ⊚ σ₂₃) ⊚ σ₁₂ ≅ˢ σ₃₄ ⊚ (σ₂₃ ⊚ σ₁₂)
  eq (⊚-assoc {Γ₄ = Γ₄} σ₃₄ σ₂₃ σ₁₂) _ = ctx≈-refl Γ₄

  ⊚-congˡ : (τ : Γ ⇒ Θ) {σ σ' : Δ ⇒ Γ} → σ ≅ˢ σ' → τ ⊚ σ ≅ˢ τ ⊚ σ'
  eq (⊚-congˡ τ σ=σ') δ = func-cong τ (eq σ=σ' δ)

  ⊚-congʳ : {τ τ' : Γ ⇒ Θ} (σ : Δ ⇒ Γ) → τ ≅ˢ τ' → τ ⊚ σ ≅ˢ τ' ⊚ σ
  eq (⊚-congʳ σ τ=τ') δ = eq τ=τ' (func σ δ)


  --------------------------------------------------
  -- The empty context (i.e. terminal object in the category of contexts)

  ◇ : Ctx C 0ℓ 0ℓ
  setoid ◇ _ = ≡-setoid ⊤
  rel ◇ _ _ = tt
  rel-cong ◇ _ _ = ≡-refl
  rel-id ◇ _ = ≡-refl
  rel-comp ◇ _ _ _ = ≡-refl

  !◇ : (Γ : Ctx C ℓ r) → Γ ⇒ ◇
  func (!◇ Γ) _ = tt
  func-cong (!◇ Γ) _ = ≡-refl
  naturality (!◇ Γ) _ = ≡-refl

  ◇-terminal : (Γ : Ctx C ℓ r) (σ τ : Γ ⇒ ◇) → σ ≅ˢ τ
  eq (◇-terminal Γ σ τ) _ = ≡-refl
