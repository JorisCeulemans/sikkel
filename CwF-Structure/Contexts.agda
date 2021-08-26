--------------------------------------------------
-- Contexts and substitutions + category structure
--------------------------------------------------

module CwF-Structure.Contexts where

open import Data.Unit using (⊤; tt)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Categories
open import Helpers


--------------------------------------------------
-- Definition of contexts and substitutions as presheaves over C

record Ctx (C : Category) : Set₁ where
  constructor MkCtx
  no-eta-equality

  open Category C

  field
    set : Ob → Set
    rel : ∀ {x y} → Hom x y → set y → set x
    ctx-id : ∀ {x} {γ : set x} → rel hom-id γ ≡ γ
    ctx-comp : ∀ {x y z} {f : Hom x y} {g : Hom y z} {γ : set z} →
               rel (g ∙ f) γ ≡ rel f (rel g γ)
open Ctx public renaming (set to _⟨_⟩; rel to _⟪_⟫_)

module _ {C : Category} where
  infix 10 _⇒_
  infix 1 _≅ˢ_
  infixl 20 _⊚_

  open Category C

  private
    variable
      x y z : Ob
      Δ Γ Θ : Ctx C

  -- The following proof is needed to define composition of morphisms in the category of elements
  -- of Γ and is used e.g. in the definition of types (in CwF-Structure.Types) and the definition
  -- of function types.
  strong-ctx-comp : (Γ : Ctx C) {f : Hom x y} {g : Hom y z} {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} →
                    (eq-zy : Γ ⟪ g ⟫ γz ≡ γy) (eq-yx : Γ ⟪ f ⟫ γy ≡ γx) →
                    Γ ⟪ g ∙ f ⟫ γz ≡ γx
  strong-ctx-comp Γ {f}{g}{γz}{γy}{γx} eq-zy eq-yx =
    begin
      Γ ⟪ g ∙ f ⟫ γz
    ≡⟨ ctx-comp Γ ⟩
      Γ ⟪ f ⟫ (Γ ⟪ g ⟫ γz)
    ≡⟨ cong (Γ ⟪ f ⟫_) eq-zy ⟩
      Γ ⟪ f ⟫ γy
    ≡⟨ eq-yx ⟩
      γx ∎
    where open ≡-Reasoning

  -- The type of substitutions from context Δ to context Γ
  record _⇒_ (Δ : Ctx C) (Γ : Ctx C) : Set where
    constructor MkSubst
    no-eta-equality
    field
      func : ∀ {x} → Δ ⟨ x ⟩ → Γ ⟨ x ⟩
      naturality : ∀ {x y} {f : Hom x y} {δ : Δ ⟨ y ⟩} → Γ ⟪ f ⟫ (func δ) ≡ func (Δ ⟪ f ⟫ δ)
  open _⇒_ public

  id-subst : (Γ : Ctx C) → Γ ⇒ Γ
  func (id-subst Γ) = id
  naturality (id-subst Γ) = refl

  -- Composition of substitutions
  _⊚_ : Γ ⇒ Θ → Δ ⇒ Γ → Δ ⇒ Θ
  func (τ ⊚ σ) = func τ ∘ func σ
  naturality (_⊚_ {Γ = Γ}{Θ = Θ}{Δ = Δ} τ σ) {f = f} {δ = δ} =
    begin
      Θ ⟪ f ⟫ (func τ (func σ δ))
    ≡⟨ naturality τ ⟩
      func τ (Γ ⟪ f ⟫ func σ δ)
    ≡⟨ cong (func τ) (naturality σ) ⟩
      func τ (func σ (Δ ⟪ f ⟫ δ)) ∎
    where open ≡-Reasoning


  --------------------------------------------------
  -- Equivalence of substitutions

  -- Two substitutions σ, τ : Δ ⇒ Γ are equivalent if they map every value of
  -- Δ ⟨ x ⟩ (for any object x) to propositionally equal values of Γ ⟨ x ⟩.
  record _≅ˢ_ {Δ : Ctx C} {Γ : Ctx C} (σ τ : Δ ⇒ Γ) : Set where
    field
      eq : ∀ {x} δ → func σ {x} δ ≡ func τ δ
  open _≅ˢ_ public

  ≅ˢ-refl : {σ : Δ ⇒ Γ} → σ ≅ˢ σ
  eq ≅ˢ-refl _ = refl

  ≅ˢ-sym : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → τ ≅ˢ σ
  eq (≅ˢ-sym σ=τ) δ = sym (eq σ=τ δ)

  ≅ˢ-trans : {σ τ ψ : Δ ⇒ Γ} → σ ≅ˢ τ → τ ≅ˢ ψ → σ ≅ˢ ψ
  eq (≅ˢ-trans σ=τ τ=ψ) δ = trans (eq σ=τ δ) (eq τ=ψ δ)

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
  eq (⊚-id-substʳ σ) _ = refl

  ⊚-id-substˡ : (σ : Δ ⇒ Γ) → id-subst Γ ⊚ σ ≅ˢ σ
  eq (⊚-id-substˡ σ) _ = refl

  ⊚-assoc : {Γ₁ : Ctx C} {Γ₂ : Ctx C} {Γ₃ : Ctx C} {Γ₄ : Ctx C}
             {σ₃₄ : Γ₃ ⇒ Γ₄} {σ₂₃ : Γ₂ ⇒ Γ₃} {σ₁₂ : Γ₁ ⇒ Γ₂} →
             (σ₃₄ ⊚ σ₂₃) ⊚ σ₁₂ ≅ˢ σ₃₄ ⊚ (σ₂₃ ⊚ σ₁₂)
  eq ⊚-assoc _ = refl

  ⊚-congˡ : {τ : Γ ⇒ Θ} {σ σ' : Δ ⇒ Γ} → σ ≅ˢ σ' → τ ⊚ σ ≅ˢ τ ⊚ σ'
  eq (⊚-congˡ {τ = τ} σ=σ') δ = cong (func τ) (eq σ=σ' δ)

  ⊚-congʳ : {τ τ' : Γ ⇒ Θ} {σ : Δ ⇒ Γ} → τ ≅ˢ τ' → τ ⊚ σ ≅ˢ τ' ⊚ σ
  eq (⊚-congʳ {σ = σ} τ=τ') δ = eq τ=τ' (func σ δ)


  --------------------------------------------------
  -- The empty context (i.e. terminal object in the category of contexts)

  ◇ : Ctx C
  ◇ ⟨ _ ⟩ = ⊤
  ◇ ⟪ _ ⟫ _ = tt
  ctx-id ◇ = refl
  ctx-comp ◇ = refl

  !◇ : (Γ : Ctx C) → Γ ⇒ ◇
  func (!◇ Γ) _ = tt
  naturality (!◇ Γ) = refl

  ◇-terminal : (Γ : Ctx C) (σ τ : Γ ⇒ ◇) → σ ≅ˢ τ
  eq (◇-terminal Γ σ τ) _ = refl
