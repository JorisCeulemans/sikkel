{-# OPTIONS --omega-in-omega #-}

open import Categories
module Reflection.Substitution {C : Category} where

open import Level
-- open import Relation.Binary.PropositionalEquality

open import CwF-Structure.Contexts
open import Reflection.Helpers

private
  variable
    ℓ ℓ' ℓ'' : Level
    Δ Γ Θ Ξ : Ctx C ℓ


data Val : {ℓ ℓ' : Level} → Ctx C ℓ → Ctx C ℓ' → Setω where
  var : {Δ : Ctx C ℓ} {Γ : Ctx C ℓ'} (σ : Δ ⇒ Γ) → Val Δ Γ
  id' : {Γ : Ctx C ℓ} → Val Γ Γ
  !◇' : {Γ : Ctx C ℓ} → Val Γ ◇

data Exp : {ℓ ℓ' : Level} → Ctx C ℓ → Ctx C ℓ' → Setω where
  val : {Δ : Ctx C ℓ} {Γ : Ctx C ℓ'} → Val Δ Γ → Exp Δ Γ
  _⊚'_ : {Δ : Ctx C ℓ} {Γ : Ctx C ℓ'} {Θ : Ctx C ℓ''} →
           Exp Γ Θ → Exp Δ Γ → Exp Δ Θ

⟦_⟧v : Val Δ Γ → Δ ⇒ Γ
⟦ var σ ⟧v = σ
⟦ id' ⟧v   = id-subst _
⟦ !◇' ⟧v   = !◇ _

⟦_⟧e : Exp Δ Γ → Δ ⇒ Γ
⟦ val s ⟧e    = ⟦ s ⟧v
⟦ e1 ⊚' e2 ⟧e = ⟦ e1 ⟧e ⊚ ⟦ e2 ⟧e

data ValSeq : {ℓ ℓ' : Level} → Ctx C ℓ → Ctx C ℓ' → Setω where
  [] : {Γ : Ctx C ℓ} → ValSeq Γ Γ
  _∷_ : {Δ : Ctx C ℓ} {Γ : Ctx C ℓ''} {Θ : Ctx C ℓ'} (σ : Val Γ Θ) (σs : ValSeq Δ Γ) → ValSeq Δ Θ

_++_ : ValSeq Γ Θ → ValSeq Δ Γ → ValSeq Δ Θ
[]       ++ τs = τs
(σ ∷ σs) ++ τs = σ ∷ (σs ++ τs)

⟦_⟧vs : ValSeq Δ Γ → Δ ⇒ Γ
⟦ [] ⟧vs     = id-subst _
⟦ σ ∷ σs ⟧vs = ⟦ σ ⟧v ⊚ ⟦ σs ⟧vs

reduce : ValSeq Δ Γ → ValSeq Δ Γ
reduce []           = []
reduce (var σ ∷ σs) = var σ ∷ reduce σs
reduce (id' ∷ σs)   = reduce σs
reduce (!◇' ∷ σs)   = !◇' ∷ []

flatten : Exp Δ Γ → ValSeq Δ Γ
flatten (val σ)    = σ ∷ []
flatten (e1 ⊚' e2) = flatten e1 ++ flatten e2

reduce-sound : (σs : ValSeq Δ Γ) → ⟦ reduce σs ⟧vs ≅ˢ ⟦ σs ⟧vs
reduce-sound []           = ≅ˢ-refl
reduce-sound (var σ ∷ σs) = ⊚-congˡ σ (reduce-sound σs)
reduce-sound (id'   ∷ σs) = ≅ˢ-trans (reduce-sound σs) (≅ˢ-sym (⊚-id-substˡ ⟦ σs ⟧vs))
reduce-sound (!◇'   ∷ σs) = ◇-terminal _ _ _

concat-denote : (σs : ValSeq Γ Θ) (τs : ValSeq Δ Γ) → ⟦ σs ++ τs ⟧vs ≅ˢ ⟦ σs ⟧vs ⊚ ⟦ τs ⟧vs
concat-denote []       τs = ≅ˢ-sym (⊚-id-substˡ ⟦ τs ⟧vs)
concat-denote (σ ∷ σs) τs =
  begin
    ⟦ σ ⟧v ⊚ ⟦ σs ++ τs ⟧vs
  ≅⟨ ⊚-congˡ ⟦ σ ⟧v (concat-denote σs τs) ⟩
    ⟦ σ ⟧v ⊚ (⟦ σs ⟧vs ⊚ ⟦ τs ⟧vs)
  ≅˘⟨ ⊚-assoc ⟦ σ ⟧v ⟦ σs ⟧vs ⟦ τs ⟧vs ⟩
    (⟦ σ ⟧v ⊚ ⟦ σs ⟧vs) ⊚ ⟦ τs ⟧vs ∎
  where open ≅ˢ-Reasoning

flatten-sound : (e : Exp Δ Γ) → ⟦ flatten e ⟧vs ≅ˢ ⟦ e ⟧e
flatten-sound (val σ)    = ⊚-id-substʳ ⟦ σ ⟧v
flatten-sound (e1 ⊚' e2) =
  begin
    ⟦ flatten e1 ++ flatten e2 ⟧vs
  ≅⟨ concat-denote (flatten e1) (flatten e2) ⟩
    ⟦ flatten e1 ⟧vs ⊚ ⟦ flatten e2 ⟧vs
  ≅⟨ ⊚-congʳ _ (flatten-sound e1) ⟩
    ⟦ e1 ⟧e ⊚ ⟦ flatten e2 ⟧vs
  ≅⟨ ⊚-congˡ _ (flatten-sound e2) ⟩
    ⟦ e1 ⟧e ⊚ ⟦ e2 ⟧e ∎
  where open ≅ˢ-Reasoning

vs-cong : {σs τs : ValSeq Δ Γ} → σs ≡ω τs → ⟦ σs ⟧vs ≅ˢ ⟦ τs ⟧vs
vs-cong refl = ≅ˢ-refl

subst-reflect : (e1 e2 : Exp Δ Γ) → reduce (flatten e1) ≡ω reduce (flatten e2) → ⟦ e1 ⟧e ≅ˢ ⟦ e2 ⟧e
subst-reflect e1 e2 eq =
  begin
    ⟦ e1 ⟧e
  ≅˘⟨ flatten-sound e1 ⟩
    ⟦ flatten e1 ⟧vs
  ≅˘⟨ reduce-sound (flatten e1) ⟩
    ⟦ reduce (flatten e1) ⟧vs
  ≅⟨ vs-cong eq ⟩
    ⟦ reduce (flatten e2) ⟧vs
  ≅⟨ reduce-sound (flatten e2) ⟩
    ⟦ flatten e2 ⟧vs
  ≅⟨ flatten-sound e2 ⟩
    ⟦ e2 ⟧e ∎
  where open ≅ˢ-Reasoning

private
  example : (ρ : Δ ⇒ Ξ) (σ : ◇ ⇒ Γ) (τ : Γ ⇒ Θ) → ((id-subst Θ ⊚ τ) ⊚ σ) ⊚ (!◇ Ξ ⊚ ρ) ≅ˢ τ ⊚ ((σ ⊚ id-subst ◇) ⊚ (!◇ Ξ ⊚ (id-subst Ξ ⊚ ρ)))
  example ρ σ τ = subst-reflect (((val id' ⊚' val (var τ)) ⊚' val (var σ)) ⊚' (val !◇' ⊚' val (var ρ)))
                                (val (var τ) ⊚' ((val (var σ) ⊚' val id') ⊚' (val !◇' ⊚' (val id' ⊚' val (var ρ)))))
                                refl

  example2 : (σ : Δ ⇒ Γ) → !◇ Γ ⊚ σ ≅ˢ id-subst ◇ ⊚ !◇ Δ
  example2 σ = subst-reflect (val !◇' ⊚' val (var σ))
                             (val id' ⊚' val !◇')
                             refl
