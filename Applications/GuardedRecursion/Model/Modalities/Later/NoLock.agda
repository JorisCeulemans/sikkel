--------------------------------------------------
-- A variant of ▻ requiring no lock on the context
--------------------------------------------------

module Applications.GuardedRecursion.Model.Modalities.Later.NoLock where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.DRA

open import Applications.GuardedRecursion.Model.Modalities.Later.Base

private
  variable
    m n : ℕ
    Γ Δ Θ : Ctx ω


--------------------------------------------------
-- Natural transformation from earlier to id-ctx-functor

ctx-m≤1+n : (Γ : Ctx ω) {m≤n : m ≤ n} {γ : Γ ⟨ suc n ⟩} →
            Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n n ⟫ γ) ≡ Γ ⟪ n≤1+n m ⟫ (Γ ⟪ s≤s m≤n ⟫ γ)
ctx-m≤1+n {m = m}{n = n} Γ {m≤n}{γ} =
  begin
    Γ ⟪ m≤n ⟫ (Γ ⟪ n≤1+n n ⟫ γ)
  ≡⟨ ctx-comp Γ ⟨
    Γ ⟪ ≤-trans m≤n (n≤1+n n) ⟫ γ
  ≡⟨ cong (Γ ⟪_⟫ γ) (≤-irrelevant _ _) ⟩
    Γ ⟪ ≤-trans (n≤1+n m)(s≤s m≤n) ⟫ γ
  ≡⟨ ctx-comp Γ ⟩
    Γ ⟪ n≤1+n m ⟫ (Γ ⟪ s≤s m≤n ⟫ γ) ∎
  where open ≡-Reasoning

from-earlier : (Γ : Ctx ω) → ◄ Γ ⇒ Γ
func (from-earlier Γ) = Γ ⟪ n≤1+n _ ⟫_
naturality (from-earlier Γ) = ctx-m≤1+n Γ

from-earlier-natural : (σ : Δ ⇒ Γ) → from-earlier Γ ⊚ ◄-subst σ ≅ˢ σ ⊚ from-earlier Δ
eq (from-earlier-natural σ) δ = naturality σ

𝟙≤later : TwoCell 𝟙 later
transf-op (transf 𝟙≤later) = from-earlier
CtxNatTransf.naturality (transf 𝟙≤later) = from-earlier-natural


--------------------------------------------------
-- Combining ▻ with the natural transformation

▻' : Ty Γ → Ty Γ
▻' {Γ = Γ} T = ▻ (T [ from-earlier Γ ])

prev' : {T : Ty Γ} → Tm Γ T → Tm (◄ Γ) (T [ from-earlier Γ ])
prev' t = t [ from-earlier _ ]'

next' : {T : Ty Γ} → Tm Γ T → Tm Γ (▻' T)
next' t = next (prev' t)

▻'-map : {T : Ty Γ} {S : Ty Γ} → (T ↣ S) → (▻' T ↣ ▻' S)
▻'-map η = ▻-map (ty-subst-map (from-earlier _) η)

▻'-cong : {T : Ty Γ} {T' : Ty Γ} → T ≅ᵗʸ T' → ▻' T ≅ᵗʸ ▻' T'
▻'-cong {Γ = Γ} T=T' = ▻-cong (ty-subst-cong-ty (from-earlier Γ) T=T')

-- The properties of ▻'-cong should follow from similar properties of
-- ▻-cong, but it is more straightforward to prove them directly.
▻'-cong-refl : {T : Ty Γ} → ▻'-cong (reflᵗʸ {T = T}) ≅ᵉ reflᵗʸ
eq (from-eq ▻'-cong-refl) {zero}  _ = refl
eq (from-eq ▻'-cong-refl) {suc n} _ = refl

▻'-cong-sym : {T S : Ty Γ} {e : T ≅ᵗʸ S} → ▻'-cong (symᵗʸ e) ≅ᵉ symᵗʸ (▻'-cong e)
eq (from-eq ▻'-cong-sym) {zero}  _ = refl
eq (from-eq ▻'-cong-sym) {suc n} _ = refl

▻'-cong-trans : {R S T : Ty Γ} {e1 : R ≅ᵗʸ S} {e2 : S ≅ᵗʸ T} → ▻'-cong (transᵗʸ e1 e2) ≅ᵉ transᵗʸ (▻'-cong e1) (▻'-cong e2)
eq (from-eq ▻'-cong-trans) {zero}  _ = refl
eq (from-eq ▻'-cong-trans) {suc n} _ = refl

▻'-cong-cong : {T S : Ty Γ} {e e' : T ≅ᵗʸ S} → e ≅ᵉ e' → ▻'-cong e ≅ᵉ ▻'-cong e'
eq (from-eq (▻'-cong-cong 𝑒)) {zero}  _ = refl
eq (from-eq (▻'-cong-cong 𝑒)) {suc n} t = eq (from-eq 𝑒) t


▻'-natural : (σ : Δ ⇒ Γ) {T : Ty Γ} → (▻' T) [ σ ] ≅ᵗʸ ▻' (T [ σ ])
▻'-natural σ = transᵗʸ (▻-natural σ) (▻-cong (ty-subst-cong-subst-2-2 _ (from-earlier-natural σ)))
