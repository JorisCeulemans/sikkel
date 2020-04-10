module CwF-Structure.ContextExtension where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.Unit using (⊤; tt)
open import Function hiding (_⟨_⟩_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms

infixl 15 _,,_

--------------------------------------------------
-- Context extension
--------------------------------------------------

_,,_ : (Γ : Ctx ℓ) (T : Ty Γ) → Ctx ℓ
set (Γ ,, T) n = Σ[ γ ∈ Γ ⟨ n ⟩ ] (T ⟨ n , γ ⟩)
rel (Γ ,, T) ineq [ γ , t ] = [ Γ ⟪ ineq ⟫ γ , strict-morph T ineq γ t ]
rel-id (Γ ,, T) [ γ , t ] = to-Σ-eq (rel-id Γ γ) (strict-morph-id T t)
rel-comp (Γ ,, T) k≤m m≤n [ γ , t ] = to-Σ-eq (rel-comp Γ k≤m m≤n γ)
                                              (strict-morph-comp T k≤m m≤n t)

π : {Γ : Ctx ℓ} {T : Ty Γ} → Γ ,, T ⇒ Γ
func π = proj₁
naturality π _ = refl

ξ : {Γ : Ctx ℓ} {T : Ty Γ} → Tm (Γ ,, T) (T [ π {T = T} ])
term ξ = λ _ → proj₂
naturality (ξ {T = T}) m≤n eq = trans (sym (morph-subst T refl (cong proj₁ eq) _))
                                      (from-Σ-eq2 eq) -- can be simpler by pattern matching on eq

from-ext-subst : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Δ ⇒ Γ ,, T → Σ[ σ ∈ Δ ⇒ Γ ] (Tm Δ (T [ σ ]))
from-ext-subst {Δ = Δ}{Γ}{T} τ = [ π ⊚ τ , subst (Tm Δ) (ty-subst-comp T π τ) (ξ [ τ ]') ]

to-ext-subst : {Δ Γ : Ctx ℓ} (T : Ty Γ) (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ]) → Δ ⇒ Γ ,, T
to-ext-subst T σ t = MkSubst (λ δ → [ func σ δ , t ⟨ _ , δ ⟩' ])
                             (λ δ → to-Σ-eq (naturality σ δ)
                                             (trans (morph-subst T refl (naturality σ δ) (term t _ δ))
                                                    (trans (cong (λ x → T ⟪ _ , x ⟫ _) (sym (trans-reflʳ (naturality σ δ))))
                                                           (naturality t _ refl))))

to-ext-subst-Σ : {Δ Γ : Ctx ℓ} (T : Ty Γ) → Σ[ σ ∈ Δ ⇒ Γ ] (Tm Δ (T [ σ ])) → Δ ⇒ Γ ,, T
to-ext-subst-Σ T [ σ , t ] = to-ext-subst T σ t

ctx-ext-left-inverse : {Δ Γ : Ctx ℓ} {T : Ty Γ} (p : Σ[ σ ∈ Δ ⇒ Γ ] (Tm Δ (T [ σ ]))) → from-ext-subst (to-ext-subst-Σ T p) ≡ p
ctx-ext-left-inverse {Δ = Δ} {T = T} [ σ , t ] = to-Σ-eq (to-subst-eq (λ δ → refl))
                                                         (cong₂-d MkTm proof
                                                                       (funextI (funextI (funext λ _ → funextI (funextI (funext λ _ → uip _ _))))))
  where
    open ≡-Reasoning
    α = to-subst-eq (λ δ → refl)
    ζ = ty-subst-comp T π (to-ext-subst-Σ T [ σ , t ])
    β = subst (Tm Δ) ζ (ξ [ to-ext-subst-Σ T [ σ , t ] ]')
    proof = term (subst (λ x → Tm Δ (T [ x ])) α β)
              ≡⟨ cong term {y = subst (Tm Δ) (cong (T [_]) α) β}
                      (subst-∘ {f = λ x → T [ x ]} α {p = β}) ⟩
            term (subst (Tm Δ) (cong (T [_]) α) β)
              ≡⟨ cong term {x = subst (Tm Δ) (cong (T [_]) α) β}
                           {y = subst (Tm Δ) (trans ζ (cong (T [_]) α))
                                      (ξ [ to-ext-subst-Σ T [ σ , t ] ]')}
                           (subst-subst ζ) ⟩
            term (subst (Tm Δ) (trans ζ (cong (T [_]) α)) (ξ [ to-ext-subst-Σ T [ σ , t ] ]'))
              ≡⟨ sym (weak-subst-application {B = Tm Δ} (λ x y → term y) (trans ζ (cong (T [_]) α))) ⟩
            subst (λ z → (n : ℕ) (γ : Δ ⟨ n ⟩) → z ⟨ n , γ ⟩) (trans ζ (cong (T [_]) α)) (term (ξ [ to-ext-subst-Σ T [ σ , t ] ]'))
              ≡⟨ subst-∘ (trans ζ (cong (T [_]) α)) ⟩
            subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) (cong type (trans ζ (cong (T [_]) α))) (term (ξ [ to-ext-subst-Σ T [ σ , t ] ]'))
              ≡⟨ cong (λ x → subst (λ z → (n : ℕ) (δ : Δ ⟨ n ⟩) → z n δ) x (term (ξ [ to-ext-subst-Σ T [ σ , t ] ]')))
                      {x = cong type (trans ζ (cong (T [_]) α))}
                      {y = refl}
                      (uip _ _) ⟩
            term t ∎

ctx-ext-right-inverse : {Δ Γ : Ctx ℓ} {T : Ty Γ} (τ : Δ ⇒ Γ ,, T) → to-ext-subst-Σ T (from-ext-subst τ) ≡ τ
ctx-ext-right-inverse {Δ = Δ} {T = T} τ = to-subst-eq (λ δ → cong [ proj₁ (func τ δ) ,_]
  (term (subst (Tm Δ) ζ η) _ δ
    ≡⟨ cong (λ z → z _ δ) (sym (weak-subst-application {B = Tm Δ} (λ x y → term y) ζ)) ⟩
  subst (λ x → (m : ℕ) (δ' : Δ ⟨ m ⟩) → x ⟨ m , δ' ⟩) ζ (term η) _ δ
    ≡⟨ cong (λ z → z _ δ) {x = subst (λ x → (m : ℕ) (δ' : Δ ⟨ m ⟩) → x ⟨ m , δ' ⟩) ζ (term η)}
            (subst-∘ ζ) ⟩
  subst (λ x → (m : ℕ) (δ' : Δ ⟨ m ⟩) → x m δ') (cong type ζ) (term η) _ δ
    ≡⟨ cong (λ z → subst (λ x → (m : ℕ) (δ' : Δ ⟨ m ⟩) → x m δ') z (term η) _ δ)
            {x = cong type ζ}
            {y = refl}
            (uip (cong type ζ) refl) ⟩
  proj₂ (func τ δ) ∎))
  where
    open ≡-Reasoning
    ζ = ty-subst-comp T π τ
    η = ξ {T = T} [ τ ]'

π-ext-comp : {Δ Γ : Ctx ℓ} (T : Ty Γ) (σ : Δ ⇒ Γ ) (t : Tm Δ (T [ σ ])) →
             π ⊚ to-ext-subst T σ t ≡ σ
π-ext-comp T σ t = to-subst-eq (λ δ → refl)

π-ext-comp-ty-subst : {Δ Γ : Ctx ℓ} {T : Ty Γ} (σ : Δ ⇒ Γ ) (t : Tm Δ (T [ σ ])) (S : Ty Γ) →
                      S [ π ] [ to-ext-subst T σ t ] ≡ S [ σ ]
π-ext-comp-ty-subst {T = T} σ t S =
  S [ π ] [ to-ext-subst T σ t ]
    ≡⟨ ty-subst-comp S π (to-ext-subst T σ t) ⟩
  S [ π ⊚ to-ext-subst T σ t ]
    ≡⟨ cong (S [_]) (π-ext-comp T σ t) ⟩
  S [ σ ] ∎
  where open ≡-Reasoning

_⌈_⌋ : {Γ : Ctx ℓ} {T S : Ty Γ} → Tm (Γ ,, T) (S [ π ]) → Tm Γ T → Tm Γ S
_⌈_⌋ {Γ = Γ}{T}{S} s t = subst (Tm Γ) proof (s [ to-ext-subst T (id-subst Γ) (t [ id-subst Γ ]') ]')
  where
    open ≡-Reasoning
    proof : S [ π ] [ to-ext-subst T (id-subst Γ) (t [ id-subst Γ ]') ] ≡ S
    proof =
      S [ π ] [ to-ext-subst T (id-subst Γ) (t [ id-subst Γ ]') ]
        ≡⟨ π-ext-comp-ty-subst {T = T} (id-subst Γ) (t [ id-subst Γ ]') S ⟩
      S [ id-subst Γ ]
        ≡⟨ ty-subst-id S ⟩
      S ∎

_⊹ : {Δ Γ : Ctx ℓ} {T : Ty Γ} (σ : Δ ⇒ Γ) → Δ ,, T [ σ ] ⇒ Γ ,, T
_⊹ {Δ = Δ} {T = T} σ = to-ext-subst T (σ ⊚ π) (subst (Tm (Δ ,, T [ σ ])) (ty-subst-comp T σ π) ξ)

module _ {Δ Γ : Ctx ℓ} {T : Ty Γ} (σ : Δ ⇒ Γ) where
  ⊹-π-comm : π {T = T} ⊚ (σ ⊹) ≡ σ ⊚ π
  ⊹-π-comm = to-subst-eq (λ δ → refl)
{-
⊹-tm-comp : {Δ Γ Θ : Ctx ℓ} (T : Ty Θ) (S : Ty (Θ ,, T)) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
            Tm (Δ ,, T [ τ ] [ σ ]) (S [ τ ⊹ ] [ σ ⊹ ]) → Tm (Δ ,, T [ τ ⊚ σ ]) (S [ (τ ⊚ σ) ⊹ ])
term (⊹-tm-comp T S τ σ s) n [ δ , t ] = {!s ⟨ n , ? ⟩'!}
naturality (⊹-tm-comp T S τ σ s) = {!!}
-}
