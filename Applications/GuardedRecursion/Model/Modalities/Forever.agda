--------------------------------------------------
-- The constantly-forever dependent adjunction
--------------------------------------------------

module Applications.GuardedRecursion.Model.Modalities.Forever where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.Helpers
open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.DRA

private
  variable
    Δ Γ Θ : Ctx ★


--------------------------------------------------
-- The constantly context functor

constantly-ctx : Ctx ★ → Ctx ω
constantly-ctx Γ ⟨ _ ⟩ = Γ ⟨ tt ⟩
constantly-ctx Γ ⟪ _ ⟫ γ = γ
ctx-id (constantly-ctx Γ) = refl
ctx-comp (constantly-ctx Γ) = refl

constantly-subst : Δ ⇒ Γ → constantly-ctx Δ ⇒ constantly-ctx Γ
func (constantly-subst σ) = func σ
_⇒_.naturality (constantly-subst σ) = refl

constantly-subst-cong : {σ τ : Δ ⇒ Γ} → σ ≅ˢ τ → constantly-subst σ ≅ˢ constantly-subst τ
eq (constantly-subst-cong σ=τ) δ = eq σ=τ δ

constantly-subst-id : constantly-subst (id-subst Γ) ≅ˢ id-subst (constantly-ctx Γ)
eq constantly-subst-id _ = refl

constantly-subst-⊚ : (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) → constantly-subst (σ ⊚ τ) ≅ˢ constantly-subst σ ⊚ constantly-subst τ
eq (constantly-subst-⊚ σ τ) _ = refl


--------------------------------------------------
-- The forever type constructor and related term formers

-- A type constructor equivalent to OmegaLimit could also be defined
-- in terms of the Agda type family of semantic terms Tm. However, Tm
-- does not enjoy eta equality, which we use below to prove `to-ω-limit-eq`.
record OmegaLimit {Γ : Ctx ★} (T : Ty (constantly-ctx Γ)) (γ : Γ ⟨ tt ⟩) : Set where
  constructor ω-lim
  field
    limit : (n : ℕ) → T ⟨ n , γ ⟩
    limit-natural : {m n : ℕ} (m≤n : m ≤ n) → T ⟪ m≤n , refl ⟫ (limit n) ≡ limit m
open OmegaLimit

ω-limit-cast : {T : Ty (constantly-ctx Γ)} {γx γy : Γ ⟨ tt ⟩} → γy ≡ γx →
              OmegaLimit T γy → OmegaLimit T γx
limit (ω-limit-cast {T = T} eγ l) = λ n → T ⟪ ≤-refl , eγ ⟫ limit l n
limit-natural (ω-limit-cast {T = T} eγ l) =
  λ m≤n → trans (ty-cong-2-2 T (≤-irrelevant _ _)) (cong (T ⟪ ≤-refl , eγ ⟫_) (limit-natural l m≤n))

to-ω-limit-eq : {T : Ty (constantly-ctx Γ)} {γ : Γ ⟨ tt ⟩} {l l' : OmegaLimit T γ} →
                (∀ n → limit l n ≡ limit l' n) →
                l ≡ l'
to-ω-limit-eq f = cong₂-d ω-lim (funext f) (funextI (funextI (funext (λ _ → uip _ _))))

ω-limit-map : {T S : Ty (constantly-ctx Γ)} {γ : Γ ⟨ tt ⟩} → (T ↣ S) →
              OmegaLimit T γ → OmegaLimit S γ
limit (ω-limit-map η l) = λ n → func η (limit l n)
limit-natural (ω-limit-map η l) = λ m≤n → trans (_↣_.naturality η) (cong (func η) (limit-natural l m≤n))

forever-ty : Ty (constantly-ctx Γ) → Ty Γ
forever-ty T ⟨ tt , γ ⟩ = OmegaLimit T γ
forever-ty {Γ = Γ} T ⟪ tt , eγ ⟫ l = ω-limit-cast (trans (sym (ctx-id Γ)) eγ) l
ty-cong (forever-ty T) _ = to-ω-limit-eq (λ _ → ty-cong T refl)
ty-id (forever-ty T) = to-ω-limit-eq (λ _ → strong-ty-id T)
ty-comp (forever-ty T) = to-ω-limit-eq (λ _ → sym (ty-cong-2-1 T (≤-irrelevant _ _)))

module _ {T : Ty (constantly-ctx Γ)} where
  forever-tm : Tm (constantly-ctx Γ) T → Tm Γ (forever-ty T)
  limit (forever-tm t ⟨ tt , γ ⟩') = λ n → t ⟨ n , γ ⟩'
  limit-natural (forever-tm t ⟨ tt , γ ⟩') m≤n = Tm.naturality t m≤n refl
  Tm.naturality (forever-tm t) _ _ = to-ω-limit-eq (λ _ → Tm.naturality t ≤-refl _)

  unforever-tm : Tm Γ (forever-ty T) → Tm (constantly-ctx Γ) T
  unforever-tm t ⟨ n , γ ⟩' = limit (t ⟨ tt , γ ⟩') n
  Tm.naturality (unforever-tm t) m≤n refl = limit-natural (t ⟨ tt , _ ⟩') m≤n

  forever-ty-β : (t : Tm (constantly-ctx Γ) T) → unforever-tm (forever-tm t) ≅ᵗᵐ t
  eq (forever-ty-β t) _ = refl

  forever-ty-η : (t : Tm Γ (forever-ty T)) → forever-tm (unforever-tm t) ≅ᵗᵐ t
  eq (forever-ty-η t) _ = to-ω-limit-eq (λ _ → refl)


--------------------------------------------------
-- Functoriality of forever-ty

forever-ty-map : {T S : Ty (constantly-ctx Γ)} → (T ↣ S) → forever-ty T ↣ forever-ty S
func (forever-ty-map η) = ω-limit-map η
_↣_.naturality (forever-ty-map η) = to-ω-limit-eq (λ n → _↣_.naturality η)

forever-ty-map-id : {T : Ty (constantly-ctx Γ)} → forever-ty-map (id-trans T) ≅ⁿ id-trans (forever-ty T)
eq forever-ty-map-id _ = to-ω-limit-eq (λ _ → refl)

forever-ty-map-⊙ : {R S T : Ty (constantly-ctx Γ)} {η : S ↣ T} {φ : R ↣ S} →
                   forever-ty-map (η ⊙ φ) ≅ⁿ forever-ty-map η ⊙ forever-ty-map φ
eq forever-ty-map-⊙ _ = to-ω-limit-eq (λ _ → refl)

forever-ty-map-cong : {T S : Ty (constantly-ctx Γ)} {η φ : T ↣ S} → η ≅ⁿ φ → forever-ty-map η ≅ⁿ forever-ty-map φ
eq (forever-ty-map-cong 𝔢) _ = to-ω-limit-eq (λ _ → eq 𝔢 _)

module _ {T : Ty (constantly-ctx Γ)} where
  forever-tm-cong : {t s : Tm (constantly-ctx Γ) T} → t ≅ᵗᵐ s → forever-tm t ≅ᵗᵐ forever-tm s
  eq (forever-tm-cong t=s) γ = to-ω-limit-eq (λ n → eq t=s γ)

  unforever-tm-cong : {t s : Tm Γ (forever-ty T)} → t ≅ᵗᵐ s → unforever-tm t ≅ᵗᵐ unforever-tm s
  eq (unforever-tm-cong t=s) γ = cong (λ x → limit x _) (eq t=s γ)

forever-convert-tm : {T S : Ty (constantly-ctx Γ)} {η : T ↣ S} (t : Tm (constantly-ctx Γ) T) →
                     convert-tm (forever-ty-map η) (forever-tm t) ≅ᵗᵐ forever-tm (convert-tm η t)
eq (forever-convert-tm t) _ = to-ω-limit-eq (λ _ → refl)


--------------------------------------------------
-- Naturality of forever-ty

forever-ty-natural : (σ : Δ ⇒ Γ) {T : Ty (constantly-ctx Γ)} → (forever-ty T) [ σ ] ≅ᵗʸ forever-ty (T [ constantly-subst σ ])
limit (func (from (forever-ty-natural σ {T})) l) = limit l
limit-natural (func (from (forever-ty-natural σ {T})) l) = λ m≤n → trans (ty-cong T refl) (limit-natural l m≤n)
_↣_.naturality (from (forever-ty-natural σ {T})) = to-ω-limit-eq (λ _ → ty-cong T refl)
limit (func (to (forever-ty-natural σ {T})) l) = limit l
limit-natural (func (to (forever-ty-natural σ {T})) l) = λ m≤n → trans (ty-cong T refl) (limit-natural l m≤n)
_↣_.naturality (to (forever-ty-natural σ {T})) = to-ω-limit-eq (λ _ → ty-cong T refl)
eq (isoˡ (forever-ty-natural σ {T})) _ = to-ω-limit-eq (λ _ → refl)
eq (isoʳ (forever-ty-natural σ {T})) _ = to-ω-limit-eq (λ _ → refl)

forever-ty-natural-map : (σ : Γ ⇒ Δ) {T S : Ty (constantly-ctx Δ)} (η : T ↣ S) →
  forever-ty-map (ty-subst-map (constantly-subst σ) η) ⊙ from (forever-ty-natural σ)
    ≅ⁿ
  from (forever-ty-natural σ) ⊙ ty-subst-map σ (forever-ty-map η)
eq (forever-ty-natural-map σ η) _ = to-ω-limit-eq (λ _ → refl)

forever-ty-natural-id-map : {T : Ty (constantly-ctx Γ)} →
  forever-ty-map (ty-subst-id-from T ⊙ ty-subst-eq-subst-morph constantly-subst-id T) ⊙ from (forever-ty-natural (id-subst Γ))
    ≅ⁿ
  ty-subst-id-from (forever-ty T)
eq (forever-ty-natural-id-map {T = T}) _ = to-ω-limit-eq (λ _ → ty-id T)

forever-ty-natural-⊚-map : (τ : Δ ⇒ Θ) (σ : Γ ⇒ Δ) {T : Ty (constantly-ctx Θ)} →
  forever-ty-map (ty-subst-comp-from T (constantly-subst τ) (constantly-subst σ))
  ⊙ from (forever-ty-natural σ)
  ⊙ ty-subst-map σ (from (forever-ty-natural τ))
    ≅ⁿ
  forever-ty-map (ty-subst-eq-subst-morph (constantly-subst-⊚ τ σ) T)
  ⊙ from (forever-ty-natural (τ ⊚ σ))
  ⊙ ty-subst-comp-from (forever-ty T) τ σ
eq (forever-ty-natural-⊚-map τ σ {T}) _ = to-ω-limit-eq (λ _ → sym (ty-id T))

forever-ty-natural-subst-eq-map : {σ τ : Γ ⇒ Δ} {T : Ty (constantly-ctx Δ)} (ε : σ ≅ˢ τ) →
  from (forever-ty-natural τ) ⊙ ty-subst-eq-subst-morph ε (forever-ty T)
    ≅ⁿ
  forever-ty-map (ty-subst-eq-subst-morph (constantly-subst-cong ε) T) ⊙ from (forever-ty-natural σ)
eq (forever-ty-natural-subst-eq-map {T = T} _) _ = to-ω-limit-eq (λ _ → ty-cong T refl)

module _ (σ : Δ ⇒ Γ) {T : Ty (constantly-ctx Γ)} where
  forever-tm-natural : (t : Tm (constantly-ctx Γ) T) →
                       (forever-tm t) [ σ ]' ≅ᵗᵐ ι[ forever-ty-natural σ ] forever-tm (t [ constantly-subst σ ]')
  eq (forever-tm-natural t) _ = to-ω-limit-eq (λ _ → refl)

  unforever-tm-natural : (t : Tm Γ (forever-ty T)) →
                         (unforever-tm t) [ constantly-subst σ ]' ≅ᵗᵐ unforever-tm (ι⁻¹[ forever-ty-natural σ ] (t [ σ ]'))
  eq (unforever-tm-natural t) _ = refl


--------------------------------------------------
-- Forever as a DRA

instance
  constantly-ctx-is-functor : IsCtxFunctor constantly-ctx
  ctx-map {{constantly-ctx-is-functor}} = constantly-subst
  ctx-map-cong {{constantly-ctx-is-functor}} = constantly-subst-cong
  ctx-map-id {{constantly-ctx-is-functor}} = constantly-subst-id
  ctx-map-⊚ {{constantly-ctx-is-functor}} = constantly-subst-⊚

constantly-ctx-functor : CtxFunctor ★ ω
ctx-op constantly-ctx-functor = constantly-ctx
is-functor constantly-ctx-functor = constantly-ctx-is-functor

forever : DRA ω ★
ctx-functor forever = constantly-ctx-functor
⟨_∣_⟩ forever = forever-ty
dra-map forever = forever-ty-map
dra-map-cong forever = forever-ty-map-cong
dra-map-id forever = forever-ty-map-id
dra-map-⊙ forever = forever-ty-map-⊙
dra-natural forever = forever-ty-natural
dra-natural-map forever = forever-ty-natural-map
dra-natural-id-map forever = forever-ty-natural-id-map
dra-natural-⊚-map forever = forever-ty-natural-⊚-map
dra-natural-subst-eq-map forever = forever-ty-natural-subst-eq-map
dra-intro forever = forever-tm
dra-intro-cong forever = forever-tm-cong
dra-intro-natural forever = forever-tm-natural
dra-intro-convert forever = forever-convert-tm
dra-elim forever = unforever-tm
dra-elim-cong forever = unforever-tm-cong
dra-β forever = forever-ty-β
dra-η forever = forever-ty-η

forever-ty-cong : {T : Ty (constantly-ctx Γ)} {S : Ty (constantly-ctx Γ)} →
                  T ≅ᵗʸ S → forever-ty T ≅ᵗʸ forever-ty S
forever-ty-cong e = dra-cong forever e

module _ {T S : Ty (constantly-ctx Γ)} {T=S : T ≅ᵗʸ S} where
  forever-tm-ι : (s : Tm (constantly-ctx Γ) S) → ι[ forever-ty-cong T=S ] forever-tm s ≅ᵗᵐ forever-tm (ι[ T=S ] s)
  forever-tm-ι s = dra-intro-ι forever s

  unforever-tm-ι : (s : Tm Γ (forever-ty S)) → ι[ T=S ] unforever-tm s ≅ᵗᵐ unforever-tm (ι[ forever-ty-cong T=S ] s)
  unforever-tm-ι s = dra-elim-ι forever s
