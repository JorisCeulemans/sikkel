--------------------------------------------------
-- Context extension
--------------------------------------------------

open import Model.BaseCategory

module Model.CwF-Structure.ContextExtension {C : BaseCategory} where

open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.String
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.Helpers
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.ContextEquivalence
open import Model.CwF-Structure.Type
open import Model.CwF-Structure.Term

open BaseCategory C

infixl 15 _,,_
infixl 15 _,,_∈_

private
  variable
    Γ Δ Θ : Ctx C
    T S R : Ty Γ


-- Definition of the extension of a context Γ with a type T.
-- In MLTT, this would be written as Γ, x : T.
_,,_ : (Γ : Ctx C) (T : Ty Γ) → Ctx C
(Γ ,, T) ⟨ x ⟩ = Σ[ γ ∈ Γ ⟨ x ⟩ ] (T ⟨ x , γ ⟩)
(Γ ,, T) ⟪ f ⟫ [ γ , t ] = [ Γ ⟪ f ⟫ γ , T ⟪ f , refl ⟫ t ]
ctx-id (Γ ,, T) = to-Σ-ty-eq T (ctx-id Γ) (trans (ty-cong-2-1 T hom-idˡ) (ty-id T))
ctx-comp (Γ ,, T) = to-Σ-ty-eq T (ctx-comp Γ) (ty-cong-2-2 T hom-idʳ)

π : Γ ,, T ⇒ Γ
func π = proj₁
naturality π = refl

-- A term corresponding to the last variable in the context. In MLTT, this would be
-- written as Γ, x : T ⊢ x : T. Note that the type of the term is T [ π ] instead of
-- T because the latter is not a type in context Γ ,, T.
ξ : Tm (Γ ,, T) (T [ π ])
ξ ⟨ _ , [ _ , t ] ⟩' = t
naturality ξ _ refl = refl

-- In any cwf, there is by definition a one-to-one correspondence between substitutions
-- Δ ⇒ Γ ,, T and pairs of type Σ[ σ : Δ ⇒ Γ ] (Tm Δ (T [ σ ])). This is worked out
-- in the following functions.
ext-subst-to-subst : (Δ ⇒ Γ ,, T) → (Δ ⇒ Γ)
ext-subst-to-subst τ = π ⊚ τ

ext-subst-to-term : (τ : Δ ⇒ Γ ,, T) → Tm Δ (T [ π ⊚ τ ])
ext-subst-to-term {T = T} τ = ι⁻¹[ ty-subst-comp T π τ ] (ξ [ τ ]')

to-ext-subst : (T : Ty Γ) (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ]) → (Δ ⇒ Γ ,, T)
func (to-ext-subst T σ t) δ = [ func σ δ , t ⟨ _ , δ ⟩' ]
naturality (to-ext-subst {Δ = Δ} T σ t) {δ = δ} = to-Σ-ty-eq T (naturality σ)
                                                               (trans (ty-cong-2-1 T hom-idʳ) (naturality t _ refl))

syntax to-ext-subst T σ t = ⟨ σ , t ∈ T ⟩

to-ext-subst-syntax : {T : Ty Γ} (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ]) → (Δ ⇒ Γ ,, T)
to-ext-subst-syntax σ t = to-ext-subst _ σ t
infixl 4 to-ext-subst-syntax
syntax to-ext-subst-syntax σ t = σ ∷ˢ t

ctx-ext-subst-β₁ : (σ : Δ ⇒ Γ) (t : Tm Δ (T [ σ ])) → π ⊚ ⟨ σ , t ∈ T ⟩ ≅ˢ σ
eq (ctx-ext-subst-β₁ σ t) δ = refl

ctx-ext-subst-β₂ : (σ : Δ ⇒ Γ) (t : Tm Δ (T [ σ ])) →
                   ξ [ ⟨ σ , t ∈ T ⟩ ]' ≅ᵗᵐ ι[ ty-subst-cong-subst-2-1 T (ctx-ext-subst-β₁ σ t) ] t
eq (ctx-ext-subst-β₂ {T = T} σ t) _ = sym (strong-ty-id T)

ctx-ext-subst-η : (τ : Δ ⇒ Γ ,, T) → ⟨ π ⊚ τ , ext-subst-to-term τ ∈ T ⟩ ≅ˢ τ
eq (ctx-ext-subst-η τ) δ = refl

-- Some consequences of the properties above
ctx-ext-subst-cong-subst : {σ σ' : Δ ⇒ Γ} (ε : σ ≅ˢ σ') (t : Tm Δ (T [ σ' ])) →
                           ⟨ σ , ι[ ty-subst-cong-subst ε T ] t ∈ T ⟩ ≅ˢ ⟨ σ' , t ∈ T ⟩
eq (ctx-ext-subst-cong-subst {T = T} ε t) δ = to-Σ-ty-eq T (eq ε δ) (trans (ty-cong-2-1 T hom-idˡ) (ty-id T))

ctx-ext-subst-cong-tm : (σ : Δ ⇒ Γ) {t t' : Tm Δ (T [ σ ])} → t ≅ᵗᵐ t' → ⟨ σ , t ∈ T ⟩ ≅ˢ ⟨ σ , t' ∈ T ⟩
eq (ctx-ext-subst-cong-tm σ 𝒆) δ = cong [ _ ,_] (eq 𝒆 δ)

ctx-ext-subst-proj₂ : (σ : Δ ⇒ Γ) (t : Tm Δ (T [ σ ])) →
                      ext-subst-to-term ⟨ σ , t ∈ T ⟩ ≅ᵗᵐ ι[ ty-subst-cong-subst (ctx-ext-subst-β₁ σ t) T ] t
eq (ctx-ext-subst-proj₂ {Γ = Γ}{T = T} σ t) δ = sym (strong-ty-id T)

ctx-ext-subst-comp : (σ : Γ ⇒ Θ) (t : Tm Γ (T [ σ ])) (τ : Δ ⇒ Γ) →
                     ⟨ σ , t ∈ T ⟩ ⊚ τ ≅ˢ ⟨ σ ⊚ τ , ι⁻¹[ ty-subst-comp T σ τ ] (t [ τ ]') ∈ T ⟩
eq (ctx-ext-subst-comp σ t τ) δ = refl

-- Substitution of the last variable in context Γ ,, T with a term in Tm Γ T.
tm-to-subst : Tm Γ T → Γ ⇒ Γ ,, T
tm-to-subst {Γ = Γ}{T = T} t = ⟨ id-subst Γ , t [ id-subst Γ ]' ∈ T ⟩

_/v = tm-to-subst

/v-cong : {t t' : Tm Γ T} → t ≅ᵗᵐ t' → t /v ≅ˢ t' /v
/v-cong e = ctx-ext-subst-cong-tm _ (tm-subst-cong-tm _ e)

_⊹ : (σ : Δ ⇒ Γ) → Δ ,, T [ σ ] ⇒ Γ ,, T
_⊹ {Δ = Δ} {T = T} σ = ⟨ σ ⊚ π , ι⁻¹[ ty-subst-comp T σ π ] ξ ∈ T ⟩

⊹-π-comm : (σ : Δ ⇒ Γ) → π {T = T} ⊚ (σ ⊹) ≅ˢ σ ⊚ π
eq (⊹-π-comm σ) δ = refl

ty-eq-to-ext-subst : (Γ : Ctx C) {T : Ty Γ} {T' : Ty Γ} →
                     T ≅ᵗʸ T' → Γ ,, T ⇒ Γ ,, T'
ty-eq-to-ext-subst Γ {T = T}{T'} T=T' = ⟨ π , ι⁻¹[ ty-subst-cong-ty π T=T' ] ξ ∈ T' ⟩

π-ext-comp-ty-subst : (σ : Δ ⇒ Γ ) (t : Tm Δ (T [ σ ])) (S : Ty Γ) →
                      S [ π ] [ ⟨ σ , t ∈ T ⟩ ] ≅ᵗʸ S [ σ ]
π-ext-comp-ty-subst σ t S = transᵗʸ (ty-subst-comp S π ⟨ σ , t ∈ _ ⟩) (ty-subst-cong-subst (ctx-ext-subst-β₁ σ t) S)

ty-weaken-subst : (t : Tm Γ T) → S [ π ] [ t /v ] ≅ᵗʸ S
ty-weaken-subst t = transᵗʸ (π-ext-comp-ty-subst _ _ _) (ty-subst-id _)

-- Extending a context with two equivalent types leads to equivalent contexts.
,,-map : (T ↣ S) → (Γ ,, T ⇒ Γ ,, S)
,,-map η = π ∷ˢ convert-tm (ty-subst-map π η) ξ

,,-map-cong : {η φ : T ↣ S} → η ≅ⁿ φ → ,,-map η ≅ˢ ,,-map φ
,,-map-cong 𝔢 = ctx-ext-subst-cong-tm π (convert-tm-cong-trans (ty-subst-map-cong 𝔢))

,,-map-id : {T : Ty Γ} → ,,-map (id-trans T) ≅ˢ id-subst (Γ ,, T)
eq ,,-map-id _ = refl

,,-map-comp : (η : S ↣ T) (φ : R ↣ S) → ,,-map (η ⊙ φ) ≅ˢ ,,-map η ⊚ ,,-map φ
eq (,,-map-comp η φ) _ = refl

,,-cong : T ≅ᵗʸ S → Γ ,, T ≅ᶜ Γ ,, S
from (,,-cong T=S) = ,,-map (from T=S)
to (,,-cong T=S) = ,,-map (to T=S)
eq (isoˡ (,,-cong T=S)) [ γ , t ] = cong [ γ ,_] (eq (isoˡ T=S) t)
eq (isoʳ (,,-cong T=S)) [ γ , s ] = cong [ γ ,_] (eq (isoʳ T=S) s)

,,-map-π : (φ : T ↣ S) → π ⊚ ,,-map φ ≅ˢ π
,,-map-π φ = ctx-ext-subst-β₁ π _

ξ-convert : (φ : T ↣ S) → convert-tm (ty-subst-map π φ) ξ ≅ᵗᵐ ι⁻¹[ ty-subst-cong-subst-2-1 S (,,-map-π φ) ] (ξ [ ,,-map φ ]')
eq (ξ-convert {S = S} φ) _ = sym (strong-ty-id S)

,,-cong-ξ : (e : T ≅ᵗʸ S) →
  ξ [ from (,,-cong e) ]'
    ≅ᵗᵐ
  ι[ ty-subst-comp S π (from (,,-cong e)) ] ι[ ty-subst-cong-subst (,,-map-π (from e)) S ]  ι⁻¹[ ty-subst-cong-ty π e ] ξ
eq (,,-cong-ξ {S = S} e) _ = sym (strong-ty-id S)

,,-cong-ext-subst : (e : T ≅ᵗʸ S) {σ : Γ ⇒ Δ} {t : Tm Γ (T [ σ ])} →
                    from (,,-cong e) ⊚ to-ext-subst T σ t ≅ˢ to-ext-subst S σ (ι⁻¹[ ty-subst-cong-ty σ e ] t)
eq (,,-cong-ext-subst e) _ = refl

-- Context extension which includes a variable name
_,,_∈_ : (Γ : Ctx C) → String → (T : Ty Γ) → Ctx C
Γ ,, v ∈ T = Γ ,, T
