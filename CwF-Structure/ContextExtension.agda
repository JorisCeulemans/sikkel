{-# OPTIONS --without-K #-}

--------------------------------------------------
-- Context extension
--------------------------------------------------

open import Categories

module CwF-Structure.ContextExtension {C : Category} where

open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.String
open import Level
open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality
  hiding ([_]; naturality; setoid) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms

open Category C

infixl 15 _,,_
infixl 15 _,,_∈_

private
  variable
    ℓc ℓt ℓt' : Level
    Γ Δ Θ : Ctx C ℓ
    T S : Ty Γ ℓ


-- Definition of the extension of a context Γ with a type T.
-- In MLTT, this would be written as Γ, x : T.
_,,_ : (Γ : Ctx C ℓc) (T : Ty Γ ℓt) → Ctx C (ℓc ⊔ ℓt)
Setoid.Carrier (setoid (Γ ,, T) x) = Σ[ γ ∈ Γ ⟨ x ⟩ ] (T ⟨ x , γ ⟩)
Setoid._≈_ (setoid (Γ ,, T) x) [ γ1 , t1 ] [ γ2 , t2 ] = Σ[ eγ ∈ γ1 ≈[ Γ ]≈ γ2 ] (ctx-element-subst T eγ t1 ≈⟦ T ⟧≈ t2)
Relation.Binary.IsEquivalence.refl (Setoid.isEquivalence (setoid (Γ ,, T) x)) {[ γ , t ]} = [ ctx≈-refl Γ , ty≈-trans T (morph-hom-cong T ≡-refl) (morph-id T t) ]
Relation.Binary.IsEquivalence.sym (Setoid.isEquivalence (setoid (Γ ,, T) x)) [ eγ , et ] = [ ctx≈-sym Γ eγ ,
  ty≈-trans T (morph-cong T hom-id _ (ty≈-sym T et))
              (ty≈-trans T (morph-hom-cong-2-1 T hom-idˡ)
                           (morph-id T _)) ]
Relation.Binary.IsEquivalence.trans (Setoid.isEquivalence (setoid (Γ ,, T) x)) [ eγ12 , et12 ] [ eγ23 , et23 ] =
  [ ctx≈-trans Γ eγ12 eγ23
  , ty≈-trans T (ty≈-sym T (morph-hom-cong-2-1 T hom-idˡ))
                (ty≈-trans T (morph-cong T hom-id _ et12)
                             et23)
  ]
rel (Γ ,, T) f [ γ , t ] = [ Γ ⟪ f ⟫ γ , strict-morph T f γ t ]
rel-cong (Γ ,, T) f [ eγ , et ] = [ rel-cong Γ f eγ ,
  ty≈-trans T (morph-hom-cong-2-2 T (≡-trans hom-idʳ (≡-sym hom-idˡ)))
              (morph-cong T f _ et) ]
rel-id (Γ ,, T) [ γ , t ] = [ rel-id Γ γ ,
  ty≈-trans T (morph-hom-cong-2-1 T hom-idˡ)
              (morph-id T t) ]
rel-comp (Γ ,, T) f g [ γ , t ] = [ rel-comp Γ f g γ , morph-hom-cong-2-2 T hom-idʳ ]

π : Γ ,, T ⇒ Γ
func π = proj₁
func-cong π [ eγ , _ ] = eγ
naturality (π {Γ = Γ}) _ = ctx≈-refl Γ

-- A term corresponding to the last variable in the context. In MLTT, this would be
-- written as Γ, x : T ⊢ x : T. Note that the type of the term is T [ π ] instead of
-- T because the latter is not a type in context Γ ,, T.
ξ : Tm (Γ ,, T) (T [ π ])
term ξ _ = proj₂
naturality (ξ {T = T}) f [ eγ , et ] = ty≈-trans T (ty≈-sym T (morph-hom-cong-2-1 T hom-idʳ)) et

-- In any cwf, there is by definition a one-to-one correspondence between substitutions
-- Δ ⇒ Γ ,, T and pairs of type Σ[ σ : Δ ⇒ Γ ] (Tm Δ (T [ σ ])). This is worked out
-- in the following functions.
ext-subst-to-subst : Δ ⇒ Γ ,, T → Δ ⇒ Γ
ext-subst-to-subst τ = π ⊚ τ

ext-subst-to-term : (τ : Δ ⇒ Γ ,, T) → Tm Δ (T [ π ⊚ τ ])
ext-subst-to-term {T = T} τ = ι⁻¹[ ty-subst-comp T π τ ] (ξ [ τ ]')

to-ext-subst : (T : Ty Γ ℓ) (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ]) → Δ ⇒ Γ ,, T
func (to-ext-subst T σ t) δ = [ func σ δ , t ⟨ _ , δ ⟩' ]
func-cong (to-ext-subst {Δ = Δ} T σ t) eδ = [ func-cong σ eδ , ty≈-trans T (morph-hom-cong T ≡-refl) (naturality t hom-id (ctx≈-trans Δ (rel-id Δ _) eδ)) ]
naturality (to-ext-subst {Δ = Δ} T σ t) δ = [ naturality σ δ , ty≈-trans T (morph-hom-cong-2-1 T hom-idʳ)
                                                                           (naturality t _ (ctx≈-refl Δ)) ]

syntax to-ext-subst T σ t = ⟨ σ , t ∈ T ⟩

ctx-ext-subst-proj₁ : (σ : Δ ⇒ Γ) (t : Tm Δ (T [ σ ])) → π ⊚ ⟨ σ , t ∈ T ⟩ ≅ˢ σ
eq (ctx-ext-subst-proj₁ {Γ = Γ} σ t) δ = ctx≈-refl Γ

ctx-ext-subst-proj₂ : (σ : Δ ⇒ Γ) (t : Tm Δ (T [ σ ])) →
                      ext-subst-to-term ⟨ σ , t ∈ T ⟩ ≅ᵗᵐ ι[ ty-subst-cong-subst (ctx-ext-subst-proj₁ σ t) T ] t
eq (ctx-ext-subst-proj₂ {Γ = Γ}{T = T} σ t) δ = ty≈-sym T (
  begin
    T ⟪ hom-id , ctx≈-trans Γ (rel-id Γ (func σ δ)) _ ⟫ (t ⟨ _ , δ ⟩')
  ≈⟨ morph-hom-cong T ≡-refl ⟩
    T ⟪ hom-id , _ ⟫ (t ⟨ _ , δ ⟩')
  ≈⟨ morph-id T _ ⟩
    t ⟨ _ , δ ⟩' ∎)
  where open SetoidReasoning (type T _ (func σ δ))

ctx-ext-subst-η : (τ : Δ ⇒ Γ ,, T) → ⟨ π ⊚ τ , ext-subst-to-term τ ∈ T ⟩ ≅ˢ τ
eq (ctx-ext-subst-η {Γ = Γ}{T = T} τ) δ = [ ctx≈-refl Γ , ty≈-trans T (morph-hom-cong T ≡-refl) (morph-id T _) ]

ctx-ext-subst-comp : (σ : Γ ⇒ Θ) (t : Tm Γ (T [ σ ])) (τ : Δ ⇒ Γ) →
                     ⟨ σ , t ∈ T ⟩ ⊚ τ ≅ˢ ⟨ σ ⊚ τ , ι⁻¹[ ty-subst-comp T σ τ ] (t [ τ ]') ∈ T ⟩
eq (ctx-ext-subst-comp {Θ = Θ}{T = T} σ t τ) δ = [ ctx≈-refl Θ , ty≈-trans T (morph-hom-cong T ≡-refl) (morph-id T _) ]

-- Substitution of the last variable in context Γ ,, T with a term in Tm Γ T.
term-to-subst : Tm Γ T → Γ ⇒ Γ ,, T
term-to-subst {Γ = Γ}{T = T} t = ⟨ id-subst Γ , ι[ ty-subst-id T ] t ∈ T ⟩

_⊹ : (σ : Δ ⇒ Γ) → Δ ,, T [ σ ] ⇒ Γ ,, T
_⊹ {Δ = Δ} {T = T} σ = ⟨ σ ⊚ π , ι⁻¹[ ty-subst-comp T σ π ] ξ ∈ T ⟩

⊹-π-comm : (σ : Δ ⇒ Γ) → π {T = T} ⊚ (σ ⊹) ≅ˢ σ ⊚ π
eq (⊹-π-comm {Γ = Γ} σ) δ = ctx≈-refl Γ

ty-eq-to-ext-subst : (Γ : Ctx C ℓc) {T : Ty Γ ℓt} {T' : Ty Γ ℓt'} →
                     T ≅ᵗʸ T' → Γ ,, T ⇒ Γ ,, T'
ty-eq-to-ext-subst Γ {T = T}{T'} T=T' = ⟨ π , ι⁻¹[ ty-subst-cong-ty π T=T' ] ξ ∈ T' ⟩

{-
-- These functions are currently not used anywhere. We keep them in case we need them
-- in the future.
π-ext-comp-ty-subst : (σ : Δ ⇒ Γ ) (t : Tm Δ (T [ σ ])) (S : Ty Γ ℓ r) →
                      S [ π ] [ ⟨ σ , t ∈ T ⟩ ] ≅ᵗʸ S [ σ ]
π-ext-comp-ty-subst {T = T} σ t S =
  S [ π ] [ ⟨ σ , t ∈ T ⟩ ]
    ≅⟨ ty-subst-comp S π ⟨ σ , t ∈ T ⟩ ⟩
  S [ π ⊚ ⟨ σ , t ∈ T ⟩ ]
    ≅⟨ ty-subst-cong-subst (ctx-ext-subst-proj₁ σ t) S ⟩
  S [ σ ] ∎
  where open ≅ᵗʸ-Reasoning

_⌈_⌋ : Tm (Γ ,, T) (S [ π ]) → Tm Γ T → Tm Γ S
_⌈_⌋ {Γ = Γ}{T = T}{S = S} s t = ι⁻¹[ proof ] (s [ term-to-subst t ]')
  where
    open ≅ᵗʸ-Reasoning
    proof : S [ π ] [ term-to-subst t ] ≅ᵗʸ S
    proof =
      S [ π ] [ term-to-subst t ]
        ≅⟨ π-ext-comp-ty-subst (id-subst Γ) (ι[ ty-subst-id T ] t) S ⟩
      S [ id-subst Γ ]
        ≅⟨ ty-subst-id S ⟩
      S ∎
-}

-- Context extension which includes a variable name
_,,_∈_ : (Γ : Ctx C ℓc) → String → (T : Ty Γ ℓt) → Ctx C (ℓc ⊔ ℓt)
Γ ,, v ∈ T = Γ ,, T
