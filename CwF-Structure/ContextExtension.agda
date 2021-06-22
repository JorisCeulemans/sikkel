--------------------------------------------------
-- Context extension
--------------------------------------------------

open import Categories

module CwF-Structure.ContextExtension {C : Category} where

open import Data.Fin
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding ([_]; _++_)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.String hiding (_++_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms

open Category C

infixl 15 _,,_
infixl 15 _,,_∈_

private
  variable
    n : ℕ
    Γ Δ Θ : Ctx C
    T S : Ty Γ


-- Definition of the extension of a context Γ with a type T.
-- In MLTT, this would be written as Γ, x : T.
_,,_ : (Γ : Ctx C) (T : Ty Γ) → Ctx C
(Γ ,, T) ⟨ x ⟩ = Σ[ γ ∈ Γ ⟨ x ⟩ ] (T ⟨ x , γ ⟩)
(Γ ,, T) ⟪ f ⟫ [ γ , t ] = [ Γ ⟪ f ⟫ γ , T ⟪ f , refl ⟫ t ]
ctx-id (Γ ,, T) = to-Σ-ty-eq T (ctx-id Γ) (trans (ty-cong-2-1 T hom-idˡ) (ty-id T))
ctx-comp (Γ ,, T) = to-Σ-ty-eq T (ctx-comp Γ) (ty-cong-2-2 T hom-idʳ)


--------------------------------------------------
-- Definition of a telescope in a context of a certain length

-- A value of Telescope Γ n ℓs is a list of types Ts = [] ∷ T1 ∷ T2 ∷ ... ∷ Tn so that
-- T1 is valid in Γ, T2 is valid in Γ ,, T1 etc. and hence Γ ,, T1 ,, T2 ,, ... ,, Tn
-- is a valid context written as Γ ++ Ts.
data Telescope (Γ : Ctx C) : (n : ℕ) → Set₁
_++_ : (Γ : Ctx C) {n : ℕ} → Telescope Γ n → Ctx C

data Telescope Γ where
  []  : Telescope Γ 0
  _∷_ : ∀ {n} (Ts : Telescope Γ n) → Ty (Γ ++ Ts) → Telescope Γ (suc n)

Γ ++ []       = Γ
Γ ++ (Ts ∷ T) = (Γ ++ Ts) ,, T

dropTel : (x : Fin (suc n)) → Telescope Γ n → Telescope Γ (n ℕ-ℕ x)
dropTel zero Ts = Ts
dropTel (suc x) (Ts ∷ T) = dropTel x Ts

πs : (x : Fin (suc n)) → (Ts : Telescope Γ n) → Γ ++ Ts ⇒ Γ ++ dropTel x Ts
func (πs zero Ts) v = v
func (πs (suc x) (Ts ∷ T)) [ v , _ ] = func (πs x Ts) v
naturality (πs zero Ts) = refl
naturality (πs (suc x) (Ts ∷ T)) = naturality (πs x Ts)

π : Γ ,, T ⇒ Γ
π {T = T} = πs (suc zero) ([] ∷ T)

lookupTel : (x : Fin n) → (Ts : Telescope Γ n) → Ty (Γ ++ dropTel (suc x) Ts)
lookupTel zero (Ts ∷ T) = T
lookupTel (suc x) (Ts ∷ T) = lookupTel x Ts

ξs : (x : Fin n) → (Ts : Telescope Γ n) → Tm (Γ ++ Ts) (lookupTel x Ts [ πs (suc x) Ts ])
ξs zero (Ts ∷ T) ⟨ _ , [ _ , v ] ⟩' = v
naturality (ξs zero (Ts ∷ T)) f refl = refl
ξs (suc x) (Ts ∷ T) ⟨ _ , [ vs , _ ] ⟩' = ξs x Ts ⟨ _ , vs ⟩'
naturality (ξs (suc x) (Ts ∷ T)) f eγ = trans (ty-cong (lookupTel x Ts) refl) (naturality (ξs x Ts) f (cong proj₁ eγ))

-- A term corresponding to the last variable in the context. In MLTT, this would be
-- written as Γ, x : T ⊢ x : T. Note that the type of the term is T [ π ] instead of
-- T because the latter is not a type in context Γ ,, T.
ξ : Tm (Γ ,, T) (T [ π ])
ξ {T = T} = ξs zero ([] ∷ T)

-- In any cwf, there is by definition a one-to-one correspondence between substitutions
-- Δ ⇒ Γ ,, T and pairs of type Σ[ σ : Δ ⇒ Γ ] (Tm Δ (T [ σ ])). This is worked out
-- in the following functions.
ext-subst-to-subst : Δ ⇒ Γ ,, T → Δ ⇒ Γ
ext-subst-to-subst τ = π ⊚ τ

ext-subst-to-term : (τ : Δ ⇒ Γ ,, T) → Tm Δ (T [ π ⊚ τ ])
ext-subst-to-term {T = T} τ = ι⁻¹[ ty-subst-comp T π τ ] (ξ [ τ ]')

to-ext-subst : (T : Ty Γ) (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ]) → Δ ⇒ Γ ,, T
func (to-ext-subst T σ t) δ = [ func σ δ , t ⟨ _ , δ ⟩' ]
naturality (to-ext-subst {Δ = Δ} T σ t) {δ = δ} = to-Σ-ty-eq T (naturality σ)
                                                               (trans (ty-cong-2-1 T hom-idʳ) (naturality t _ refl))

syntax to-ext-subst T σ t = ⟨ σ , t ∈ T ⟩

ctx-ext-subst-proj₁ : (σ : Δ ⇒ Γ) (t : Tm Δ (T [ σ ])) → π ⊚ ⟨ σ , t ∈ T ⟩ ≅ˢ σ
eq (ctx-ext-subst-proj₁ σ t) δ = refl

ctx-ext-subst-proj₂ : (σ : Δ ⇒ Γ) (t : Tm Δ (T [ σ ])) →
                      ext-subst-to-term ⟨ σ , t ∈ T ⟩ ≅ᵗᵐ ι[ ty-subst-cong-subst (ctx-ext-subst-proj₁ σ t) T ] t
eq (ctx-ext-subst-proj₂ {Γ = Γ}{T = T} σ t) δ = sym (strong-ty-id T)

ctx-ext-subst-η : (τ : Δ ⇒ Γ ,, T) → ⟨ π ⊚ τ , ext-subst-to-term τ ∈ T ⟩ ≅ˢ τ
eq (ctx-ext-subst-η τ) δ = refl

ctx-ext-subst-comp : (σ : Γ ⇒ Θ) (t : Tm Γ (T [ σ ])) (τ : Δ ⇒ Γ) →
                     ⟨ σ , t ∈ T ⟩ ⊚ τ ≅ˢ ⟨ σ ⊚ τ , ι⁻¹[ ty-subst-comp T σ τ ] (t [ τ ]') ∈ T ⟩
eq (ctx-ext-subst-comp σ t τ) δ = refl

-- Substitution of the last variable in context Γ ,, T with a term in Tm Γ T.
term-to-subst : Tm Γ T → Γ ⇒ Γ ,, T
term-to-subst {Γ = Γ}{T = T} t = ⟨ id-subst Γ , ι[ ty-subst-id T ] t ∈ T ⟩

_⊹ : (σ : Δ ⇒ Γ) → Δ ,, T [ σ ] ⇒ Γ ,, T
_⊹ {Δ = Δ} {T = T} σ = ⟨ σ ⊚ π , ι⁻¹[ ty-subst-comp T σ π ] ξ ∈ T ⟩

⊹-π-comm : (σ : Δ ⇒ Γ) → π {T = T} ⊚ (σ ⊹) ≅ˢ σ ⊚ π
eq (⊹-π-comm σ) δ = refl

ty-eq-to-ext-subst : (Γ : Ctx C) {T : Ty Γ} {T' : Ty Γ} →
                     T ≅ᵗʸ T' → Γ ,, T ⇒ Γ ,, T'
ty-eq-to-ext-subst Γ {T = T}{T'} T=T' = ⟨ π , ι⁻¹[ ty-subst-cong-ty π T=T' ] ξ ∈ T' ⟩

{-
-- These functions are currently not used anywhere. We keep them in case we need them
-- in the future.
π-ext-comp-ty-subst : (σ : Δ ⇒ Γ ) (t : Tm Δ (T [ σ ])) (S : Ty Γ) →
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
_,,_∈_ : (Γ : Ctx C) → String → (T : Ty Γ) → Ctx C
Γ ,, v ∈ T = Γ ,, T
