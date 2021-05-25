--------------------------------------------------
-- Definition and use of telescopes in a context
--------------------------------------------------

open import Categories

module CwF-Structure.Telescopes {C : Category} where

open import Data.Fin
open import Data.Nat hiding (_⊔_)
open import Data.Vec hiding ([_]; _++_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality) renaming (subst to transport)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])

open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension

private
  variable
    Γ : Ctx C
    n : ℕ


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

lookupTel : (x : Fin n) → (Ts : Telescope Γ n) → Ty (Γ ++ dropTel (suc x) Ts)
lookupTel zero (Ts ∷ T) = T
lookupTel (suc x) (Ts ∷ T) = lookupTel x Ts

-- πs : (x : Fin (suc n)) → (Ts : Telescope Γ n) → Γ ++ Ts ⇒ Γ ++ dropTel x Ts
-- func (πs zero Ts) v = v
-- func (πs (suc x) (Ts ∷ T)) [ v , _ ] = func (πs x Ts) v
-- naturality (πs zero Ts) = refl
-- naturality (πs (suc x) (Ts ∷ T)) = naturality (πs x Ts)

πs : (x : Fin (suc n)) → (Ts : Telescope Γ n) → Γ ++ Ts ⇒ Γ ++ dropTel x Ts
πs zero Ts = id-subst _
πs (suc zero) (Ts ∷ T) = π
πs (suc (suc x)) (Ts ∷ T) = πs (suc x) Ts ⊚ π

ξs : (x : Fin n) → (Ts : Telescope Γ n) → Tm (Γ ++ Ts) (lookupTel x Ts [ πs (suc x) Ts ])
ξs zero (Ts ∷ T) ⟨ _ , [ _ , v ] ⟩' = v
naturality (ξs zero (Ts ∷ T)) f refl = refl
ξs (suc x) (Ts ∷ T) ⟨ _ , [ vs , _ ] ⟩' = ξs x Ts ⟨ _ , vs ⟩'
naturality (ξs (suc x) (Ts ∷ T)) f eγ = trans (ty-cong (lookupTel x Ts) refl) (naturality (ξs x Ts) f (cong proj₁ eγ))


var-type′ : (Ts : Telescope Γ n) (x : Fin n) → Ty (Γ ++ Ts)
var-type′ Ts x = lookupTel x Ts [ πs (suc x) Ts ]

prim-var′ : (Ts : Telescope Γ n) (x : Fin n) → Tm (Γ ++ Ts) (var-type′ Ts x)
prim-var′ Ts x = ξs x Ts

--------------------------------------------------
-- A telescope of length n can be used to denote variables
-- as de Bruijn indices using elements of type Fin n.

var-type : (Ts : Telescope Γ n) (x : Fin n) → Ty (Γ ++ Ts)
var-type (Ts ∷ T) zero    = T [ π ]
var-type (Ts ∷ T) (suc x) = (var-type Ts x) [ π ]

-- Not for direct use. See Reflection.Tactic.Telescopes.
prim-var : (Ts : Telescope Γ n) (x : Fin n) → Tm (Γ ++ Ts) (var-type Ts x)
prim-var (Ts ∷ T) zero    = ξ
prim-var (Ts ∷ T) (suc x) = (prim-var Ts x) [ π ]'


--------------------------------------------------
-- Using a telescope to define weakening of types and terms.

max-πs : (Ts : Telescope Γ n) → Γ ++ Ts ⇒ Γ
max-πs []       = id-subst _
max-πs ([] ∷ _) = π
max-πs ((Ts ∷ T) ∷ _) = max-πs (Ts ∷ T) ⊚ π

weaken-type : {Γ : Ctx C} {n : ℕ} (Ts : Telescope Γ n) →
              Ty Γ → Ty (Γ ++ Ts)
weaken-type Ts S = S [ max-πs Ts ]

-- Not for direct use. See Reflection.Tactic.Telescopes.
weaken-term : {Γ : Ctx C} {n : ℕ} (Ts : Telescope Γ n) {S : Ty Γ} →
              Tm Γ S → Tm (Γ ++ Ts) (weaken-type Ts S)
weaken-term Ts s = s [ max-πs Ts ]'
