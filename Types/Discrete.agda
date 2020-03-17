module Types.Discrete where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Unit using (⊤; tt)
open import Function hiding (_⟨_⟩_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms

--------------------------------------------------
-- Discrete types
--------------------------------------------------

Discr : (A : Set 0ℓ) {Γ : Ctx 0ℓ} → Ty Γ
type (Discr A) = λ _ _ → A
morph (Discr A) = λ _ _ → id
morph-id (Discr A) = λ _ → subst-const _ _
morph-comp (Discr A) = λ _ _ _ → subst-const _ _

discr : {A : Set 0ℓ} {Γ : Ctx 0ℓ} → A → Tm Γ (Discr A)
term (discr a) = λ _ _ → a
naturality (discr a) = λ _ _ → refl

undiscr : {A : Set 0ℓ} → Tm ◇ (Discr A) → A
undiscr t = t ⟨ 0 , lift tt ⟩'

undiscr-discr : {A : Set 0ℓ} (a : A) → undiscr (discr a) ≡ a
undiscr-discr a = refl

discr-undiscr : {A : Set 0ℓ} (t : Tm ◇ (Discr A)) → discr (undiscr t) ≡ t
discr-undiscr t = cong₂-d MkTm
                          (sym (funext λ n → funext λ γ → t ⟪ z≤n , lift tt ⟫'))
                          (funextI (funextI (funext λ ineq → funext λ _ → uip _ _)))

Unit' : {Γ : Ctx 0ℓ} → Ty Γ
Unit' = Discr ⊤

tt' : {Γ : Ctx 0ℓ} → Tm Γ Unit'
tt' = discr tt

Bool' : {Γ : Ctx 0ℓ} → Ty Γ
Bool' = Discr Bool

true' : {Γ : Ctx 0ℓ} → Tm Γ Bool'
true' = discr true

false' : {Γ : Ctx 0ℓ} → Tm Γ Bool'
false' = discr false

if'_then'_else'_ : {Γ : Ctx 0ℓ} {T : Ty Γ} → Tm Γ Bool' → Tm Γ T → Tm Γ T → Tm Γ T
term (if' c then' t else' f) = λ n γ → if c ⟨ n , γ ⟩' then t ⟨ n , γ ⟩' else f ⟨ n , γ ⟩'
naturality (if'_then'_else'_ {Γ = Γ} c t f) {m} {n} ineq γ with c ⟨ m , Γ ⟪ ineq ⟫ γ ⟩' | c ⟨ n , γ ⟩' | c ⟪ ineq , γ ⟫'
naturality (if'_then'_else'_ {Γ} c t f) {m} {n} ineq γ | false | .false | refl = f ⟪ ineq , γ ⟫'
naturality (if'_then'_else'_ {Γ} c t f) {m} {n} ineq γ | true  | .true  | refl = t ⟪ ineq , γ ⟫'

β-Bool'-true : {Γ : Ctx 0ℓ} {T : Ty Γ} (t t' : Tm Γ T) →
               if' true' then' t else' t' ≡ t
β-Bool'-true t t' = refl

β-Bool'-false : {Γ : Ctx 0ℓ} {T : Ty Γ} (t t' : Tm Γ T) →
               if' false' then' t else' t' ≡ t'
β-Bool'-false t t' = refl

Nat' : {Γ : Ctx 0ℓ} → Ty Γ
Nat' = Discr ℕ

zero' : {Γ : Ctx 0ℓ} → Tm Γ Nat'
zero' = discr zero

suc' : {Γ : Ctx 0ℓ} → Tm Γ Nat' → Tm Γ Nat'
term (suc' t) = λ n γ → suc (t ⟨ n , γ ⟩')
naturality (suc' t) = λ m≤n γ → cong suc (naturality t m≤n γ)
