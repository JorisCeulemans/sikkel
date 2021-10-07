open import Model.BaseCategory

module Experimental.DependentTypes.Model.Boolean {C : BaseCategory} where

open import Data.Bool
open import Data.Product renaming (_,_ to [_,_])
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.CwF-Structure
open import Model.Type.Discrete
import Experimental.DependentTypes.Model.IdentityType as IdentityType
open IdentityType.Alternative2

private
  variable
    Γ : Ctx C


_/var0 : {T : Ty Γ} → Tm Γ T → (Γ ⇒ Γ ,, T)
t /var0 = term-to-subst t

bool-ind : (T : Ty (Γ ,, "x" ∈ Bool')) → Tm Γ (T [ true' /var0 ]) → Tm Γ (T [ false' /var0 ]) → Tm (Γ ,, Bool') T
bool-ind T t f ⟨ x , [ γ , false ] ⟩' = f ⟨ x , γ ⟩'
bool-ind T t f ⟨ x , [ γ , true  ] ⟩' = t ⟨ x , γ ⟩'
Tm.naturality (bool-ind T t f) {γy = [ γy , false ]} {γx = [ γx , false ]} ρ eγ = trans (ty-cong T refl) (Tm.naturality f ρ (cong proj₁ eγ))
Tm.naturality (bool-ind T t f) {γy = [ γy , true  ]} {γx = [ γx , true  ]} ρ eγ = trans (ty-cong T refl) (Tm.naturality t ρ (cong proj₁ eγ))

{-
-- Examples hopefully become a lot easier in the deeply-embedded layer, from
--   which they can be interpreted in the model.

not' : Tm Γ Bool' → Tm Γ Bool'
not' b = if' b then' false' else' true'

not-involutive : {Γ : Ctx C} → Tm (Γ ,, Bool') (Id [ (ι[ by-naturality ] not' (not' (db-varι 0))) /var0 ])
not-involutive = bool-ind _ case-true case-false
  where
    open import Reflection.SubstitutionSequence
    case-true : Tm _ _ -- ((Id [(ι[ by-naturality ] not' (not' (db-varι 0))) /var0 ]) [ true' /var0 ])
    case-true = ι[ ty-subst-seq-cong ((_ /var0) ∷ (true' /var0) ◼)
                                     (π ∷ (refl' ⊚ (true' /var0)) ◼)
                                     Id
                                     (record { eq = λ _ → refl }) ]
                (ξ [ refl' ⊚ (true' /var0) ]')

    case-false : Tm _ _ -- ((Id [(ι[ by-naturality ] not' (not' (db-varι 0))) /var0 ]) [ false' /var0 ])
    case-false = ι[ ty-subst-seq-cong ((_ /var0) ∷ (false' /var0) ◼)
                                      (π ∷ (refl' ⊚ (false' /var0)) ◼)
                                      Id
                                      (record { eq = λ _ → refl }) ]
                 (ξ [ refl' ⊚ (false' /var0) ]')
-}
