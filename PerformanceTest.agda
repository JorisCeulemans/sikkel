open import Categories

module PerformanceTest {C : Category} where

open import Data.Bool
open import Level

open import CwF-Structure
open import Types.Functions
open import Types.Discrete
open import Types.Products
open import Types.Instances
open import Reflection.Naturality.TypeOperations
open import Reflection.Tactic.Naturality
open import Reflection.Tactic.Lambda

private
  variable
    ℓ ℓ' : Level
    Γ : Ctx C ℓ


postulate
  unop : UnaryTypeOp {C = C} (λ Γ → Γ) (λ _ ℓ → ℓ)
  instance
    unop-natural : IsUnaryNatural unop
  unop⊛ : {T : Ty Γ ℓ} {S : Ty Γ ℓ'} → Tm Γ (unop (T ⇛ S)) → Tm Γ (unop T) → Tm Γ (unop S)
  return-unop : {T : Ty Γ ℓ} → Tm Γ T → Tm Γ (unop T)
  fakelöb : {T : Ty Γ ℓ} → Tm Γ (unop T ⇛ T) → Tm Γ T

not-func : Tm Γ (Bool' ⇛ Bool')
not-func = discr-func not

test1 : Tm Γ ((Bool' ⇛ Bool') ⇛ Bool' ⇛ Bool')
test1 = lamι (Bool' ⇛ Bool')
             (lamι Bool'
                   (app (db-varι 1) (app not-func (db-varι 0))))

test2 : Tm Γ ((Bool' ⇛ Bool' ⇛ Bool') ⇛ Bool' ⇛ Bool' ⇛ Bool')
test2 = lamι (Bool' ⇛ Bool' ⇛ Bool')
             (lamι Bool'
                   (lamι Bool'
                         (app (app (db-varι 2) (db-varι 0)) (db-varι 1))))

test3 : Tm Γ (((unop Bool' ⇛ Bool') ⇛ Bool' ⇛ Bool') ⇛ (unop Bool' ⇛ Bool') ⇛ Bool' ⇛ Bool')
test3 = lamι ((unop Bool' ⇛ Bool') ⇛ Bool' ⇛ Bool')
             (lamι (unop Bool' ⇛ Bool')
                   (lamι Bool'
                         (app (app (db-varι 2) (db-varι 1)) (app not-func (db-varι 0)))))

test4 : Tm Γ ((Bool' ⊠ unop Bool' ⇛ Bool') ⇛ Bool' ⇛ Bool')
test4 = fakelöb (lamι (unop (((Bool' ⊠ unop Bool') ⇛ Bool') ⇛ Bool' ⇛ Bool'))
                      (lamι ((Bool' ⊠ unop Bool') ⇛ Bool')
                            (lamι Bool'
                                  (app (db-varι 1) (pair (db-varι 0)
                                                      (unop⊛ (unop⊛ (db-varι 2) (return-unop (db-varι 1))) (return-unop (db-varι 0))))))))
