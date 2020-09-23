module Reflection.NaturalityTactic where

--------------------------------------------------
-- Definition of tactic by-naturality

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; filter)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Reflection hiding (lam; var)
open import Reflection.Argument using (_⟨∷⟩_; unArg)
open import Reflection.TypeChecking.Monad.Syntax using (_<$>_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Helpers
open import CwF-Structure
open import Reflection.Naturality hiding (reduce)

get-args : Type → Maybe (Term × Term)
get-args (def _ xs) = go xs
  where
  go : List (Arg Term) → Maybe (Term × Term)
  go (vArg x ∷ vArg y ∷ []) = just (x , y)
  go (x ∷ xs)               = go xs
  go _                      = nothing
get-args _ = nothing

breakTC : ∀ {a} {A : Set a} → (A → TC Bool) → List A → TC (List A × List A)
breakTC p []       = return ([] , [])
breakTC p (x ∷ xs) = p x >>= λ
  { false → (λ (ys , zs) → (x ∷ ys , zs)) <$> breakTC p xs
  ; true  → return ([] , x ∷ xs)
  }

is-visible : ∀ {a} {A : Set a} → Arg A → Bool
is-visible (arg (arg-info visible r) x) = true
is-visible (arg (arg-info hidden r) x) = false
is-visible (arg (arg-info instance′ r) x) = false

is-arg-semtype : Arg Term → TC Bool
is-arg-semtype a = inferType (unArg a) >>= λ
  { (def (quote Ty) _) → return true
  ; _ → return false
  }

{-# TERMINATING #-}
construct-exp : Term → TC Term
construct-exp (def (quote _[_]) args) = breakTC is-arg-semtype args >>= λ
  { (_ , (ty ⟨∷⟩ subst ⟨∷⟩ [])) → do
      ty-exp ← construct-exp ty
      return (con (quote sub) (vArg ty-exp ∷ vArg subst ∷ []))
  ; _ → typeError (strErr "Illegal substitution." ∷ [])
  }
construct-exp (def op args) = breakTC is-arg-semtype (filter (dec-from-bool is-visible) args) >>= λ
  { (others , []) → return (con (quote nul) (vArg (def op others) ∷ []))
  ; (others , (ty1 ⟨∷⟩ [])) → do
      ty1-exp ← construct-exp ty1
      return (con (quote un) (vArg (def op others) ∷ vArg ty1-exp ∷ []))
  ; (others , (ty1 ⟨∷⟩ ty2 ⟨∷⟩ [])) → do
      ty1-exp ← construct-exp ty1
      ty2-exp ← construct-exp ty2
      return (con (quote bin) (vArg (def op others) ∷ vArg ty1-exp ∷ vArg ty2-exp ∷ []))
  ; _ → typeError (strErr "No type operator recognized." ∷ [])
  }
construct-exp (meta m args) = debugPrint "vtac" 5 (strErr "Blocking on meta" ∷ termErr (meta m args) ∷ strErr "in construct-exp." ∷ []) >> blockOnMeta m
construct-exp ty = typeError (strErr "The naturality tactic does not work for the type" ∷ termErr ty ∷ [])

by-naturality-macro : Term → TC ⊤
by-naturality-macro hole = do
  goal ← inferType hole >>= normalise
  debugPrint "vtac" 5 (strErr "naturality solver called, goal:" ∷ termErr goal ∷ [])
  just (lhs , rhs) ← return (get-args goal)
    where nothing → typeError (termErr goal ∷ strErr "is not a type equality." ∷ [])
  lhs-exp ← construct-exp lhs
  rhs-exp ← construct-exp rhs
  debugPrint "vtac" 5 (strErr "naturality solver successfully constructed expressions:" ∷ termErr lhs-exp ∷ termErr rhs-exp ∷ [])
  let sol = def (quote type-naturality-reflect)
                (vArg lhs-exp ∷ vArg rhs-exp ∷ vArg (con (quote _≡_.refl) []) ∷ vArg (con (quote _≡ω_.refl) []) ∷ [])
  unify hole sol

macro
  by-naturality : Term → TC ⊤
  by-naturality = by-naturality-macro


private
  open import Types.Discrete
  open import Types.Functions
  open import Types.Products

  example' : ∀ {ℓ ℓ' ℓ'' C} {Δ : Ctx C ℓ} {Γ : Ctx C ℓ'} {Θ : Ctx C ℓ''} →
             (σ : Δ ⇒ Γ) (τ : Γ ⇒ Θ) →
             ((Bool' ⇛ Bool') ⊠ ((Discr Bool) [ τ ])) [ σ ] ≅ᵗʸ ((Bool' ⇛ Bool') [ σ ]) ⊠ Bool'
  example' σ τ = by-naturality


-- Experiments interaction var + by-naturality tactics

open Data.Bool using (not)
open Data.Product using (Σ; Σ-syntax; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Categories
open import Types.Discrete
open import Types.Functions
open import Types.Products
open import Types.Sums

module _ {C : Category} where
  not' : {Γ : Ctx C ℓ} → Tm Γ Bool' → Tm Γ Bool'
  term (not' b) x _ = not (b ⟨ x , _ ⟩')
  naturality (not' b) f eγ = cong not (naturality b f eγ)

  not-fun : Tm {C = C} ◇ (Bool' ⇛ Bool')
  not-fun = lam Bool' (ι[ by-naturality ] not' (ι[ by-naturality ] var 0))

lam-tactic : ∀ {C ℓc ℓs} {Γ : Ctx C ℓc} → Ty Γ ℓs → Term → TC ⊤
lam-tactic S hole = do
  t-S ← quoteTC S >>= reduce
  debugPrint "vtac" 5 (strErr "lam-tactic called with type" ∷ termErr t-S ∷ [])
  expr-S ← construct-exp t-S
  let S'-t = def (quote ⟦_⟧exp) (vArg expr-S ∷ [])
  debugPrint "vtac" 5 (strErr "lam-tactic constructed expression" ∷ termErr S'-t ∷ [])
  let proof = def (quote type-naturality-reflect)
                  (vArg (con (quote sub) (vArg expr-S ∷ vArg (def (quote π) []) ∷ []))
                    ∷ vArg expr-S
                    ∷ vArg (con (quote _≡_.refl) [])
                    ∷ vArg (con (quote _≡ω_.refl) [])
                    ∷ [])
  unify hole (con (quote _,_) (vArg S'-t ∷ vArg proof ∷ []))

lamι : ∀ {C ℓc ℓt ℓs ℓs'} {Γ : Ctx C ℓc} (T : Ty Γ ℓt) {S : Ty Γ ℓs}
       {@(tactic lam-tactic S) body-type : Σ[ S' ∈ Ty (Γ ,, T) ℓs' ] (S [ π ] ≅ᵗʸ S')} →
       Tm (Γ ,, T) (proj₁ body-type) → Tm Γ (T ⇛ S)
lamι T {body-type = S' , S=S'} b = lam T (ι[ S=S' ] b)

module _ {C ℓc} {Γ : Ctx C ℓc} where
  test-lam : Tm Γ (Bool' ⇛ Bool' ⇛ Bool')
  test-lam = lamι Bool' (lamι Bool' (ι[ by-naturality ] var 1))

open import GuardedRecursion.Later
other-test : Tm {C = ω} ◇ (▻' Bool' ⇛ ▻' Bool')
other-test = (lamι (▻' Bool') ?)
