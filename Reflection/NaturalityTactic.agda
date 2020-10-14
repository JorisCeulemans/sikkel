module Reflection.NaturalityTactic where

--------------------------------------------------
-- Definition of tactic by-naturality

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc; #_)
open import Data.List using (List; []; _∷_; filter)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Reflection hiding (lam; var)
open import Reflection.Argument using (_⟨∷⟩_; unArg)
open import Reflection.TypeChecking.Monad.Syntax using (_<$>_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Helpers
open import CwF-Structure
open import Reflection.Naturality renaming (reduce to nat-reduce)
open import Reflection.Util

get-args : Type → Maybe (Term × Term)
get-args (def (quote _≅ᵗʸ_) xs) = go xs
  where
  go : List (Arg Term) → Maybe (Term × Term)
  go (vArg x ∷ vArg y ∷ []) = just (x , y)
  go (x ∷ xs)               = go xs
  go _                      = nothing
get-args _ = nothing

is-arg-semtype : Arg Term → TC Bool
is-arg-semtype a = inferType (unArg a) >>= λ
  { (def (quote Ty) _) → return true
  ; _ → return false
  }

tyseqLookup : Term → {n : ℕ} → Fin n → TC Term
tyseqLookup (con (quote TypeSequence.[]) args) i = typeError (strErr "The requested variable does not exist." ∷ [])
tyseqLookup (con (quote TypeSequence._∷_) args) zero = getVisibleArg 1 args
tyseqLookup (con (quote TypeSequence._∷_) args) (suc i) = getVisibleArg 0 args >>= λ tyseq → tyseqLookup tyseq i
tyseqLookup tyseq i = typeError (strErr "tyseqLookup is not called with a type sequence." ∷ [])

weakenVarExpr : Term → {n : ℕ} → Fin n → Term
weakenVarExpr expr zero    = con (quote sub) (expr ⟨∷⟩ def (quote π) [] ⟨∷⟩ [])
weakenVarExpr expr (suc i) = con (quote sub) (weakenVarExpr expr i ⟨∷⟩ def (quote π) [] ⟨∷⟩ [])

weakenExpr : Term → ℕ → Term
weakenExpr expr zero    = expr
weakenExpr expr (suc n) = con (quote sub) (weakenExpr expr n ⟨∷⟩ def (quote π) [] ⟨∷⟩ [])

{-# TERMINATING #-}
construct-exp : Term → TC Term
construct-exp (def (quote ⟦_⟧exp) args) = getVisibleArg 0 args
construct-exp (def (quote var-type) args) = do
  t-tyseq ← getVisibleArg 0 args
  len-tyseq ← getArg 3 args >>= unquoteTC
  var-num ← getVisibleArg 1 args >>= unquoteTC
  t-type ← tyseqLookup t-tyseq {len-tyseq} var-num
  expr-type ← construct-exp t-type
  return (weakenVarExpr expr-type var-num)
construct-exp (def (quote weaken-type) args) = do
  expr-not-weakened-type ← getVisibleArg 1 args >>= construct-exp
  weaken-nr ← getArg 4 args >>= unquoteTC
  return (weakenExpr expr-not-weakened-type weaken-nr)
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
construct-exp (meta m args) = debugPrint "vtac" 5 (strErr "Blocking on meta" ∷ termErr (meta m args) ∷ strErr "in construct-exp." ∷ []) >>
                              blockOnMeta m
construct-exp ty = typeError (strErr "The naturality tactic does not work for the type" ∷ termErr ty ∷ [])

by-naturality-macro : Term → TC ⊤
by-naturality-macro hole = do
  goal ← inferType hole
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


--------------------------------------------------
-- Lambda that automatically performs naturality reduction on its body type

lam-tactic : ∀ {C ℓc ℓt ℓs} {Γ : Ctx C ℓc} → Ty Γ ℓt → Ty Γ ℓs → Term → TC ⊤
lam-tactic T S hole = do
  t-wantedBodyType ← quoteTC (S [ π {T = T} ])
  debugPrint "vtac" 5 (strErr "lam-tactic called with type" ∷ termErr t-wantedBodyType ∷ [])
  expr-wantedBodyType ← construct-exp t-wantedBodyType
  let expr-reducedBodyType = def (quote nat-reduce) (vArg expr-wantedBodyType ∷ [])
  debugPrint "vtac" 5 (strErr "lam-tactic constructed expression" ∷ termErr expr-reducedBodyType ∷ [])
  let t-reducedBodyType = def (quote ⟦_⟧exp) (vArg expr-reducedBodyType ∷ [])
  let proof = def (quote reduce-sound) (vArg expr-wantedBodyType ∷ [])
  unify hole (con (quote _,_) (vArg t-reducedBodyType ∷ vArg proof ∷ []))

lamι : ∀ {C ℓc ℓt ℓs ℓs'} {Γ : Ctx C ℓc} (T : Ty Γ ℓt) {S : Ty Γ ℓs}
       {@(tactic lam-tactic T S) body-type : Σ[ S' ∈ Ty (Γ ,, T) ℓs' ] (S [ π ] ≅ᵗʸ S')} →
       Tm (Γ ,, T) (proj₁ body-type) → Tm Γ (T ⇛ S)
lamι T {body-type = S' , S=S'} b = lam T (ι[ S=S' ] b)


--------------------------------------------------
-- Variable macro that automatically performs naturality reduction on its type

getTermType : Type → TC Term
getTermType (def (quote Tm) args) = getVisibleArg 1 args
getTermType (meta m args) = debugPrint "vtac" 5 (strErr "Blocking on meta" ∷ termErr (meta m args) ∷ strErr "in getTermType." ∷ []) >>
                            blockOnMeta m
getTermType _ = typeError (strErr "The varι macro can only construct a term." ∷ [])

varι-macro : Term → Term → TC ⊤
varι-macro x hole = do
  goal ← inferType hole
  debugPrint "vtac" 5 (strErr "varι macro called, goal:" ∷ termErr goal ∷ [])
  ctx ← get-ctx goal
  tyseq ← ctx-to-tyseq ctx
  check-within-bounds x tyseq
  let partialSolution = def (quote prim-var) (vArg tyseq ∷ vArg (def (quote #_) (vArg x ∷ [])) ∷ [])
  expr-resultType ← inferType partialSolution >>= getTermType >>= construct-exp
  let proof = def (quote reduce-sound) (expr-resultType ⟨∷⟩ [])
  let solution = def (quote ι⁻¹[_]_) (proof ⟨∷⟩ partialSolution ⟨∷⟩ [])
  debugPrint "vtac" 5 (strErr "varι macro successfully constructed solution:" ∷ termErr solution ∷ [])
  unify hole solution

macro
  varι : Term → Term → TC ⊤
  varι = varι-macro


--------------------------------------------------
-- Weakening macro that automatically performs naturality reduction on its type

weakenι-macro : ℕ → Term → Term → TC ⊤
weakenι-macro n term hole = do
  extended-ctx ← inferType hole >>= get-ctx
  ty-seq ← bounded-ctx-to-tyseq n extended-ctx
  let partial-solution = def (quote weaken-term) (ty-seq ⟨∷⟩ term ⟨∷⟩ [])
  expr-resultType ← inferType partial-solution >>= getTermType >>= construct-exp
  let proof = def (quote reduce-sound) (expr-resultType ⟨∷⟩ [])
  let solution = def (quote ι⁻¹[_]_) (proof ⟨∷⟩ partial-solution ⟨∷⟩ [])
  unify hole solution

macro
  ↑ι⟨_⟩_ : ℕ → Term → Term → TC ⊤
  ↑ι⟨ n ⟩ term = weakenι-macro n term


--------------------------------------------------
-- Löb induction with automatic reduction of type

open import GuardedRecursion.Later
löb'-tactic : ∀ {ℓc ℓt} {Γ : Ctx ω ℓc} → Ty Γ ℓt → Term → TC ⊤
löb'-tactic T hole = do
  t-wantedBodyType ← quoteTC (T [ π {T = ▻' T} ])
  expr-wantedBodyType ← construct-exp t-wantedBodyType
  let expr-reducedBodyType = def (quote nat-reduce) (vArg expr-wantedBodyType ∷ [])
  let t-reducedBodyType = def (quote ⟦_⟧exp) (vArg expr-reducedBodyType ∷ [])
  let proof = def (quote reduce-sound) (vArg expr-wantedBodyType ∷ [])
  unify hole (con (quote _,_) (vArg t-reducedBodyType ∷ vArg proof ∷ []))

löbι : ∀ {ℓc ℓt ℓs} {Γ : Ctx ω ℓc} (T : Ty Γ ℓt)
      {@(tactic löb'-tactic T) body-type : Σ[ S ∈ Ty (Γ ,, ▻' T) ℓs ] (T [ π ] ≅ᵗʸ S)} →
      Tm (Γ ,, ▻' T) (proj₁ body-type) → Tm Γ T
löbι T {body-type = S , T=S} b = löb' T (ι[ T=S ] b)
