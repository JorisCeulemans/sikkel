{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- Naturality solver
--
-- This module implements a solver for proofs of type equalities making use
-- of naturality. A typical example for its applicability can be found at the
-- bottom of the file.
-- The solver works with arbitrary nullary, unary and binary type operations
-- that are natural with respect to the context (and that also respect equivalence
-- of types in case of unary and binary operations). When you implement a new
-- operation in a specific base category, you can make the solver work with it
-- by providing a value of the appropriate record type below (NullaryTypeOp,
-- UnaryTypeOp or BinaryTypeOp).
-- Note that we use the option omega-in-omega in order to define
-- an inductive data type in Setω and to pattern match on it (which
-- is not possible in Agda 2.6.1 without this option). This code should
-- typecheck without this option in Agda 2.6.2 once released.
--------------------------------------------------

open import Categories

module Reflection.Naturality {C : Category} where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import Reflection.Helpers public


-- TODO: Allow operations that can change the context the type lives in using a certain endofunctor
-- on the category of contexts (needed for ▻). Later, functors between different categories might as well be interesting.


--------------------------------------------------
-- Definition of record types of nullary, unary and binary type operations.

NullaryTypeOp : Level → Setω
NullaryTypeOp ℓ = ∀ {ℓc} {Γ : Ctx C ℓc} → Ty Γ ℓ

record IsNullaryNatural {ℓ} (U : NullaryTypeOp ℓ) : Setω where
  field
    natural-nul : ∀ {ℓc ℓc'} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} (σ : Δ ⇒ Γ) →
                  U [ σ ] ≅ᵗʸ U

open IsNullaryNatural {{...}} public

UnaryTypeOp : (Level → Level → Level) → Setω
UnaryTypeOp f = ∀ {ℓc ℓt} {Γ : Ctx C ℓc} → Ty Γ ℓt → Ty Γ (f ℓc ℓt)

record IsUnaryNatural {f} (F : UnaryTypeOp f) : Setω where
  field
    natural-un : ∀ {ℓc ℓc' ℓt} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} (σ : Δ ⇒ Γ) {T : Ty Γ ℓt} →
                 (F T) [ σ ] ≅ᵗʸ F (T [ σ ])
    cong-un : ∀ {ℓc ℓt ℓt'} {Γ : Ctx C ℓc}
              {T : Ty Γ ℓt} {T' : Ty Γ ℓt'} →
              T ≅ᵗʸ T' → F T ≅ᵗʸ F T'

open IsUnaryNatural {{...}} public

BinaryTypeOp : (Level → Level → Level → Level) → Setω
BinaryTypeOp f = ∀ {ℓc ℓt ℓt'} {Γ : Ctx C ℓc} → Ty Γ ℓt → Ty Γ ℓt' → Ty Γ (f ℓc ℓt ℓt')

record IsBinaryNatural {f} (F : BinaryTypeOp f) : Setω where
  field
    natural-bin : ∀ {ℓc ℓc' ℓt ℓt'} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} (σ : Δ ⇒ Γ) →
                  {T : Ty Γ ℓt} {S : Ty Γ ℓt'} →
                  (F T S) [ σ ] ≅ᵗʸ F (T [ σ ]) (S [ σ ])
    cong-bin : ∀ {ℓc ℓt ℓt' ℓs ℓs'} {Γ : Ctx C ℓc}
               {T : Ty Γ ℓt} {T' : Ty Γ ℓt'} {S : Ty Γ ℓs} {S' : Ty Γ ℓs'} →
               T ≅ᵗʸ T' → S ≅ᵗʸ S' → F T S ≅ᵗʸ F T' S'

open IsBinaryNatural {{...}} public


--------------------------------------------------
-- Definition of expressions that represent the structure of a type.

-- An expression is indexed by its skeleton, which drops the information
-- about contexts but keeps track of universe levels. The skeleton is needed
-- to convince Agda that the function reduce below terminates.
data ExpSkeleton : Set where
  -- svar : Level → ExpSkeleton
  snul : Level → ExpSkeleton
  sun  : (f : Level → Level → Level) (ℓc : Level) →
         ExpSkeleton → ExpSkeleton
  sbin : (f : Level → Level → Level → Level) (ℓc : Level) →
         ExpSkeleton → ExpSkeleton → ExpSkeleton
  ssub : (ℓc : Level) → ExpSkeleton → ExpSkeleton

level : ExpSkeleton → Level
-- level (svar ℓ) = ℓ
level (snul ℓ) = ℓ
level (sun f ℓc s) = f ℓc (level s)
level (sbin f ℓc s1 s2) = f ℓc (level s1) (level s2)
level (ssub ℓc s) = level s

-- NOTE: At the moment the introduction of an arbitrary type, without
-- info on naturality, in an Exp using var is disabled because it simplifies
-- the macro by-naturality. We will consider its reintroduction in the future.
-- (var isn't a good name anyway because it is now the name of the macro for variables.)
data Exp : {ℓc : Level} (Γ : Ctx C ℓc) → ExpSkeleton → Setω where
  -- var : ∀ {ℓc ℓ} {Γ : Ctx C ℓc} →
  --       (T : Ty Γ ℓ) → Exp Γ (svar ℓ)
  nul : ∀ {ℓc ℓ} {Γ : Ctx C ℓc} →
        (U : NullaryTypeOp ℓ) → {{IsNullaryNatural U}} → Exp Γ (snul ℓ)
  un  : ∀ {ℓc f s} {Γ : Ctx C ℓc} →
        (F : UnaryTypeOp f) → {{IsUnaryNatural F}} → (e : Exp Γ s) → Exp Γ (sun f ℓc s)
  bin : ∀ {ℓc f s s'} {Γ : Ctx C ℓc} →
        (F : BinaryTypeOp f) → {{IsBinaryNatural F}} → (e1 : Exp Γ s) (e2 : Exp Γ s') → Exp Γ (sbin f ℓc s s')
  sub : ∀ {ℓc ℓc' s} {Δ : Ctx C ℓc} {Γ : Ctx C ℓc'} →
        Exp Γ s → (σ : Δ ⇒ Γ) → Exp Δ (ssub ℓc s)

⟦_⟧exp : ∀ {ℓc s} {Γ : Ctx C ℓc} → Exp Γ s → Ty Γ (level s)
-- ⟦ var T ⟧exp = T
⟦ nul U ⟧exp = U
⟦ un F e ⟧exp = F ⟦ e ⟧exp
⟦ bin F e1 e2 ⟧exp = F ⟦ e1 ⟧exp ⟦ e2 ⟧exp
⟦ sub e σ ⟧exp = ⟦ e ⟧exp [ σ ]


--------------------------------------------------
-- Reduction of expressions + soundness

reduce-skeleton : ExpSkeleton → ExpSkeleton
-- reduce-skeleton (svar ℓ) = svar ℓ
reduce-skeleton (snul ℓ) = snul ℓ
reduce-skeleton (sun f ℓc s) = sun f ℓc (reduce-skeleton s)
reduce-skeleton (sbin f ℓc s1 s2) = sbin f ℓc (reduce-skeleton s1) (reduce-skeleton s2)
-- reduce-skeleton (ssub ℓc (svar ℓ)) = ssub ℓc (svar ℓ)
reduce-skeleton (ssub ℓc (snul ℓ)) = snul ℓ
reduce-skeleton (ssub ℓc (sun f ℓc' s)) = sun f ℓc (reduce-skeleton (ssub ℓc s))
reduce-skeleton (ssub ℓc (sbin f ℓc' s1 s2)) = sbin f ℓc (reduce-skeleton (ssub ℓc s1)) (reduce-skeleton (ssub ℓc s2))
reduce-skeleton (ssub ℓc (ssub ℓc' s)) = reduce-skeleton (ssub ℓc s)

reduce : ∀ {ℓc s} {Γ : Ctx C ℓc} → Exp Γ s → Exp Γ (reduce-skeleton s)
-- reduce (var T) = var T
reduce (nul U) = nul U
reduce (un F e) = un F (reduce e)
reduce (bin F e1 e2) = bin F (reduce e1) (reduce e2)
-- reduce (sub (var T) σ) = sub (var T) σ
reduce (sub (nul U) σ) = nul U
reduce (sub (un F e) σ) = un F (reduce (sub e σ))
reduce (sub (bin F e1 e2) σ) = bin F (reduce (sub e1 σ)) (reduce (sub e2 σ))
reduce (sub (sub e τ) σ) = reduce (sub e (τ ⊚ σ))

reduce-sound : ∀ {ℓc s} {Γ : Ctx C ℓc} (e : Exp Γ s) →
               ⟦ e ⟧exp ≅ᵗʸ ⟦ reduce e ⟧exp
-- reduce-sound (var T) = ≅ᵗʸ-refl
reduce-sound (nul U) = ≅ᵗʸ-refl
reduce-sound (un F e) = cong-un (reduce-sound e)
reduce-sound (bin F e1 e2) = cong-bin (reduce-sound e1) (reduce-sound e2)
-- reduce-sound (sub (var T) σ) = ≅ᵗʸ-refl
reduce-sound (sub (nul U) σ) = natural-nul σ
reduce-sound (sub (un F e) σ) =
  begin
    (F ⟦ e ⟧exp) [ σ ]
  ≅⟨ natural-un σ ⟩
    F (⟦ e ⟧exp [ σ ])
  ≅⟨⟩
    F ⟦ sub e σ ⟧exp
  ≅⟨ cong-un (reduce-sound (sub e σ)) ⟩
    F ⟦ reduce (sub e σ ) ⟧exp ∎
  where open ≅ᵗʸ-Reasoning
reduce-sound (sub (bin F e1 e2) σ) =
  begin
    (F ⟦ e1 ⟧exp ⟦ e2 ⟧exp) [ σ ]
  ≅⟨ natural-bin σ ⟩
    F (⟦ e1 ⟧exp [ σ ]) (⟦ e2 ⟧exp [ σ ])
  ≅⟨⟩
    F ⟦ sub e1 σ ⟧exp ⟦ sub e2 σ ⟧exp
  ≅⟨ cong-bin (reduce-sound (sub e1 σ)) (reduce-sound (sub e2 σ)) ⟩
    F ⟦ reduce (sub e1 σ) ⟧exp ⟦ reduce (sub e2 σ) ⟧exp ∎
  where open ≅ᵗʸ-Reasoning
reduce-sound (sub (sub e τ) σ) =
  begin
    (⟦ e ⟧exp [ τ ]) [ σ ]
  ≅⟨ ty-subst-comp ⟦ e ⟧exp τ σ ⟩
    ⟦ e ⟧exp [ τ ⊚ σ ]
  ≅⟨⟩
    ⟦ sub e (τ ⊚ σ) ⟧exp
  ≅⟨ reduce-sound (sub e (τ ⊚ σ)) ⟩
    ⟦ reduce (sub e (τ ⊚ σ)) ⟧exp ∎
  where open ≅ᵗʸ-Reasoning

⟦⟧exp-cong : ∀ {ℓc s s'} {Γ : Ctx C ℓc} →
             {e : Exp Γ s} {e' : Exp Γ s'} →
             (p : s ≡ s') →
             ω-transp (Exp Γ) p e ≡ω e' →
             ⟦ e ⟧exp ≅ᵗʸ ⟦ e' ⟧exp
⟦⟧exp-cong refl refl = ≅ᵗʸ-refl


--------------------------------------------------
-- End result

type-naturality-reflect : ∀ {ℓc s s'} {Γ : Ctx C ℓc} →
                          (e : Exp Γ s) (e' : Exp Γ s') →
                          (p : reduce-skeleton s ≡ reduce-skeleton s') →
                          ω-transp (Exp Γ) p (reduce e) ≡ω reduce e' →
                          ⟦ e ⟧exp ≅ᵗʸ ⟦ e' ⟧exp
type-naturality-reflect e e' p q =
  begin
    ⟦ e ⟧exp
  ≅⟨ reduce-sound e ⟩
    ⟦ reduce e ⟧exp
  ≅⟨ ⟦⟧exp-cong p q ⟩
    ⟦ reduce e' ⟧exp
  ≅˘⟨ reduce-sound e' ⟩
    ⟦ e' ⟧exp ∎
  where open ≅ᵗʸ-Reasoning


--------------------------------------------------
-- Definition of some operations that exist in any presheaf category

module Operations where
  open import Types.Discrete
  open import Types.Functions
  open import Types.Products
  open import Types.Sums

  instance
    discr-nul : ∀ {ℓ} {A : Set ℓ} → IsNullaryNatural (Discr A)
    natural-nul {{discr-nul {A = A}}} σ = Discr-natural A σ

    fun-bin : IsBinaryNatural _⇛_
    natural-bin {{fun-bin}} σ = ⇛-natural σ
    cong-bin {{fun-bin}} = ⇛-cong

    prod-bin : IsBinaryNatural _⊠_
    natural-bin {{prod-bin}} σ = ⊠-natural σ
    cong-bin {{prod-bin}} = ⊠-cong

    sum-bin : IsBinaryNatural _⊞_
    natural-bin {{sum-bin}} σ = ⊞-natural σ
    cong-bin {{sum-bin}} = ⊞-cong

open Operations public


--------------------------------------------------
-- Definition of tactic by-naturality

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; break)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Reflection
open import Reflection.Argument using (_⟨∷⟩_; unArg)
open import Reflection.TypeChecking.MonadSyntax using (_<$>_)

open import Helpers

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

is-ty : Term → Bool
is-ty (def (quote Ty) _) = true
is-ty _ = false

arg-pred : Arg Term → TC Bool
arg-pred a = inferType (unArg a) >>= λ ta → return (is-visible a ∧ is-ty ta)

construct-exp : Term → TC Term
construct-exp (def (quote _[_]) args) = breakTC arg-pred args >>= λ
  { (_ , (ty ⟨∷⟩ subst ⟨∷⟩ [])) → do
      ty-exp ← construct-exp ty
      return (con (quote sub) (vArg ty-exp ∷ vArg subst ∷ []))
  ; _ → typeError (strErr "Illegal substitution." ∷ [])
  }
construct-exp (def op args) = breakTC arg-pred args >>= λ
  { (others , []) → return (con (quote nul) (vArg (def op {-others-}[]) ∷ []))
  ; (others , (ty1 ⟨∷⟩ [])) → do
      ty1-exp ← construct-exp ty1
      return (con (quote un) (vArg (def op {-others-}[]) ∷ vArg ty1-exp ∷ []))
  ; (others , (ty1 ⟨∷⟩ ty2 ⟨∷⟩ [])) → do
      ty1-exp ← construct-exp ty1
      ty2-exp ← construct-exp ty2
      return (con (quote bin) (vArg (def op {-others-}[]) ∷ vArg ty1-exp ∷ vArg ty2-exp ∷ []))
  ; _ → typeError (strErr "No type operator recognized." ∷ [])
  }
construct-exp ty = typeError (strErr "The naturality tactic does not work for the type" ∷ termErr ty ∷ [])

by-naturality-macro : Term → TC ⊤
by-naturality-macro hole = do
  goal ← inferType hole
  just (lhs , rhs) ← return (get-args goal)
    where nothing → typeError (termErr goal ∷ strErr "is not a type equality." ∷ [])
  lhs-exp ← construct-exp lhs
  rhs-exp ← construct-exp rhs
  debugPrint "vtac" 5 (termErr lhs-exp ∷ termErr rhs-exp ∷ [])
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

  example : ∀ {ℓ ℓ' ℓ''} {Δ : Ctx C ℓ} {Γ : Ctx C ℓ'} {Θ : Ctx C ℓ''} →
            (σ : Δ ⇒ Γ) (τ : Γ ⇒ Θ) →
            ((Bool' ⇛ Bool') ⊠ (Bool' [ τ ])) [ σ ] ≅ᵗʸ ((Bool' ⇛ Bool') [ σ ]) ⊠ Bool'
  example σ τ = type-naturality-reflect (sub (bin _⊠_ (bin _⇛_ (nul Bool') (nul Bool')) (sub (nul Bool') τ)) σ)
                                        (bin _⊠_ (sub (bin _⇛_ (nul Bool') (nul Bool')) σ) (nul Bool'))
                                        refl
                                        refl

  example' : ∀ {ℓ ℓ' ℓ''} {Δ : Ctx C ℓ} {Γ : Ctx C ℓ'} {Θ : Ctx C ℓ''} →
             (σ : Δ ⇒ Γ) (τ : Γ ⇒ Θ) →
             ((Bool' ⇛ Bool') ⊠ (Bool' [ τ ])) [ σ ] ≅ᵗʸ ((Bool' ⇛ Bool') [ σ ]) ⊠ Bool'
  example' σ τ = by-naturality
