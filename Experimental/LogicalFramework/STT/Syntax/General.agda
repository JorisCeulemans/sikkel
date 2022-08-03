--------------------------------------------------
-- Definition of STT contexts, terms and their associated operations
--   The general syntax is parametrised by a type of names to represent
--   variables. It is not recommended to directly import this module,
--   but rather use STT.Syntax.Named.
--------------------------------------------------

module Experimental.LogicalFramework.STT.Syntax.General (Name : Set) where

open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.STT.Syntax.Types

private variable
  T S : TyExpr
  x y : Name


--------------------------------------------------
-- Definition of STT contexts and terms

infixl 4 _,,_∈_
data CtxExpr : Set where
  ◇ : CtxExpr
  _,,_∈_ : (Γ : CtxExpr) (x : Name) (T : TyExpr) → CtxExpr
    -- ^ All variables have a name of type Name.

private variable
  Γ Δ Θ : CtxExpr


-- The predicate Var x Γ expresses that a variable named x is present
-- in context Γ. Note that this is a proof-relevant predicate and
-- names in Γ may not be unique (but this is of course discouraged).
-- As a result, STT terms internally represent variables using De
-- Bruijn indices, but we do keep track of the names of the variables.
data Var : Name → CtxExpr → Set where
  vzero : Var x (Γ ,, x ∈ T)
  vsuc : Var x Γ → Var x (Γ ,, y ∈ S)

lookup-var : Var x Γ → TyExpr
lookup-var (vzero {T = T}) = T
lookup-var (vsuc v) = lookup-var v

infixl 50 _∙_
data TmExpr (Γ : CtxExpr) : TyExpr → Set where
  var' : (x : Name) {v : Var x Γ} → {lookup-var v ≡ T} → TmExpr Γ T
  -- ^ When writing programs, one should not directly use var' but rather combine
  --   it with a decision procedure for Var, which will resolve the name.
  --   Using the type equality, lets us avoid transporting terms in the operations below.
  lam[_∈_]_ : (x : Name) (T : TyExpr) → TmExpr (Γ ,, x ∈ T) S → TmExpr Γ (T ⇛ S)
  _∙_ : TmExpr Γ (T ⇛ S) → TmExpr Γ T → TmExpr Γ S
  zero : TmExpr Γ Nat'
  suc : TmExpr Γ (Nat' ⇛ Nat')
  nat-elim : {A : TyExpr} → TmExpr Γ A → TmExpr Γ (A ⇛ A) → TmExpr Γ (Nat' ⇛ A)
  true false : TmExpr Γ Bool'
  if : {A : TyExpr} → TmExpr Γ Bool' → (t f : TmExpr Γ A) → TmExpr Γ A
  pair : TmExpr Γ T → TmExpr Γ S → TmExpr Γ (T ⊠ S)
  fst : TmExpr Γ (T ⊠ S) → TmExpr Γ T
  snd : TmExpr Γ (T ⊠ S) → TmExpr Γ S


--------------------------------------------------
-- Weakening of terms

_++ctx_ : CtxExpr → CtxExpr → CtxExpr
Γ ++ctx ◇ = Γ
Γ ++ctx (Δ ,, x ∈ T) = (Γ ++ctx Δ) ,, x ∈ T

mid-weaken-var : {Γ : CtxExpr} (Δ : CtxExpr) → Var x (Γ ++ctx Δ) → Var x ((Γ ,, y ∈ S) ++ctx Δ)
mid-weaken-var ◇            v        = vsuc v
mid-weaken-var (Δ ,, _ ∈ R) vzero    = vzero
mid-weaken-var (Δ ,, _ ∈ R) (vsuc v) = vsuc (mid-weaken-var Δ v)

mid-weaken-var-ty : ∀ {x y S} {Γ : CtxExpr} (Δ : CtxExpr) (v : Var x (Γ ++ctx Δ)) →
                    lookup-var (mid-weaken-var {y = y} {S = S} Δ v) ≡ lookup-var v
mid-weaken-var-ty ◇            v        = refl
mid-weaken-var-ty (Δ ,, _ ∈ R) vzero    = refl
mid-weaken-var-ty (Δ ,, _ ∈ R) (vsuc v) = mid-weaken-var-ty Δ v

mid-weaken-tm : ∀ (Δ : CtxExpr) → TmExpr (Γ ++ctx Δ) T → TmExpr ((Γ ,, x ∈ S) ++ctx Δ) T
mid-weaken-tm Δ (var' x {v} {refl}) = var' x {mid-weaken-var Δ v} {mid-weaken-var-ty Δ v}
mid-weaken-tm Δ (lam[ y ∈ T ] t) = lam[ y ∈ T ] mid-weaken-tm (Δ ,, y ∈ T) t
mid-weaken-tm Δ (f ∙ t) = mid-weaken-tm Δ f ∙ mid-weaken-tm Δ t
mid-weaken-tm Δ zero = zero
mid-weaken-tm Δ suc = suc
mid-weaken-tm Δ (nat-elim a f) = nat-elim (mid-weaken-tm Δ a) (mid-weaken-tm Δ f)
mid-weaken-tm Δ true = true
mid-weaken-tm Δ false = false
mid-weaken-tm Δ (if b t f) = if (mid-weaken-tm Δ b) (mid-weaken-tm Δ t) (mid-weaken-tm Δ f)
mid-weaken-tm Δ (pair t s) = pair (mid-weaken-tm Δ t) (mid-weaken-tm Δ s)
mid-weaken-tm Δ (fst p) = fst (mid-weaken-tm Δ p)
mid-weaken-tm Δ (snd p) = snd (mid-weaken-tm Δ p)

weaken-tm : TmExpr Γ T → TmExpr (Γ ,, x ∈ S) T
weaken-tm t = mid-weaken-tm ◇ t

multi-weaken-tm : (Δ : CtxExpr) → TmExpr Γ T → TmExpr (Γ ++ctx Δ) T
multi-weaken-tm ◇            t = t
multi-weaken-tm (Δ ,, x ∈ T) t = weaken-tm (multi-weaken-tm Δ t)


--------------------------------------------------
-- Syntactic substitutions

-- With the following data type, there are multiple ways to represent
-- the same substitution. This is not a problem since we will never
-- compare substitutions (only apply them to terms and compute
-- immediately). Having a constructor for e.g. the identity seems more
-- efficient than implementing it (but this claim needs justification).
data SubstExpr : CtxExpr → CtxExpr → Set where
  [] : SubstExpr Γ ◇
  _∷_/_ : SubstExpr Δ Γ → TmExpr Δ T → (x : Name) → SubstExpr Δ (Γ ,, x ∈ T)
  id-subst : (Γ : CtxExpr) → SubstExpr Γ Γ
  _⊚πs⟨_⟩ : SubstExpr Δ Γ → (Θ : CtxExpr) → SubstExpr (Δ ++ctx Θ) Γ

π : SubstExpr (Γ ,, x ∈ T) Γ
π = id-subst _ ⊚πs⟨ _ ⟩

_⊚π : SubstExpr Δ Γ → SubstExpr (Δ ,, x ∈ T) Γ
σ ⊚π = σ ⊚πs⟨ _ ⟩

_⊹⟨_⟩ : SubstExpr Δ Γ → (x : Name) → SubstExpr (Δ ,, x ∈ T) (Γ ,, x ∈ T)
σ ⊹⟨ x ⟩ = (σ ⊚π) ∷ var' x {vzero} {refl} / x

_/_ : TmExpr Γ T → (x : Name) → SubstExpr Γ (Γ ,, x ∈ T)
t / x = id-subst _ ∷ t / x


--------------------------------------------------
-- Applying a substitution to a term
--   Note that the operation _[_]tm is automatically capture-avoiding
--   since it only makes use of the De Bruijn indices, not of names.

-- We will use the following view pattern in the implementation of
-- substitution for terms, in order to treat some substitutions
-- specially.
data SpecialSubstExpr : SubstExpr Γ Δ → Set where
  id-subst : (Γ : CtxExpr) → SpecialSubstExpr (id-subst Γ)
  _⊚πs⟨_⟩ : (σ : SubstExpr Γ Δ) → (Θ : CtxExpr) → SpecialSubstExpr (σ ⊚πs⟨ Θ ⟩)

is-special-subst? : (σ : SubstExpr Γ Δ) → Maybe (SpecialSubstExpr σ)
is-special-subst? []           = nothing
is-special-subst? (σ ∷ t / x)  = nothing
is-special-subst? (id-subst Γ) = just (id-subst Γ)
is-special-subst? (σ ⊚πs⟨ Θ ⟩) = just (σ ⊚πs⟨ Θ ⟩)

subst-var : (v : Var x Γ) → SubstExpr Δ Γ → lookup-var v ≡ T → TmExpr Δ T
subst-var {x = x} v (id-subst Γ) e = var' x {v} {e}
subst-var v         (σ ⊚πs⟨ ◇ ⟩) e = subst-var v σ e
subst-var v         (σ ⊚πs⟨ Δ ,, _ ∈ T ⟩) e = weaken-tm (subst-var v (σ ⊚πs⟨ Δ ⟩) e)
subst-var vzero     (σ ∷ t / x) refl = t
subst-var (vsuc v)  (σ ∷ s / x) e = subst-var v σ e

_[_]tm : TmExpr Γ T → SubstExpr Δ Γ → TmExpr Δ T
t [ σ ]tm with is-special-subst? σ
(t [ .(id-subst Γ) ]tm)  | just (id-subst Γ) = t
(t [ .(σ ⊚πs⟨ Θ ⟩) ]tm)  | just (σ ⊚πs⟨ Θ ⟩) = multi-weaken-tm Θ (t [ σ ]tm)
(var' x {v} {e}) [ σ ]tm | nothing = subst-var v σ e
(lam[ x ∈ T ] t) [ σ ]tm | nothing = lam[ x ∈ T ] (t [ σ ⊹⟨ x ⟩ ]tm)
(f ∙ t) [ σ ]tm          | nothing = (f [ σ ]tm) ∙ (t [ σ ]tm)
zero [ σ ]tm             | nothing = zero
suc [ σ ]tm              | nothing = suc
(nat-elim a f) [ σ ]tm   | nothing = nat-elim (a [ σ ]tm) (f [ σ ]tm)
true [ σ ]tm             | nothing = true
false [ σ ]tm            | nothing = false
(if b t f) [ σ ]tm       | nothing = if (b [ σ ]tm) (t [ σ ]tm) (f [ σ ]tm)
(pair t s) [ σ ]tm       | nothing = pair (t [ σ ]tm) (s [ σ ]tm)
(fst p) [ σ ]tm          | nothing = fst (p [ σ ]tm)
(snd p) [ σ ]tm          | nothing = snd (p [ σ ]tm)


--------------------------------------------------
-- Proving that substituting the most recently added variable in a
--   weakened term has no effect.

multi⊹ : (Θ : CtxExpr) → SubstExpr Γ Δ → SubstExpr (Γ ++ctx Θ) (Δ ++ctx Θ)
multi⊹ ◇            σ = σ
multi⊹ (Θ ,, x ∈ T) σ = (multi⊹ Θ σ) ⊹⟨ x ⟩

cong₃ : {A B C D : Set} (f : A → B → C → D)
        {a a' : A} {b b' : B} {c c' : C} →
        a ≡ a' → b ≡ b' → c ≡ c' →
        f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

var-weaken-subst-trivial-multi : (Θ : CtxExpr) (v : Var x (Γ ++ctx Θ)) {s : TmExpr Γ S} (e : lookup-var (mid-weaken-var Θ v) ≡ lookup-var v) →
  (var' x {mid-weaken-var Θ v} {e}) [ multi⊹ Θ (s / y) ]tm ≡ var' x {v} {refl}
var-weaken-subst-trivial-multi ◇ v refl = refl
var-weaken-subst-trivial-multi (Θ ,, x ∈ T) vzero refl = refl
var-weaken-subst-trivial-multi (◇ ,, x ∈ T) (vsuc v) refl = refl
var-weaken-subst-trivial-multi (Θ ,, x ∈ T ,, y ∈ S) (vsuc v) e = cong weaken-tm (var-weaken-subst-trivial-multi (Θ ,, x ∈ T) v e)

tm-weaken-subst-trivial-multi : (Θ : CtxExpr) (t : TmExpr (Γ ++ctx Θ) T) {s : TmExpr Γ S} → (mid-weaken-tm Θ t) [ multi⊹ Θ (s / x) ]tm ≡ t
tm-weaken-subst-trivial-multi ◇ (var' x {_} {refl}) = refl
tm-weaken-subst-trivial-multi ◇ (lam[ _ ∈ _ ] t) = cong (lam[ _ ∈ _ ]_) (tm-weaken-subst-trivial-multi (◇ ,, _ ∈ _) t)
tm-weaken-subst-trivial-multi ◇ (f ∙ t) = cong₂ _∙_ (tm-weaken-subst-trivial-multi ◇ f) (tm-weaken-subst-trivial-multi ◇ t)
tm-weaken-subst-trivial-multi ◇ zero = refl
tm-weaken-subst-trivial-multi ◇ suc = refl
tm-weaken-subst-trivial-multi ◇ (nat-elim a f) = cong₂ nat-elim (tm-weaken-subst-trivial-multi ◇ a) (tm-weaken-subst-trivial-multi ◇ f)
tm-weaken-subst-trivial-multi ◇ true = refl
tm-weaken-subst-trivial-multi ◇ false = refl
tm-weaken-subst-trivial-multi ◇ (if b t f) =
  cong₃ if (tm-weaken-subst-trivial-multi ◇ b) (tm-weaken-subst-trivial-multi ◇ t) (tm-weaken-subst-trivial-multi ◇ f)
tm-weaken-subst-trivial-multi ◇ (pair t s) = cong₂ pair (tm-weaken-subst-trivial-multi ◇ t) (tm-weaken-subst-trivial-multi ◇ s)
tm-weaken-subst-trivial-multi ◇ (fst p) = cong fst (tm-weaken-subst-trivial-multi ◇ p)
tm-weaken-subst-trivial-multi ◇ (snd p) = cong snd (tm-weaken-subst-trivial-multi ◇ p)
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (var' _ {v} {refl}) = var-weaken-subst-trivial-multi (Θ ,, _ ∈ T) v (mid-weaken-var-ty (Θ ,, _ ∈ _) v)
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (lam[ _ ∈ _ ] t) = cong (lam[ _ ∈ _ ]_) (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T ,, _ ∈ _) t)
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (f ∙ t) = cong₂ _∙_ (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) f) (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) t)
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) zero = refl
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) suc = refl
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (nat-elim a f) = cong₂ nat-elim (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) a) (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) f)
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) true = refl
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) false = refl
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (if b t f) =
  cong₃ if (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) b) (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) t) (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) f)
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (pair t s) = cong₂ pair (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) t) (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) s)
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (fst p) = cong fst (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) p)
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (snd p) = cong snd (tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) p)

tm-weaken-subst-trivial : (t : TmExpr Γ T) (s : TmExpr Γ S) → (t [ π ]tm) [ s / x ]tm ≡ t
tm-weaken-subst-trivial t s = tm-weaken-subst-trivial-multi ◇ t
