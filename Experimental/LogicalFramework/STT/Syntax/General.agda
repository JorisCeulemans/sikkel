--------------------------------------------------
-- Definition of STT contexts, terms and their associated operations
--   The general syntax is parametrised by a type of names to represent
--   variables. It is not recommended to directly import this module,
--   but rather use STT.Syntax.Named.
--------------------------------------------------

module Experimental.LogicalFramework.STT.Syntax.General (Name : Set) where

open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.STT.ModeTheory
open import Experimental.LogicalFramework.STT.Syntax.Types

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  T S : Ty m
  x y : Name


--------------------------------------------------
-- Definition of STT contexts and terms

infixl 4 _,,_∣_∈_
data Ctx (m : Mode) : Set where
  ◇ : Ctx m
  _,,_∣_∈_ : (Γ : Ctx m) (μ : Modality n m) (x : Name) (T : Ty n) → Ctx m
    -- ^ All variables have a name of type Name and appear under a modality.
  _,lock⟨_⟩ : (Γ : Ctx n) (μ : Modality m n) → Ctx m

private variable
  Γ Δ Θ : Ctx m


-- The predicate Var x μ T κ Γ expresses that a variable named x is
-- present in context Γ under modality μ with type T and with κ the
-- composition of all locks to the right of x. Note that this is a
-- proof-relevant predicate and names in Γ may not be unique (but this
-- is of course discouraged).  As a result, STT terms internally
-- represent variables using De Bruijn indices, but we do keep track
-- of the names of the variables.
data Var (x : Name) (μ : Modality n o) (T : Ty n) : Modality m o → Ctx m → Set where
  vzero : Var x μ T 𝟙 (Γ ,, μ ∣ x ∈ T)
  vsuc : Var x μ T κ Γ → Var x μ T κ (Γ ,, ρ ∣ y ∈ S)
  skip-lock : (ρ : Modality m p) → Var x μ T κ Γ → Var x μ T (κ ⓜ ρ) (Γ ,lock⟨ ρ ⟩)

infixl 50 _∙_
data Tm (Γ : Ctx m) : Ty m → Set where
  var' : (x : Name) {μ : Modality m n} {v : Var x μ T κ Γ} → TwoCell μ κ → Tm Γ T
  -- ^ When writing programs, one should not directly use var' but rather combine
  --   it with a decision procedure for Var, which will resolve the name.
  lam[_∈_]_ : (x : Name) (T : Ty m) → Tm (Γ ,, 𝟙 ∣ x ∈ T) S → Tm Γ (T ⇛ S)
  _∙_ : Tm Γ (T ⇛ S) → Tm Γ T → Tm Γ S
  zero : Tm Γ Nat'
  suc : Tm Γ (Nat' ⇛ Nat')
  nat-elim : {A : Ty m} → Tm Γ A → Tm Γ (A ⇛ A) → Tm Γ (Nat' ⇛ A)
  true false : Tm Γ Bool'
  if : {A : Ty m} → Tm Γ Bool' → (t f : Tm Γ A) → Tm Γ A
  pair : Tm Γ T → Tm Γ S → Tm Γ (T ⊠ S)
  fst : Tm Γ (T ⊠ S) → Tm Γ T
  snd : Tm Γ (T ⊠ S) → Tm Γ S
  mod⟨_⟩_ : (μ : Modality n m) → Tm (Γ ,lock⟨ μ ⟩) T → Tm Γ ⟨ μ ∣ T ⟩
  mod-elim : (ρ : Modality o m) (μ : Modality n o) (x : Name)
             (t : Tm (Γ ,lock⟨ ρ ⟩) ⟨ μ ∣ T ⟩) (s : Tm (Γ ,, ρ ⓜ μ ∣ x ∈ T) S) →
             Tm Γ S

syntax mod-elim ρ μ x t s = let⟨ ρ ⟩ mod⟨ μ ⟩ x ← t in' s

mod-elim' : (μ : Modality n m) (x : Name) (t : Tm Γ ⟨ μ ∣ T ⟩) (s : Tm (Γ ,, μ ∣ x ∈ T) S) → Tm Γ S
mod-elim' = {!mod-elim 𝟙!}

syntax mod-elim' μ x t s = let' mod⟨ μ ⟩ x ← t in' s


private
  coe[_]_ : Name → TwoCell μ ρ → Tm Γ ⟨ μ ∣ T ⟩ → Tm Γ ⟨ ρ ∣ T ⟩
  coe[_]_ {μ = μ} {ρ = ρ} x α t = let' mod⟨ μ ⟩ x ← t in' (mod⟨ ρ ⟩ var' x {_} {skip-lock ρ vzero} {!α!})

  triv : Tm Γ T → Tm Γ ⟨ 𝟙 ∣ T ⟩
  triv t = mod⟨ 𝟙 ⟩ {!t!}

  triv⁻¹ : Name → Tm Γ ⟨ 𝟙 ∣ T ⟩ → Tm Γ T
  triv⁻¹ x t = let' mod⟨ 𝟙 ⟩ x ← t in' var' x {_} {vzero} id-cell

  comp : Name → Name → Tm Γ ⟨ μ ∣ ⟨ ρ ∣ T ⟩ ⟩ → Tm Γ ⟨ μ ⓜ ρ ∣ T ⟩
  comp {μ = μ} {ρ = ρ} x y t =
    let' mod⟨ μ ⟩ x ← t in'
    let⟨ μ ⟩ mod⟨ ρ ⟩ y ← var' x {_} {skip-lock _ vzero} {!id-cell!} in'
    (mod⟨ μ ⓜ ρ ⟩ var' y {_} {skip-lock _ vzero} {!id-cell!})

  comp⁻¹ : Name → Tm Γ ⟨ μ ⓜ ρ ∣ T ⟩ → Tm Γ ⟨ μ ∣ ⟨ ρ ∣ T ⟩ ⟩
  comp⁻¹ {μ = μ} {ρ = ρ} x t = let' mod⟨ μ ⓜ ρ ⟩ x ← t in' (mod⟨ μ ⟩ (mod⟨ ρ ⟩ var' x {_} {skip-lock _ (skip-lock _ vzero)} {!id-cell!}))


--------------------------------------------------
-- Weakening of terms

data Telescope : (m n : Mode) → Set where
  ◇t : Telescope m m
  _,,_∣_∈_ : Telescope m n → Modality o n → Name → Ty o → Telescope m n
  _,lock⟨_⟩ : Telescope m n → Modality o n → Telescope m o

_++tel_ : Ctx m → Telescope m n → Ctx n
Γ ++tel ◇t = Γ
Γ ++tel (Δ ,, μ ∣ x ∈ T) = (Γ ++tel Δ) ,, μ ∣ x ∈ T
Γ ++tel (Δ ,lock⟨ μ ⟩) = (Γ ++tel Δ) ,lock⟨ μ ⟩
{-
mid-weaken-var : {Γ : Ctx m} {φ : Modality n m} (Δ : Telescope m n φ) →
                 Var x μ T (κ ⓜ φ) (Γ ++tel Δ) →
                 Var x μ T (κ ⓜ φ) ((Γ ,, ρ ∣ y ∈ S) ++tel Δ)
mid-weaken-var ◇t v = vsuc v
mid-weaken-var (Δ ,, _ ∣ _ ∈ _) vzero = vzero
mid-weaken-var (Δ ,, _ ∣ _ ∈ _) (vsuc v) = vsuc (mid-weaken-var Δ v)
mid-weaken-var (Δ ,lock⟨ μ ⟩) v = {!skip-lock μ {!!}!}

mid-weaken-var ◇            v        = vsuc v
mid-weaken-var (Δ ,, _ ∈ R) vzero    = vzero
mid-weaken-var (Δ ,, _ ∈ R) (vsuc v) = vsuc (mid-weaken-var Δ v)

mid-weaken-tm : ∀ (Δ : Ctx) → Tm (Γ ++tel Δ) T → Tm ((Γ ,, x ∈ S) ++tel Δ) T
mid-weaken-tm Δ (var' x {v}) = var' x {mid-weaken-var Δ v}
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

weaken-tm : Tm Γ T → Tm (Γ ,, x ∈ S) T
weaken-tm t = mid-weaken-tm ◇ t

multi-weaken-tm : (Δ : Ctx) → Tm Γ T → Tm (Γ ++tel Δ) T
multi-weaken-tm ◇            t = t
multi-weaken-tm (Δ ,, x ∈ T) t = weaken-tm (multi-weaken-tm Δ t)
-}

--------------------------------------------------
-- Syntactic substitutions

data LockFreeTele (m : Mode) : Set where
  ◇t : LockFreeTele m
  _,,_∣_∈_ : LockFreeTele m → Modality n m → Name → Ty n → LockFreeTele m

_++lft_ : Ctx m → LockFreeTele m → Ctx m
Γ ++lft ◇t = Γ
Γ ++lft (Δ ,, μ ∣ x ∈ T) = (Γ ++lft Δ) ,, μ ∣ x ∈ T

-- With the following data type, there are multiple ways to represent
-- the same substitution. This is not a problem since we will never
-- compare substitutions (only apply them to terms and compute
-- immediately). Having a constructor for e.g. the identity seems more
-- efficient than implementing it (but this claim needs justification).
data Subst : Ctx m → Ctx m → Set where
  [] : Subst Γ ◇
  _∷_/_ : Subst Δ Γ → Tm (Δ ,lock⟨ μ ⟩) T → (x : Name) → Subst Δ (Γ ,, μ ∣ x ∈ T)
  id-subst : (Γ : Ctx m) → Subst Γ Γ
  _⊚πs⟨_⟩ : Subst Δ Γ → (Θ : LockFreeTele m) → Subst (Δ ++lft Θ) Γ
  _,lock⟨_⟩ : Subst Δ Γ → (μ : Modality m n) → Subst (Δ ,lock⟨ μ ⟩) (Γ ,lock⟨ μ ⟩)
  key : TwoCell μ ρ → Subst (Γ ,lock⟨ ρ ⟩) (Γ ,lock⟨ μ ⟩)

π : Subst (Γ ,, μ ∣ x ∈ T) Γ
π = id-subst _ ⊚πs⟨ _ ⟩

_⊚π : Subst Δ Γ → Subst (Δ ,, μ ∣ x ∈ T) Γ
σ ⊚π = σ ⊚πs⟨ _ ⟩

_⊹⟨_⟩ : Subst Δ Γ → (x : Name) → Subst (Δ ,, μ ∣ x ∈ T) (Γ ,, μ ∣ x ∈ T)
σ ⊹⟨ x ⟩ = (σ ⊚π) ∷ var' x {_} {skip-lock _ vzero} {!id-cell!} / x

_/_ : Tm (Γ ,lock⟨ μ ⟩) T → (x : Name) → Subst Γ (Γ ,, μ ∣ x ∈ T)
t / x = id-subst _ ∷ t / x


--------------------------------------------------
-- Applying a substitution to a term
--   Note that the operation _[_]tm is automatically capture-avoiding
--   since it only makes use of the De Bruijn indices, not of names.

-- We will use the following view pattern in the implementation of
-- substitution for terms, in order to treat some substitutions
-- specially.
data SpecialSubst : Subst Γ Δ → Set where
  id-subst : (Γ : Ctx m) → SpecialSubst (id-subst Γ)
  _⊚πs⟨_⟩ : {Γ Δ : Ctx m} (σ : Subst Γ Δ) → (Θ : LockFreeTele m) → SpecialSubst (σ ⊚πs⟨ Θ ⟩)

is-special-subst? : (σ : Subst Γ Δ) → Maybe (SpecialSubst σ)
is-special-subst? []           = nothing
is-special-subst? (σ ∷ t / x)  = nothing
is-special-subst? (id-subst Γ) = just (id-subst Γ)
is-special-subst? (σ ⊚πs⟨ Θ ⟩) = just (σ ⊚πs⟨ Θ ⟩)
is-special-subst? (σ ,lock⟨ μ ⟩) = nothing
is-special-subst? (key α) = nothing

subst-var : {Γ : Ctx m} {μ : Modality n o} {κ : Modality m o} (v : Var x μ T κ Γ) →
            (ρ : Modality n m) → TwoCell μ (κ ⓜ ρ) → Subst Δ Γ → Tm (Δ ,lock⟨ ρ ⟩) T
subst-var {x = x} v ρ α (id-subst _) = var' x {_} {skip-lock ρ v} α
subst-var v ρ α (σ ⊚πs⟨ ◇t ⟩) = subst-var v ρ α σ
subst-var v ρ α (σ ⊚πs⟨ Θ ,, _ ∣ _ ∈ _ ⟩) = {!!}
subst-var vzero ρ α (σ ∷ t / x) = {!t [ key α ]tm!}
subst-var (vsuc v) ρ α (σ ∷ t / x) = subst-var v ρ α σ
subst-var (skip-lock .μ v) ρ α (σ ,lock⟨ μ ⟩) = {!subst-var v (μ ⓜ ρ) {!α!} σ!}
subst-var {x = x} (skip-lock _ v) ρ α (key β) = var' x {_} {skip-lock _ (skip-lock _ v)} (((id-cell ⓣ-hor β) ⓣ-hor id-cell {_}{_}{ρ}) ⓣ-vert α)

{-
subst-var : (v : Var x μ T κ Γ) → TwoCell μ κ → Subst Δ Γ → Tm Δ T
subst-var {x = x} v α (id-subst _) = var' x {v = v} α
subst-var v α (σ ⊚πs⟨ ◇t ⟩) = subst-var v α σ
subst-var v α (σ ⊚πs⟨ Θ ,, _ ∣ _ ∈ _ ⟩) = {!!}
subst-var vzero α (σ ∷ t / x) = {!t [ key α ]tm!}
subst-var (vsuc v) α (σ ∷ t / x) = subst-var v α σ
subst-var (skip-lock .μ v) α (σ ,lock⟨ μ ⟩) = {!subst-var v ? ?!}
subst-var {x = x} (skip-lock μ v) α (key {ρ = ρ} β) = var' x {v = skip-lock ρ v} ((id-cell ⓣ-hor β) ⓣ-vert α)
-}
{-
subst-var {x = x} v (id-subst Γ) = var' x {v}
subst-var v         (σ ⊚πs⟨ ◇ ⟩) = subst-var v σ
subst-var v         (σ ⊚πs⟨ Δ ,, _ ∈ T ⟩) = weaken-tm (subst-var v (σ ⊚πs⟨ Δ ⟩))
subst-var vzero     (σ ∷ t / x) = t
subst-var (vsuc v)  (σ ∷ s / x) = subst-var v σ
-}
_[_]tm : Tm Γ T → Subst Δ Γ → Tm Δ T
t [ σ ]tm with is-special-subst? σ
(t [ .(id-subst Γ) ]tm)  | just (id-subst Γ) = t
(t [ .(σ ⊚πs⟨ Θ ⟩) ]tm)  | just (σ ⊚πs⟨ Θ ⟩) = {!multi-weaken-tm Θ (t [ σ ]tm)!}
(var' x {_}{v} α) [ σ ]tm | nothing = {!subst-var v α σ!}
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
(mod⟨ μ ⟩ t) [ σ ]tm      | nothing = mod⟨ μ ⟩ (t [ σ ,lock⟨ μ ⟩ ]tm)
(mod-elim ρ μ x t s) [ σ ]tm | nothing = mod-elim ρ μ x (t [ σ ,lock⟨ ρ ⟩ ]tm) (s [ σ ⊹⟨ x ⟩ ]tm)
{-

--------------------------------------------------
-- Proving that substituting the most recently added variable in a
--   weakened term has no effect.

multi⊹ : (Θ : Ctx) → Subst Γ Δ → Subst (Γ ++tel Θ) (Δ ++tel Θ)
multi⊹ ◇            σ = σ
multi⊹ (Θ ,, x ∈ T) σ = (multi⊹ Θ σ) ⊹⟨ x ⟩

cong₃ : {A B C D : Set} (f : A → B → C → D)
        {a a' : A} {b b' : B} {c c' : C} →
        a ≡ a' → b ≡ b' → c ≡ c' →
        f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

var-weaken-subst-trivial-multi : (Θ : Ctx) (v : Var x (Γ ++tel Θ) T) {s : Tm Γ S} →
  (var' x {mid-weaken-var Θ v}) [ multi⊹ Θ (s / y) ]tm ≡ var' x {v}
var-weaken-subst-trivial-multi ◇ v = refl
var-weaken-subst-trivial-multi (Θ ,, x ∈ T) vzero = refl
var-weaken-subst-trivial-multi (◇ ,, x ∈ T) (vsuc v) = refl
var-weaken-subst-trivial-multi (Θ ,, x ∈ T ,, y ∈ S) (vsuc v) = cong weaken-tm (var-weaken-subst-trivial-multi (Θ ,, x ∈ T) v)

tm-weaken-subst-trivial-multi : (Θ : Ctx) (t : Tm (Γ ++tel Θ) T) {s : Tm Γ S} → (mid-weaken-tm Θ t) [ multi⊹ Θ (s / x) ]tm ≡ t
tm-weaken-subst-trivial-multi ◇ (var' x {_}) = refl
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
tm-weaken-subst-trivial-multi (Θ ,, _ ∈ T) (var' _ {v}) = var-weaken-subst-trivial-multi (Θ ,, _ ∈ T) v
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

tm-weaken-subst-trivial : (t : Tm Γ T) (s : Tm Γ S) → (t [ π ]tm) [ s / x ]tm ≡ t
tm-weaken-subst-trivial t s = tm-weaken-subst-trivial-multi ◇ t
-}
