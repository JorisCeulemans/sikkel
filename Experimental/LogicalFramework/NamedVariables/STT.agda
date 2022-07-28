--------------------------------------------------
-- A Simple Type Theory for which we will provide a logic
--------------------------------------------------

module Experimental.LogicalFramework.NamedVariables.STT where

open import Data.Empty
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.String as Str
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core

open import Model.BaseCategory
open import Model.CwF-Structure as M using (Ctx; Ty; Tm)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Discrete as M

open import Experimental.ClosedTypes as M


--------------------------------------------------
-- Definition of syntactic types, contexts and terms

infixr 6 _⇛_
infixl 5 _⊠_
data TyExpr : Set where
  Nat' : TyExpr
  Bool' : TyExpr
  _⇛_ : TyExpr → TyExpr → TyExpr
  _⊠_ : TyExpr → TyExpr → TyExpr

private variable
  T S : TyExpr


infixl 4 _,,_∈_
data CtxExpr : Set where
  ◇ : CtxExpr
  _,,_∈_ : (Γ : CtxExpr) (x : String) (T : TyExpr) → CtxExpr

private variable
  Γ Δ Θ : CtxExpr


-- Variables are represented as de Bruijn indices, but we keep track
-- of their names.
data Var : String → CtxExpr → Set where
  vzero : ∀ {x} → Var x (Γ ,, x ∈ T)
  vsuc : ∀ {x y} → Var x Γ → Var x (Γ ,, y ∈ S)

vpred : ∀ {x y} → ¬ (x ≡ y) → Var x (Γ ,, y ∈ S) → Var x Γ
vpred ¬x=y vzero    = ⊥-elim (¬x=y refl)
vpred ¬x=y (vsuc v) = v

var? : (x : String) (Γ : CtxExpr) → Dec (Var x Γ)
var? x ◇ = no (λ ())
var? x (Γ ,, y ∈ T) with x Str.≟ y
var? x (Γ ,, .x ∈ T) | yes refl = yes vzero
var? x (Γ ,, y ∈ T)  | no ¬x=y = map′ vsuc (vpred ¬x=y) (var? x Γ)

lookup-var : ∀ {x} → Var x Γ → TyExpr
lookup-var (vzero {Γ} {T}) = T
lookup-var (vsuc v) = lookup-var v

infixl 50 _∙_
data TmExpr (Γ : CtxExpr) : TyExpr → Set where
  var' : (x : String) {v : Var x Γ} → {lookup-var v ≡ T} → TmExpr Γ T
  lam[_∈_]_ : (x : String) (T : TyExpr) → TmExpr (Γ ,, x ∈ T) S → TmExpr Γ (T ⇛ S)
  _∙_ : TmExpr Γ (T ⇛ S) → TmExpr Γ T → TmExpr Γ S
  zero : TmExpr Γ Nat'
  suc : TmExpr Γ (Nat' ⇛ Nat')
  nat-elim : {A : TyExpr} → TmExpr Γ A → TmExpr Γ (A ⇛ A) → TmExpr Γ (Nat' ⇛ A)
  true false : TmExpr Γ Bool'
  if : {A : TyExpr} → TmExpr Γ Bool' → (t f : TmExpr Γ A) → TmExpr Γ A
  pair : TmExpr Γ T → TmExpr Γ S → TmExpr Γ (T ⊠ S)
  fst : TmExpr Γ (T ⊠ S) → TmExpr Γ T
  snd : TmExpr Γ (T ⊠ S) → TmExpr Γ S

-- Constructing a variable term by only mentioning the variable name
-- (i.e. resolving the De Bruijn index automatically)
var : (x : String) → {v : True (var? x Γ)} → TmExpr Γ (lookup-var (toWitness v))
var x {v} = var' x {toWitness v} {refl}


--------------------------------------------------
-- Interpretation of types, contexts and terms in the presheaf
--   model over the trivial base category

⟦_⟧ty : TyExpr → ClosedTy ★
⟦ Nat' ⟧ty = M.Nat'
⟦ Bool' ⟧ty = M.Bool'
⟦ T ⇛ S ⟧ty = ⟦ T ⟧ty M.⇛ ⟦ S ⟧ty
⟦ T ⊠ S ⟧ty = ⟦ T ⟧ty M.⊠ ⟦ S ⟧ty

⟦_⟧ctx : CtxExpr → Ctx ★
⟦ ◇ ⟧ctx = M.◇
⟦ Γ ,, _ ∈ T ⟧ctx = ⟦ Γ ⟧ctx ,,ₛ ⟦ T ⟧ty

⟦_⟧var : ∀ {x} → (v : Var x Γ) → SimpleTm ⟦ Γ ⟧ctx ⟦ lookup-var v ⟧ty
⟦ vzero ⟧var = sξ
⟦ vsuc v ⟧var = ⟦ v ⟧var [ M.π ]s

⟦_⟧tm : TmExpr Γ T → SimpleTm ⟦ Γ ⟧ctx ⟦ T ⟧ty
⟦ var' _ {v} {refl} ⟧tm = ⟦ v ⟧var
⟦ lam[ _ ∈ _ ] t ⟧tm = sλ[ _ ] ⟦ t ⟧tm
⟦ f ∙ t ⟧tm = ⟦ f ⟧tm ∙ₛ ⟦ t ⟧tm
⟦ zero ⟧tm = szero
⟦ suc ⟧tm = ssuc
⟦ nat-elim a f ⟧tm = snat-elim ⟦ a ⟧tm ⟦ f ⟧tm
⟦ true ⟧tm = strue
⟦ false ⟧tm = sfalse
⟦ if b t f ⟧tm = sif ⟦ b ⟧tm ⟦ t ⟧tm ⟦ f ⟧tm
⟦ pair t s ⟧tm = spair ⟦ t ⟧tm ⟦ s ⟧tm
⟦ fst p ⟧tm = sfst ⟦ p ⟧tm
⟦ snd p ⟧tm = ssnd ⟦ p ⟧tm


--------------------------------------------------
-- Definition of some operations on contexts and terms,
--   most notably weakening of a term.

_++ctx_ : CtxExpr → CtxExpr → CtxExpr
Γ ++ctx ◇ = Γ
Γ ++ctx (Δ ,, x ∈ T) = (Γ ++ctx Δ) ,, x ∈ T

mid-weaken-var : ∀ {x y} {Γ : CtxExpr} (Δ : CtxExpr) → Var x (Γ ++ctx Δ) → Var x ((Γ ,, y ∈ S) ++ctx Δ)
mid-weaken-var ◇            v        = vsuc v
mid-weaken-var (Δ ,, _ ∈ R) vzero    = vzero
mid-weaken-var (Δ ,, _ ∈ R) (vsuc v) = vsuc (mid-weaken-var Δ v)

mid-weaken-var-ty : ∀ {x y S} {Γ : CtxExpr} (Δ : CtxExpr) (v : Var x (Γ ++ctx Δ)) →
                    lookup-var (mid-weaken-var {S = S} {y = y} Δ v) ≡ lookup-var v
mid-weaken-var-ty ◇            v        = refl
mid-weaken-var-ty (Δ ,, _ ∈ R) vzero    = refl
mid-weaken-var-ty (Δ ,, _ ∈ R) (vsuc v) = mid-weaken-var-ty Δ v

mid-weaken-tm : ∀ {x} (Δ : CtxExpr) → TmExpr (Γ ++ctx Δ) T → TmExpr ((Γ ,, x ∈ S) ++ctx Δ) T
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

weaken-tm : ∀ {x} → TmExpr Γ T → TmExpr (Γ ,, x ∈ S) T
weaken-tm t = mid-weaken-tm ◇ t

multi-weaken-tm : (Δ : CtxExpr) → TmExpr Γ T → TmExpr (Γ ++ctx Δ) T
multi-weaken-tm ◇            t = t
multi-weaken-tm (Δ ,, x ∈ T) t = weaken-tm (multi-weaken-tm Δ t)

mid-weaken-sem-subst : (x : String) {Γ : CtxExpr} (S : TyExpr) (Δ : CtxExpr) → ⟦ (Γ ,, x ∈ S) ++ctx Δ ⟧ctx M.⇒ ⟦ Γ ++ctx Δ ⟧ctx
mid-weaken-sem-subst _ S ◇ = M.π
mid-weaken-sem-subst x S (Δ ,, _ ∈ T) = mid-weaken-sem-subst x S Δ s⊹

mid-weaken-var-sound : ∀ {x y} {Γ : CtxExpr} (Δ : CtxExpr) (v : Var x (Γ ++ctx Δ)) →
                       (⟦ v ⟧var [ mid-weaken-sem-subst y S Δ ]s) M.≅ᵗᵐ ⟦ var' x {mid-weaken-var Δ v} {mid-weaken-var-ty Δ v} ⟧tm
mid-weaken-var-sound ◇            v = M.≅ᵗᵐ-refl
mid-weaken-var-sound (Δ ,, _ ∈ T) vzero    = ,ₛ-β2 _ sξ
mid-weaken-var-sound (Δ ,, _ ∈ T) (vsuc v) =
  M.≅ᵗᵐ-trans (stm-subst-comp ⟦ v ⟧var M.π _)
              (M.≅ᵗᵐ-trans (stm-subst-cong-subst ⟦ v ⟧var (,ₛ-β1 _ sξ))
                           (M.≅ᵗᵐ-trans (M.≅ᵗᵐ-sym (stm-subst-comp ⟦ v ⟧var _ M.π))
                                        (M.≅ᵗᵐ-trans (stm-subst-cong-tm (mid-weaken-var-sound Δ v) M.π)
                                                     (varπ (mid-weaken-var Δ v) (mid-weaken-var-ty Δ v)))))
  where
    varπ : ∀ {x y T S} (v : Var x Γ) (e : lookup-var v ≡ T) →
           (⟦ var' x {v} {e} ⟧tm M.[ M.π ]s) M.≅ᵗᵐ ⟦ var' x {vsuc {S = S} {y = y} v} {e} ⟧tm
    varπ v refl = M.≅ᵗᵐ-refl

mid-weaken-tm-sound : ∀ {x} {S : TyExpr} (Δ : CtxExpr) (t : TmExpr (Γ ++ctx Δ) T) →
                      (⟦ t ⟧tm [ mid-weaken-sem-subst x S Δ ]s) M.≅ᵗᵐ ⟦ mid-weaken-tm {S = S} Δ t ⟧tm
mid-weaken-tm-sound Δ (var' x {v} {refl}) = mid-weaken-var-sound Δ v
mid-weaken-tm-sound Δ (lam[ _ ∈ _ ] t) = M.≅ᵗᵐ-trans (sλ-natural _) (sλ-cong (mid-weaken-tm-sound (Δ ,, _ ∈ _) t))
mid-weaken-tm-sound Δ (f ∙ t) = M.≅ᵗᵐ-trans (∙ₛ-natural _) (∙ₛ-cong (mid-weaken-tm-sound Δ f) (mid-weaken-tm-sound Δ t))
mid-weaken-tm-sound Δ zero = sdiscr-natural _
mid-weaken-tm-sound Δ suc = sdiscr-func-natural _
mid-weaken-tm-sound Δ (nat-elim a f) = M.≅ᵗᵐ-trans (snat-elim-natural _) (snat-elim-cong (mid-weaken-tm-sound Δ a) (mid-weaken-tm-sound Δ f))
mid-weaken-tm-sound Δ true = sdiscr-natural _
mid-weaken-tm-sound Δ false = sdiscr-natural _
mid-weaken-tm-sound Δ (if b t f) =
  M.≅ᵗᵐ-trans (sif-natural _) (sif-cong (mid-weaken-tm-sound Δ b) (mid-weaken-tm-sound Δ t) (mid-weaken-tm-sound Δ f))
mid-weaken-tm-sound Δ (pair t s) = M.≅ᵗᵐ-trans (spair-natural _) (spair-cong (mid-weaken-tm-sound Δ t) (mid-weaken-tm-sound Δ s))
mid-weaken-tm-sound Δ (fst p) = M.≅ᵗᵐ-trans (sfst-natural _) (sfst-cong (mid-weaken-tm-sound Δ p))
mid-weaken-tm-sound Δ (snd p) = M.≅ᵗᵐ-trans (ssnd-natural _) (ssnd-cong (mid-weaken-tm-sound Δ p))

weaken-tm-sound : ∀ {x} {S : TyExpr} (t : TmExpr Γ T) → (⟦ t ⟧tm [ M.π ]s) M.≅ᵗᵐ ⟦ weaken-tm {S = S} {x = x} t ⟧tm
weaken-tm-sound t = mid-weaken-tm-sound ◇ t


--------------------------------------------------
-- Syntactic substitutions

-- With the following data type, there are multiple ways to represent
-- the same substitution. This is not a problem since we will never
-- compare substitutions (only apply them to terms and compute
-- immediately). Having a constructor for e.g. the identity seems more
-- efficient than implementing it (claim needs justification).
data SubstExpr : CtxExpr → CtxExpr → Set where
  [] : SubstExpr Γ ◇
  _∷_/_ : SubstExpr Δ Γ → TmExpr Δ T → (x : String) → SubstExpr Δ (Γ ,, x ∈ T)
  id-subst : (Γ : CtxExpr) → SubstExpr Γ Γ
  _⊚πs⟨_⟩ : SubstExpr Δ Γ → (Θ : CtxExpr) → SubstExpr (Δ ++ctx Θ) Γ

π : ∀ {x} → SubstExpr (Γ ,, x ∈ T) Γ
π = id-subst _ ⊚πs⟨ _ ⟩

_⊚π : ∀ {x} → SubstExpr Δ Γ → SubstExpr (Δ ,, x ∈ T) Γ
σ ⊚π = σ ⊚πs⟨ _ ⟩

_⊹⟨_⟩ : SubstExpr Δ Γ → (x : String) → SubstExpr (Δ ,, x ∈ T) (Γ ,, x ∈ T)
σ ⊹⟨ x ⟩ = (σ ⊚π) ∷ var' x {vzero} {refl} / x

_/_ : TmExpr Γ T → (x : String) → SubstExpr Γ (Γ ,, x ∈ T)
t / x = id-subst _ ∷ t / x


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

subst-var : ∀ {x T} → (v : Var x Γ) → SubstExpr Δ Γ → lookup-var v ≡ T → TmExpr Δ T
subst-var {x = x} v (id-subst Γ) e = var' x {v} {e}
subst-var v         (σ ⊚πs⟨ ◇ ⟩) e = subst-var v σ e
subst-var v         (σ ⊚πs⟨ Δ ,, _ ∈ T ⟩) e = weaken-tm (subst-var v (σ ⊚πs⟨ Δ ⟩) e)
subst-var vzero     (σ ∷ t / x) refl = t
subst-var (vsuc v)  (σ ∷ s / x) e = subst-var v σ e

_[_]tm : TmExpr Γ T → SubstExpr Δ Γ → TmExpr Δ T
t [ σ ]tm with is-special-subst? σ
(t [ .(id-subst Γ) ]tm)  | just (id-subst Γ) = t
(t [ .(σ ⊚πs⟨ Θ ⟩) ]tm)  | just (σ ⊚πs⟨ Θ ⟩) = multi-weaken-tm Θ (t [ σ ]tm)
var' x {v} {e} [ σ ]tm   | nothing = subst-var v σ e
(lam[ x ∈ T ] t) [ σ ]tm | nothing = lam[ x ∈ T ] (t [ σ ⊹⟨ x ⟩ ]tm)
(f ∙ t) [ σ ]tm          | nothing = (f [ σ ]tm) ∙ (t [ σ ]tm)
zero [ σ ]tm             | nothing = zero
suc [ σ ]tm              | nothing = suc
nat-elim a f [ σ ]tm     | nothing = nat-elim (a [ σ ]tm) (f [ σ ]tm)
true [ σ ]tm             | nothing = true
false [ σ ]tm            | nothing = false
if b t f [ σ ]tm         | nothing = if (b [ σ ]tm) (t [ σ ]tm) (f [ σ ]tm)
pair t s [ σ ]tm         | nothing = pair (t [ σ ]tm) (s [ σ ]tm)
fst p [ σ ]tm            | nothing = fst (p [ σ ]tm)
snd p [ σ ]tm            | nothing = snd (p [ σ ]tm)


-- Interpretation of substitutions as presheaf morphisms
⟦_⟧subst : SubstExpr Δ Γ → (⟦ Δ ⟧ctx M.⇒ ⟦ Γ ⟧ctx)
⟦ [] ⟧subst = M.!◇ _
⟦ _∷_/_ {_} {T} σ t _ ⟧subst = ⟦ σ ⟧subst ,ₛ ⟦ t ⟧tm
⟦ id-subst Γ ⟧subst = M.id-subst _
⟦ σ ⊚πs⟨ ◇ ⟩      ⟧subst = ⟦ σ ⟧subst
⟦ σ ⊚πs⟨ Δ ,, _ ∈ T ⟩ ⟧subst = ⟦ σ ⊚πs⟨ Δ ⟩ ⟧subst M.⊚ M.π

⊹-sound : ∀ {x} (σ : SubstExpr Δ Γ) {T : TyExpr} → (⟦ σ ⟧subst s⊹) M.≅ˢ ⟦ _⊹⟨_⟩ {T = T} σ x ⟧subst
⊹-sound σ = M.≅ˢ-refl

subst-var-sound : ∀ {x} (v : Var x Γ) (σ : SubstExpr Δ Γ) → (⟦ v ⟧var [ ⟦ σ ⟧subst ]s) M.≅ᵗᵐ ⟦ subst-var v σ refl ⟧tm
subst-var-sound vzero    (σ ∷ t / x) = ,ₛ-β2 ⟦ σ ⟧subst ⟦ t ⟧tm
subst-var-sound (vsuc v) (σ ∷ t / x) =
  M.≅ᵗᵐ-trans (stm-subst-comp ⟦ v ⟧var M.π (⟦ σ ⟧subst ,ₛ ⟦ t ⟧tm))
              (M.≅ᵗᵐ-trans (stm-subst-cong-subst (⟦ v ⟧var) (,ₛ-β1 ⟦ σ ⟧subst ⟦ t ⟧tm))
                           (subst-var-sound v σ))
subst-var-sound v (id-subst Γ) = stm-subst-id _
subst-var-sound v (σ ⊚πs⟨ ◇ ⟩)      = subst-var-sound v σ
subst-var-sound v (σ ⊚πs⟨ Δ ,, _ ∈ T ⟩) =
  M.≅ᵗᵐ-trans (M.≅ᵗᵐ-sym (stm-subst-comp _ _ _))
              (M.≅ᵗᵐ-trans (stm-subst-cong-tm (subst-var-sound v (σ ⊚πs⟨ Δ ⟩)) _)
                           (weaken-tm-sound (subst-var v (σ ⊚πs⟨ Δ ⟩) refl)))

tm-subst-sound : (t : TmExpr Γ T) (σ : SubstExpr Δ Γ) → (⟦ t ⟧tm [ ⟦ σ ⟧subst ]s) M.≅ᵗᵐ ⟦ t [ σ ]tm ⟧tm
tm-subst-sound t σ with is-special-subst? σ
tm-subst-sound t .(id-subst Γ)          | just (id-subst Γ) = stm-subst-id ⟦ t ⟧tm
tm-subst-sound t .(σ ⊚πs⟨ ◇ ⟩)          | just (σ ⊚πs⟨ ◇ ⟩) = tm-subst-sound t σ
tm-subst-sound t .(σ ⊚πs⟨ Θ ,, _ ∈ T ⟩) | just (σ ⊚πs⟨ Θ ,, _ ∈ T ⟩) =
  M.≅ᵗᵐ-trans (M.≅ᵗᵐ-sym (M.stm-subst-comp _ _ _))
               (M.≅ᵗᵐ-trans (stm-subst-cong-tm (tm-subst-sound t (σ ⊚πs⟨ Θ ⟩)) _)
                            (weaken-tm-sound (t [ σ ⊚πs⟨ Θ ⟩ ]tm)))
tm-subst-sound (var' x {v} {refl}) σ | nothing = subst-var-sound v σ
tm-subst-sound (lam[ x ∈ _ ] t) σ | nothing =
  M.≅ᵗᵐ-trans (sλ-natural {b = ⟦ t ⟧tm} ⟦ σ ⟧subst)
              (sλ-cong (tm-subst-sound t (σ ⊹⟨ x ⟩)))
tm-subst-sound (f ∙ t) σ | nothing = M.≅ᵗᵐ-trans (∙ₛ-natural _) (∙ₛ-cong (tm-subst-sound f σ) (tm-subst-sound t σ))
tm-subst-sound zero σ | nothing = sdiscr-natural _
tm-subst-sound suc σ | nothing = sdiscr-func-natural _
tm-subst-sound (nat-elim a f) σ | nothing = M.≅ᵗᵐ-trans (snat-elim-natural _) (snat-elim-cong (tm-subst-sound a σ) (tm-subst-sound f σ))
tm-subst-sound true σ | nothing = sdiscr-natural _
tm-subst-sound false σ | nothing = sdiscr-natural _
tm-subst-sound (if b t f) σ | nothing = M.≅ᵗᵐ-trans (sif-natural _) (sif-cong (tm-subst-sound b σ) (tm-subst-sound t σ) (tm-subst-sound f σ))
tm-subst-sound (pair t s) σ | nothing = M.≅ᵗᵐ-trans (spair-natural _) (spair-cong (tm-subst-sound t σ) (tm-subst-sound s σ))
tm-subst-sound (fst p) σ | nothing = M.≅ᵗᵐ-trans (sfst-natural _) (sfst-cong (tm-subst-sound p σ))
tm-subst-sound (snd p) σ | nothing = M.≅ᵗᵐ-trans (ssnd-natural _) (ssnd-cong (tm-subst-sound p σ))

multi⊹ : (Θ : CtxExpr) → SubstExpr Γ Δ → SubstExpr (Γ ++ctx Θ) (Δ ++ctx Θ)
multi⊹ ◇            σ = σ
multi⊹ (Θ ,, x ∈ T) σ = (multi⊹ Θ σ) ⊹⟨ x ⟩

cong₃ : {A B C D : Set} (f : A → B → C → D)
        {a a' : A} {b b' : B} {c c' : C} →
        a ≡ a' → b ≡ b' → c ≡ c' →
        f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

var-weaken-subst-trivial-multi : ∀ {x y} (Θ : CtxExpr) (v : Var x (Γ ++ctx Θ)) {s : TmExpr Γ S} (e : lookup-var (mid-weaken-var Θ v) ≡ lookup-var v) →
  (var' x {mid-weaken-var Θ v} {e}) [ multi⊹ Θ (s / y) ]tm ≡ var' x {v} {refl}
var-weaken-subst-trivial-multi ◇ v refl = refl
var-weaken-subst-trivial-multi (Θ ,, x ∈ T) vzero refl = refl
var-weaken-subst-trivial-multi (◇ ,, x ∈ T) (vsuc v) refl = refl
var-weaken-subst-trivial-multi (Θ ,, x ∈ T ,, y ∈ S) (vsuc v) e = cong weaken-tm (var-weaken-subst-trivial-multi (Θ ,, x ∈ T) v e)

tm-weaken-subst-trivial-multi : ∀ {x} (Θ : CtxExpr) (t : TmExpr (Γ ++ctx Θ) T) {s : TmExpr Γ S} → (mid-weaken-tm Θ t) [ multi⊹ Θ (s / x) ]tm ≡ t
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

tm-weaken-subst-trivial : ∀ {x} → (t : TmExpr Γ T) (s : TmExpr Γ S) → (t [ π ]tm) [ s / x ]tm ≡ t
tm-weaken-subst-trivial t s = tm-weaken-subst-trivial-multi ◇ t

-- The next lemma is needed multiple times in the soundness proof.
subst-lemma : (Δ : CtxExpr) {Γ : M.Ctx ★} {T : ClosedTy ★}
              (σ : Γ M.⇒ ⟦ Δ ⟧ctx) (t : SimpleTm ⟦ Δ ⟧ctx T) →
              (⟦ id-subst Δ ⟧subst ,ₛ t) M.⊚ σ M.≅ˢ (σ s⊹) M.⊚ (M.id-subst Γ ,ₛ (t [ σ ]s))
subst-lemma Δ σ t =
  M.≅ˢ-trans (M.,ₛ-⊚ _ _ _)
             (M.≅ˢ-trans (M.,ₛ-cong1 (M.⊚-id-substˡ _) _)
                         (M.≅ˢ-sym (M.≅ˢ-trans (M.,ₛ-⊚ _ _ _)
                                               (M.≅ˢ-trans (M.,ₛ-cong2 _ (M.,ₛ-β2 _ _))
                                                           (M.,ₛ-cong1 (M.≅ˢ-trans M.⊚-assoc (M.≅ˢ-trans (M.⊚-congˡ (M.,ₛ-β1 _ _))
                                                                                                         (M.⊚-id-substʳ _))) _)))))
