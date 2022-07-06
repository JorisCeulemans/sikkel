--------------------------------------------------
-- A Simple Type Theory for which we will provide a logic
--------------------------------------------------

module Experimental.LogicalFramework.STT where

open import Data.Maybe
open import Data.Nat
open import Relation.Binary.PropositionalEquality

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


infixl 4 _,,_
data CtxExpr : Set where
  ◇ : CtxExpr
  _,,_ : (Γ : CtxExpr) (T : TyExpr) → CtxExpr

private variable
  Γ Δ Θ : CtxExpr


-- Variables are represented as de Bruijn indices.
data Var : CtxExpr → TyExpr → Set where
  vzero : Var (Γ ,, T) T
  vsuc : Var Γ T → Var (Γ ,, S) T

infixl 50 _∙_
data TmExpr (Γ : CtxExpr) : TyExpr → Set where
  var : Var Γ T → TmExpr Γ T
  lam : TmExpr (Γ ,, T) S → TmExpr Γ (T ⇛ S)
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
-- Interpretation of types, contexts and terms in the presheaf
--   model over the trivial base category

⟦_⟧ty : TyExpr → ClosedTy ★
⟦ Nat' ⟧ty = M.Nat'
⟦ Bool' ⟧ty = M.Bool'
⟦ T ⇛ S ⟧ty = ⟦ T ⟧ty M.⇛ ⟦ S ⟧ty
⟦ T ⊠ S ⟧ty = ⟦ T ⟧ty M.⊠ ⟦ S ⟧ty

⟦_⟧ctx : CtxExpr → Ctx ★
⟦ ◇ ⟧ctx = M.◇
⟦ Γ ,, T ⟧ctx = ⟦ Γ ⟧ctx ,,ₛ ⟦ T ⟧ty

⟦_⟧var : Var Γ T → SimpleTm ⟦ Γ ⟧ctx ⟦ T ⟧ty
⟦ vzero ⟧var = sξ
⟦ vsuc x ⟧var = ⟦ x ⟧var [ M.π ]s

⟦_⟧tm : TmExpr Γ T → SimpleTm ⟦ Γ ⟧ctx ⟦ T ⟧ty
⟦ var x ⟧tm = ⟦ x ⟧var
⟦ lam t ⟧tm = sλ[ _ ] ⟦ t ⟧tm
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
Γ ++ctx (Δ ,, T) = (Γ ++ctx Δ) ,, T

mid-weaken-var : {Γ : CtxExpr} (Δ : CtxExpr) → Var (Γ ++ctx Δ) T → Var ((Γ ,, S) ++ctx Δ) T
mid-weaken-var ◇        x        = vsuc x
mid-weaken-var (Δ ,, R) vzero    = vzero
mid-weaken-var (Δ ,, R) (vsuc x) = vsuc (mid-weaken-var Δ x)

mid-weaken-tm : (Δ : CtxExpr) → TmExpr (Γ ++ctx Δ) T → TmExpr ((Γ ,, S) ++ctx Δ) T
mid-weaken-tm {Γ} Δ (var x) = var (mid-weaken-var Δ x)
mid-weaken-tm {Γ} Δ (lam t) = lam (mid-weaken-tm {Γ} (Δ ,, _) t)
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

weaken-tm : TmExpr Γ T → TmExpr (Γ ,, S) T
weaken-tm t = mid-weaken-tm ◇ t

multi-weaken-tm : (Δ : CtxExpr) → TmExpr Γ T → TmExpr (Γ ++ctx Δ) T
multi-weaken-tm ◇        t = t
multi-weaken-tm (Δ ,, T) t = weaken-tm (multi-weaken-tm Δ t)

mid-weaken-sem-subst : {Γ : CtxExpr} (S : TyExpr) (Δ : CtxExpr) → ⟦ (Γ ,, S) ++ctx Δ ⟧ctx M.⇒ ⟦ Γ ++ctx Δ ⟧ctx
mid-weaken-sem-subst S ◇ = M.π
mid-weaken-sem-subst S (Δ ,, T) = mid-weaken-sem-subst S Δ s⊹

mid-weaken-var-sound : {Γ : CtxExpr} (Δ : CtxExpr) (x : Var (Γ ++ctx Δ) T) →
                       (⟦ x ⟧var [ mid-weaken-sem-subst S Δ ]s) M.≅ᵗᵐ ⟦ mid-weaken-var Δ x ⟧var
mid-weaken-var-sound ◇        x = M.≅ᵗᵐ-refl
mid-weaken-var-sound (Δ ,, T) vzero    = ,ₛ-β2 _ sξ
mid-weaken-var-sound (Δ ,, T) (vsuc x) =
  M.≅ᵗᵐ-trans (stm-subst-comp ⟦ x ⟧var M.π _)
              (M.≅ᵗᵐ-trans (stm-subst-cong-subst ⟦ x ⟧var (,ₛ-β1 _ sξ))
                           (M.≅ᵗᵐ-trans (M.≅ᵗᵐ-sym (stm-subst-comp ⟦ x ⟧var _ M.π))
                                        (stm-subst-cong-tm (mid-weaken-var-sound Δ x) M.π)))

mid-weaken-tm-sound : {S : TyExpr} (Δ : CtxExpr) (t : TmExpr (Γ ++ctx Δ) T) →
                      (⟦ t ⟧tm [ mid-weaken-sem-subst S Δ ]s) M.≅ᵗᵐ ⟦ mid-weaken-tm {S = S} Δ t ⟧tm
mid-weaken-tm-sound Δ (var x) = mid-weaken-var-sound Δ x
mid-weaken-tm-sound Δ (lam t) = M.≅ᵗᵐ-trans (sλ-natural _) (sλ-cong (mid-weaken-tm-sound (Δ ,, _) t))
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

weaken-tm-sound : {S : TyExpr} (t : TmExpr Γ T) → (⟦ t ⟧tm [ M.π ]s) M.≅ᵗᵐ ⟦ weaken-tm {S = S} t ⟧tm
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
  _∷_ : SubstExpr Δ Γ → TmExpr Δ T → SubstExpr Δ (Γ ,, T)
  id-subst : (Γ : CtxExpr) → SubstExpr Γ Γ
  _⊚πs⟨_⟩ : SubstExpr Δ Γ → (Θ : CtxExpr) → SubstExpr (Δ ++ctx Θ) Γ

{-
weaken-subst : SubstExpr Δ Γ → SubstExpr (Δ ,, S) Γ
weaken-subst [] = []
weaken-subst (σ ∷ t) = weaken-subst σ ∷ (weaken-tm t)
weaken-subst (πs Δ) = πs (Δ ,, _)

id-subst : (Γ : CtxExpr) → SubstExpr Γ Γ
id-subst Γ = πs ◇
-}

π : SubstExpr (Γ ,, T) Γ
π = id-subst _ ⊚πs⟨ _ ⟩

_⊚π : SubstExpr Δ Γ → SubstExpr (Δ ,, T) Γ
σ ⊚π = σ ⊚πs⟨ _ ⟩

_⊹ : SubstExpr Δ Γ → SubstExpr (Δ ,, T) (Γ ,, T)
σ ⊹ = (σ ⊚π) ∷ var vzero

_/var0 : TmExpr Γ T → SubstExpr Γ (Γ ,, T)
t /var0 = id-subst _ ∷ t


-- We will use the following view pattern in the implementation of
-- substitution for terms, in order to treat some substitutions
-- specially.
data SpecialSubstExpr : SubstExpr Γ Δ → Set where
  id-subst : (Γ : CtxExpr) → SpecialSubstExpr (id-subst Γ)
  _⊚πs⟨_⟩ : (σ : SubstExpr Γ Δ) → (Θ : CtxExpr) → SpecialSubstExpr (σ ⊚πs⟨ Θ ⟩)

is-special-subst? : (σ : SubstExpr Γ Δ) → Maybe (SpecialSubstExpr σ)
is-special-subst? []           = nothing
is-special-subst? (σ ∷ t)      = nothing
is-special-subst? (id-subst Γ) = just (id-subst Γ)
is-special-subst? (σ ⊚πs⟨ Θ ⟩) = just (σ ⊚πs⟨ Θ ⟩)

subst-var : Var Γ T → SubstExpr Δ Γ → TmExpr Δ T
subst-var x        (id-subst Γ) = var x
subst-var x        (σ ⊚πs⟨ ◇ ⟩) = subst-var x σ
subst-var x        (σ ⊚πs⟨ Δ ,, T ⟩) = weaken-tm (subst-var x (σ ⊚πs⟨ Δ ⟩))
subst-var vzero    (σ ∷ t) = t
subst-var (vsuc x) (σ ∷ s) = subst-var x σ

_[_]tm : TmExpr Γ T → SubstExpr Δ Γ → TmExpr Δ T
t [ σ ]tm with is-special-subst? σ
(t [ .(id-subst Γ) ]tm) | just (id-subst Γ) = t
(t [ .(σ ⊚πs⟨ Θ ⟩) ]tm) | just (σ ⊚πs⟨ Θ ⟩) = multi-weaken-tm Θ (t [ σ ]tm)
var x [ σ ]tm           | nothing = subst-var x σ
lam t [ σ ]tm           | nothing = lam (t [ σ ⊹ ]tm)
(f ∙ t) [ σ ]tm         | nothing = (f [ σ ]tm) ∙ (t [ σ ]tm)
zero [ σ ]tm            | nothing = zero
suc [ σ ]tm             | nothing = suc
nat-elim a f [ σ ]tm    | nothing = nat-elim (a [ σ ]tm) (f [ σ ]tm)
true [ σ ]tm            | nothing = true
false [ σ ]tm           | nothing = false
if b t f [ σ ]tm        | nothing = if (b [ σ ]tm) (t [ σ ]tm) (f [ σ ]tm)
pair t s [ σ ]tm        | nothing = pair (t [ σ ]tm) (s [ σ ]tm)
fst p [ σ ]tm           | nothing = fst (p [ σ ]tm)
snd p [ σ ]tm           | nothing = snd (p [ σ ]tm)

{-
_⊚_ : SubstExpr Γ Θ → SubstExpr Δ Γ → SubstExpr Δ Θ
[]      ⊚ σ = []
(τ ∷ t) ⊚ σ = (τ ⊚ σ) ∷ (t [ σ ]tm)
-}


-- Interpretation of substitutions as presheaf morphisms
⟦_⟧subst : SubstExpr Δ Γ → (⟦ Δ ⟧ctx M.⇒ ⟦ Γ ⟧ctx)
⟦ [] ⟧subst = M.!◇ _
⟦ _∷_ {_} {T} σ t ⟧subst = ⟦ σ ⟧subst ,ₛ ⟦ t ⟧tm
⟦ id-subst Γ ⟧subst = M.id-subst _
⟦ σ ⊚πs⟨ ◇ ⟩      ⟧subst = ⟦ σ ⟧subst
⟦ σ ⊚πs⟨ Δ ,, T ⟩ ⟧subst = ⟦ σ ⊚πs⟨ Δ ⟩ ⟧subst M.⊚ M.π
{-
weaken-subst-sound : (σ : SubstExpr Δ Γ) {S : TyExpr} → (⟦ σ ⟧subst M.⊚ M.π) M.≅ˢ ⟦ weaken-subst {S = S} σ ⟧subst
weaken-subst-sound []      = M.◇-terminal _ _ _
weaken-subst-sound (σ ∷ t) = M.≅ˢ-trans (,ₛ-⊚ _ _ _) (M.≅ˢ-trans (,ₛ-cong1 (weaken-subst-sound σ) _) (,ₛ-cong2 _ (weaken-tm-sound t)))
weaken-subst-sound (πs ◇) = M.≅ˢ-refl
weaken-subst-sound (πs (Δ ,, T)) = M.≅ˢ-refl
-}
{-
id-subst-sound : (Γ : CtxExpr) → M.id-subst ⟦ Γ ⟧ctx M.≅ˢ ⟦ id-subst ⟧subst
id-subst-sound ◇        = M.◇-terminal _ _ _
id-subst-sound (Γ ,, T) = M.≅ˢ-trans ,ₛ-η-id (,ₛ-cong1 (M.≅ˢ-trans (M.≅ˢ-sym (M.⊚-id-substˡ _))
                                                                   (M.≅ˢ-trans (M.⊚-congʳ (id-subst-sound Γ))
                                                                               (weaken-subst-sound id-subst))) _)

π-sound : (Γ : CtxExpr) (T : TyExpr) → M.π M.≅ˢ ⟦ π {Γ = Γ} {T = T} ⟧subst
π-sound Γ T =
  M.≅ˢ-trans (M.≅ˢ-sym (M.⊚-id-substˡ _)) (M.≅ˢ-trans (M.⊚-congʳ (id-subst-sound Γ)) (weaken-subst-sound (id-subst Γ) {S = T}))
-}

⊹-sound : (σ : SubstExpr Δ Γ) {T : TyExpr} → (⟦ σ ⟧subst s⊹) M.≅ˢ ⟦ _⊹ {T = T} σ ⟧subst
⊹-sound σ = M.≅ˢ-refl

subst-var-sound : (x : Var Γ T) (σ : SubstExpr Δ Γ) → (⟦ x ⟧var [ ⟦ σ ⟧subst ]s) M.≅ᵗᵐ ⟦ subst-var x σ ⟧tm
subst-var-sound vzero    (σ ∷ t) = ,ₛ-β2 ⟦ σ ⟧subst ⟦ t ⟧tm
subst-var-sound (vsuc x) (σ ∷ t) =
  M.≅ᵗᵐ-trans (stm-subst-comp ⟦ x ⟧var M.π (⟦ σ ⟧subst ,ₛ ⟦ t ⟧tm))
              (M.≅ᵗᵐ-trans (stm-subst-cong-subst (⟦ x ⟧var) (,ₛ-β1 ⟦ σ ⟧subst ⟦ t ⟧tm))
                           (subst-var-sound x σ))
subst-var-sound x (id-subst Γ) = stm-subst-id _
subst-var-sound x (σ ⊚πs⟨ ◇ ⟩)      = subst-var-sound x σ
subst-var-sound x (σ ⊚πs⟨ Δ ,, T ⟩) =
  M.≅ᵗᵐ-trans (M.≅ᵗᵐ-sym (stm-subst-comp _ _ _))
              (M.≅ᵗᵐ-trans (stm-subst-cong-tm (subst-var-sound x (σ ⊚πs⟨ Δ ⟩)) _)
                           (weaken-tm-sound (subst-var x (σ ⊚πs⟨ Δ ⟩))))

tm-subst-sound : (t : TmExpr Γ T) (σ : SubstExpr Δ Γ) → (⟦ t ⟧tm [ ⟦ σ ⟧subst ]s) M.≅ᵗᵐ ⟦ t [ σ ]tm ⟧tm
tm-subst-sound t σ with is-special-subst? σ
tm-subst-sound t .(id-subst Γ)      | just (id-subst Γ) = stm-subst-id ⟦ t ⟧tm
tm-subst-sound t .(σ ⊚πs⟨ ◇ ⟩)      | just (σ ⊚πs⟨ ◇ ⟩) = tm-subst-sound t σ
tm-subst-sound t .(σ ⊚πs⟨ Θ ,, T ⟩) | just (σ ⊚πs⟨ Θ ,, T ⟩) =
  M.≅ᵗᵐ-trans (M.≅ᵗᵐ-sym (M.stm-subst-comp _ _ _))
               (M.≅ᵗᵐ-trans (stm-subst-cong-tm (tm-subst-sound t (σ ⊚πs⟨ Θ ⟩)) _)
                            (weaken-tm-sound (t [ σ ⊚πs⟨ Θ ⟩ ]tm)))
tm-subst-sound (var x) σ | nothing = subst-var-sound x σ
tm-subst-sound (lam t) σ | nothing =
  M.≅ᵗᵐ-trans (sλ-natural {b = ⟦ t ⟧tm} ⟦ σ ⟧subst)
              (sλ-cong (tm-subst-sound t (σ ⊹)))
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
multi⊹ ◇        σ = σ
multi⊹ (Θ ,, T) σ = (multi⊹ Θ σ) ⊹

cong₃ : {A B C D : Set} (f : A → B → C → D)
        {a a' : A} {b b' : B} {c c' : C} →
        a ≡ a' → b ≡ b' → c ≡ c' →
        f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

tm-weaken-subst-trivial-lemma : (Θ : CtxExpr) (t : TmExpr (Γ ++ctx Θ) T) {s : TmExpr Γ S} → (mid-weaken-tm Θ t) [ multi⊹ Θ (s /var0) ]tm ≡ t
tm-weaken-subst-trivial-lemma ◇ (var x) = refl
tm-weaken-subst-trivial-lemma ◇ (lam t) = cong lam (tm-weaken-subst-trivial-lemma (◇ ,, _) t)
tm-weaken-subst-trivial-lemma ◇ (f ∙ t) = cong₂ _∙_ (tm-weaken-subst-trivial-lemma ◇ f) (tm-weaken-subst-trivial-lemma ◇ t)
tm-weaken-subst-trivial-lemma ◇ zero = refl
tm-weaken-subst-trivial-lemma ◇ suc = refl
tm-weaken-subst-trivial-lemma ◇ (nat-elim a f) = cong₂ nat-elim (tm-weaken-subst-trivial-lemma ◇ a) (tm-weaken-subst-trivial-lemma ◇ f)
tm-weaken-subst-trivial-lemma ◇ true = refl
tm-weaken-subst-trivial-lemma ◇ false = refl
tm-weaken-subst-trivial-lemma ◇ (if b t f) =
  cong₃ if (tm-weaken-subst-trivial-lemma ◇ b) (tm-weaken-subst-trivial-lemma ◇ t) (tm-weaken-subst-trivial-lemma ◇ f)
tm-weaken-subst-trivial-lemma ◇ (pair t s) = cong₂ pair (tm-weaken-subst-trivial-lemma ◇ t) (tm-weaken-subst-trivial-lemma ◇ s)
tm-weaken-subst-trivial-lemma ◇ (fst p) = cong fst (tm-weaken-subst-trivial-lemma ◇ p)
tm-weaken-subst-trivial-lemma ◇ (snd p) = cong snd (tm-weaken-subst-trivial-lemma ◇ p)
tm-weaken-subst-trivial-lemma (Θ ,, T) (var vzero) = refl
tm-weaken-subst-trivial-lemma (◇ ,, T) (var (vsuc x)) = refl
tm-weaken-subst-trivial-lemma (Θ ,, S ,, T) (var (vsuc x)) = cong (mid-weaken-tm ◇) (tm-weaken-subst-trivial-lemma (Θ ,, S) (var x))
tm-weaken-subst-trivial-lemma (Θ ,, T) (lam t) = cong lam (tm-weaken-subst-trivial-lemma (Θ ,, T ,, _) t)
tm-weaken-subst-trivial-lemma (Θ ,, T) (f ∙ t) = cong₂ _∙_ (tm-weaken-subst-trivial-lemma (Θ ,, T) f) (tm-weaken-subst-trivial-lemma (Θ ,, T) t)
tm-weaken-subst-trivial-lemma (Θ ,, T) zero = refl
tm-weaken-subst-trivial-lemma (Θ ,, T) suc = refl
tm-weaken-subst-trivial-lemma (Θ ,, T) (nat-elim a f) = cong₂ nat-elim (tm-weaken-subst-trivial-lemma (Θ ,, T) a) (tm-weaken-subst-trivial-lemma (Θ ,, T) f)
tm-weaken-subst-trivial-lemma (Θ ,, T) true = refl
tm-weaken-subst-trivial-lemma (Θ ,, T) false = refl
tm-weaken-subst-trivial-lemma (Θ ,, T) (if b t f) =
  cong₃ if (tm-weaken-subst-trivial-lemma (Θ ,, T) b) (tm-weaken-subst-trivial-lemma (Θ ,, T) t) (tm-weaken-subst-trivial-lemma (Θ ,, T) f)
tm-weaken-subst-trivial-lemma (Θ ,, T) (pair t s) = cong₂ pair (tm-weaken-subst-trivial-lemma (Θ ,, T) t) (tm-weaken-subst-trivial-lemma (Θ ,, T) s)
tm-weaken-subst-trivial-lemma (Θ ,, T) (fst p) = cong fst (tm-weaken-subst-trivial-lemma (Θ ,, T) p)
tm-weaken-subst-trivial-lemma (Θ ,, T) (snd p) = cong snd (tm-weaken-subst-trivial-lemma (Θ ,, T) p)

tm-weaken-subst-trivial : (t : TmExpr Γ T) {s : TmExpr Γ S} → (t [ π ]tm) [ s /var0 ]tm ≡ t
tm-weaken-subst-trivial t = tm-weaken-subst-trivial-lemma ◇ t

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
