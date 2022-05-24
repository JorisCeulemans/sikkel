--------------------------------------------------
-- A Simple Type Theory for which we will provide a logic
--------------------------------------------------

module Experimental.ProgramLogic.AlternativeClosedTypes.STT where

open import Data.Nat

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
  lit : ℕ → TmExpr Γ Nat'
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
⟦ lit n ⟧tm = sdiscr n
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

multi-weaken-var : {Γ : CtxExpr} (Δ : CtxExpr) → Var (Γ ++ctx Δ) T → Var ((Γ ,, S) ++ctx Δ) T
multi-weaken-var ◇        x        = vsuc x
multi-weaken-var (Δ ,, R) vzero    = vzero
multi-weaken-var (Δ ,, R) (vsuc x) = vsuc (multi-weaken-var Δ x)

multi-weaken-tm : (Δ : CtxExpr) → TmExpr (Γ ++ctx Δ) T → TmExpr ((Γ ,, S) ++ctx Δ) T
multi-weaken-tm {Γ} Δ (var x) = var (multi-weaken-var Δ x)
multi-weaken-tm {Γ} Δ (lam t) = lam (multi-weaken-tm {Γ} (Δ ,, _) t)
multi-weaken-tm Δ (f ∙ t) = multi-weaken-tm Δ f ∙ multi-weaken-tm Δ t
multi-weaken-tm Δ (lit n) = lit n
multi-weaken-tm Δ suc = suc
multi-weaken-tm Δ (nat-elim a f) = nat-elim (multi-weaken-tm Δ a) (multi-weaken-tm Δ f)
multi-weaken-tm Δ true = true
multi-weaken-tm Δ false = false
multi-weaken-tm Δ (if b t f) = if (multi-weaken-tm Δ b) (multi-weaken-tm Δ t) (multi-weaken-tm Δ f)
multi-weaken-tm Δ (pair t s) = pair (multi-weaken-tm Δ t) (multi-weaken-tm Δ s)
multi-weaken-tm Δ (fst p) = fst (multi-weaken-tm Δ p)
multi-weaken-tm Δ (snd p) = snd (multi-weaken-tm Δ p)

weaken-tm : TmExpr Γ T → TmExpr (Γ ,, S) T
weaken-tm t = multi-weaken-tm ◇ t

multi-weaken-sem-subst : {Γ : CtxExpr} (S : TyExpr) (Δ : CtxExpr) → ⟦ (Γ ,, S) ++ctx Δ ⟧ctx M.⇒ ⟦ Γ ++ctx Δ ⟧ctx
multi-weaken-sem-subst S ◇ = M.π
multi-weaken-sem-subst S (Δ ,, T) = multi-weaken-sem-subst S Δ s⊹

multi-weaken-var-sound : {Γ : CtxExpr} (Δ : CtxExpr) (x : Var (Γ ++ctx Δ) T) →
                         (⟦ x ⟧var [ multi-weaken-sem-subst S Δ ]s) M.≅ᵗᵐ ⟦ multi-weaken-var Δ x ⟧var
multi-weaken-var-sound ◇        x = M.≅ᵗᵐ-refl
multi-weaken-var-sound (Δ ,, T) vzero    = ,ₛ-β2 _ sξ
multi-weaken-var-sound (Δ ,, T) (vsuc x) =
  M.≅ᵗᵐ-trans (stm-subst-comp ⟦ x ⟧var M.π _)
              (M.≅ᵗᵐ-trans (stm-subst-cong-subst ⟦ x ⟧var (,ₛ-β1 _ sξ))
                           (M.≅ᵗᵐ-trans (M.≅ᵗᵐ-sym (stm-subst-comp ⟦ x ⟧var _ M.π))
                                        (stm-subst-cong-tm (multi-weaken-var-sound Δ x) M.π)))

multi-weaken-tm-sound : {S : TyExpr} (Δ : CtxExpr) (t : TmExpr (Γ ++ctx Δ) T) →
                        (⟦ t ⟧tm [ multi-weaken-sem-subst S Δ ]s) M.≅ᵗᵐ ⟦ multi-weaken-tm {S = S} Δ t ⟧tm
multi-weaken-tm-sound Δ (var x) = multi-weaken-var-sound Δ x
multi-weaken-tm-sound Δ (lam t) = M.≅ᵗᵐ-trans (sλ-natural _) (sλ-cong (multi-weaken-tm-sound (Δ ,, _) t))
multi-weaken-tm-sound Δ (f ∙ t) = M.≅ᵗᵐ-trans (∙ₛ-natural _) (∙ₛ-cong (multi-weaken-tm-sound Δ f) (multi-weaken-tm-sound Δ t))
multi-weaken-tm-sound Δ (lit n) = sdiscr-natural _
multi-weaken-tm-sound Δ suc = sdiscr-func-natural _
multi-weaken-tm-sound Δ (nat-elim a f) = M.≅ᵗᵐ-trans (snat-elim-natural _) (snat-elim-cong (multi-weaken-tm-sound Δ a) (multi-weaken-tm-sound Δ f))
multi-weaken-tm-sound Δ true = sdiscr-natural _
multi-weaken-tm-sound Δ false = sdiscr-natural _
multi-weaken-tm-sound Δ (if b t f) =
  M.≅ᵗᵐ-trans (sif-natural _) (sif-cong (multi-weaken-tm-sound Δ b) (multi-weaken-tm-sound Δ t) (multi-weaken-tm-sound Δ f))
multi-weaken-tm-sound Δ (pair t s) = M.≅ᵗᵐ-trans (spair-natural _) (spair-cong (multi-weaken-tm-sound Δ t) (multi-weaken-tm-sound Δ s))
multi-weaken-tm-sound Δ (fst p) = M.≅ᵗᵐ-trans (sfst-natural _) (sfst-cong (multi-weaken-tm-sound Δ p))
multi-weaken-tm-sound Δ (snd p) = M.≅ᵗᵐ-trans (ssnd-natural _) (ssnd-cong (multi-weaken-tm-sound Δ p))

weaken-tm-sound : {S : TyExpr} (t : TmExpr Γ T) → (⟦ t ⟧tm [ M.π ]s) M.≅ᵗᵐ ⟦ weaken-tm {S = S} t ⟧tm
weaken-tm-sound t = multi-weaken-tm-sound ◇ t


--------------------------------------------------
-- Substitutions are sequences of terms.

data SubstExpr (Δ : CtxExpr) : CtxExpr → Set where
  [] : SubstExpr Δ ◇
  _∷_ : SubstExpr Δ Γ → TmExpr Δ T → SubstExpr Δ (Γ ,, T)

weaken-subst : SubstExpr Δ Γ → SubstExpr (Δ ,, S) Γ
weaken-subst [] = []
weaken-subst (σ ∷ t) = weaken-subst σ ∷ (weaken-tm t)

id-subst : SubstExpr Γ Γ
id-subst {◇} = []
id-subst {Γ ,, T} = weaken-subst (id-subst {Γ}) ∷ var vzero

π : SubstExpr (Γ ,, T) Γ
π = weaken-subst id-subst

_⊹ : SubstExpr Δ Γ → SubstExpr (Δ ,, T) (Γ ,, T)
σ ⊹ = weaken-subst σ ∷ var vzero

subst-var : Var Γ T → SubstExpr Δ Γ → TmExpr Δ T
subst-var vzero    (σ ∷ t) = t
subst-var (vsuc x) (σ ∷ s) = subst-var x σ

_[_]tm : TmExpr Γ T → SubstExpr Δ Γ → TmExpr Δ T
var x [ σ ]tm = subst-var x σ
lam t [ σ ]tm = lam (t [ σ ⊹ ]tm)
(f ∙ t) [ σ ]tm = (f [ σ ]tm) ∙ (t [ σ ]tm)
lit n [ σ ]tm = lit n
suc [ σ ]tm = suc
nat-elim a f [ σ ]tm = nat-elim (a [ σ ]tm) (f [ σ ]tm)
true [ σ ]tm = true
false [ σ ]tm = false
if b t f [ σ ]tm = if (b [ σ ]tm) (t [ σ ]tm) (f [ σ ]tm)
pair t s [ σ ]tm = pair (t [ σ ]tm) (s [ σ ]tm)
fst p [ σ ]tm = fst (p [ σ ]tm)
snd p [ σ ]tm = snd (p [ σ ]tm)

_⊚_ : SubstExpr Γ Θ → SubstExpr Δ Γ → SubstExpr Δ Θ
[]      ⊚ σ = []
(τ ∷ t) ⊚ σ = (τ ⊚ σ) ∷ (t [ σ ]tm)


-- Interpretation of substitutions as presheaf morphisms
⟦_⟧subst : SubstExpr Δ Γ → (⟦ Δ ⟧ctx M.⇒ ⟦ Γ ⟧ctx)
⟦ [] ⟧subst = M.!◇ _
⟦ _∷_ {_} {T} σ t ⟧subst = ⟦ σ ⟧subst ,ₛ ⟦ t ⟧tm

weaken-subst-sound : (σ : SubstExpr Δ Γ) {S : TyExpr} → (⟦ σ ⟧subst M.⊚ M.π) M.≅ˢ ⟦ weaken-subst {S = S} σ ⟧subst
weaken-subst-sound []      = M.◇-terminal _ _ _
weaken-subst-sound (σ ∷ t) = M.≅ˢ-trans (,ₛ-⊚ _ _ _) (M.≅ˢ-trans (,ₛ-cong1 (weaken-subst-sound σ) _) (,ₛ-cong2 _ (weaken-tm-sound t)))

id-subst-sound : M.id-subst ⟦ Γ ⟧ctx M.≅ˢ ⟦ id-subst {Γ = Γ} ⟧subst
id-subst-sound {Γ = ◇}      = M.◇-terminal _ _ _
id-subst-sound {Γ = Γ ,, T} = M.≅ˢ-trans ,ₛ-η-id (,ₛ-cong1 (M.≅ˢ-trans (M.≅ˢ-sym (M.⊚-id-substˡ _))
                                                                       (M.≅ˢ-trans (M.⊚-congʳ (id-subst-sound {Γ = Γ}))
                                                                                   (weaken-subst-sound {Δ = Γ} id-subst))) _)

π-sound : M.π M.≅ˢ ⟦ π {Γ = Γ} {T = T} ⟧subst
π-sound {Γ = Γ} {T = T} =
  M.≅ˢ-trans (M.≅ˢ-sym (M.⊚-id-substˡ _)) (M.≅ˢ-trans (M.⊚-congʳ (id-subst-sound {Γ})) (weaken-subst-sound {Γ} id-subst {S = T}))

⊹-sound : (σ : SubstExpr Δ Γ) {T : TyExpr} → (⟦ σ ⟧subst s⊹) M.≅ˢ ⟦ _⊹ {T = T} σ ⟧subst
⊹-sound σ = ,ₛ-cong1 (weaken-subst-sound σ) sξ

tm-subst-sound : (t : TmExpr Γ T) (σ : SubstExpr Δ Γ) → (⟦ t ⟧tm [ ⟦ σ ⟧subst ]s) M.≅ᵗᵐ ⟦ t [ σ ]tm ⟧tm
tm-subst-sound (var vzero)    (σ ∷ t) = ,ₛ-β2 ⟦ σ ⟧subst ⟦ t ⟧tm
tm-subst-sound (var (vsuc x)) (σ ∷ t) =
  M.≅ᵗᵐ-trans (stm-subst-comp ⟦ x ⟧var M.π (⟦ σ ⟧subst ,ₛ ⟦ t ⟧tm))
              (M.≅ᵗᵐ-trans (stm-subst-cong-subst (⟦ x ⟧var) (,ₛ-β1 ⟦ σ ⟧subst ⟦ t ⟧tm))
                           (tm-subst-sound (var x) σ))
tm-subst-sound (lam t) σ =
  M.≅ᵗᵐ-trans (sλ-natural {b = ⟦ t ⟧tm} ⟦ σ ⟧subst)
              (sλ-cong (M.≅ᵗᵐ-trans (stm-subst-cong-subst ⟦ t ⟧tm (⊹-sound σ))
                                    (tm-subst-sound t (σ ⊹))))
tm-subst-sound (f ∙ t) σ = M.≅ᵗᵐ-trans (∙ₛ-natural _) (∙ₛ-cong (tm-subst-sound f σ) (tm-subst-sound t σ))
tm-subst-sound (lit n) σ = sdiscr-natural _
tm-subst-sound suc σ = sdiscr-func-natural _
tm-subst-sound (nat-elim a f) σ = M.≅ᵗᵐ-trans (snat-elim-natural _) (snat-elim-cong (tm-subst-sound a σ) (tm-subst-sound f σ))
tm-subst-sound true σ = sdiscr-natural _
tm-subst-sound false σ = sdiscr-natural _
tm-subst-sound (if b t f) σ = M.≅ᵗᵐ-trans (sif-natural _) (sif-cong (tm-subst-sound b σ) (tm-subst-sound t σ) (tm-subst-sound f σ))
tm-subst-sound (pair t s) σ = M.≅ᵗᵐ-trans (spair-natural _) (spair-cong (tm-subst-sound t σ) (tm-subst-sound s σ))
tm-subst-sound (fst p) σ = M.≅ᵗᵐ-trans (sfst-natural _) (sfst-cong (tm-subst-sound p σ))
tm-subst-sound (snd p) σ = M.≅ᵗᵐ-trans (ssnd-natural _) (ssnd-cong (tm-subst-sound p σ))
