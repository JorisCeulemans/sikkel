{-# OPTIONS --allow-unsolved-metas #-}

--------------------------------------------------
-- A Simple Type Theory for which we will provide a logic
--------------------------------------------------

module Experimental.ProgramLogic.STT where

open import Data.Nat

open import Model.BaseCategory
open import Model.CwF-Structure as M using (Ctx; Ty; Tm; ClosedTy)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Discrete as M


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
⟦ Γ ,, T ⟧ctx = ⟦ Γ ⟧ctx M.,, ⟦ T ⟧ty

ty-closed : (T : TyExpr) {Δ Γ : Ctx ★} {σ : Δ M.⇒ Γ} → ⟦ T ⟧ty M.[ σ ] M.≅ᵗʸ ⟦ T ⟧ty
ty-closed Nat' = M.Discr-natural ℕ _
ty-closed Bool' = M.Discr-natural _ _
ty-closed (T ⇛ S) = M.≅ᵗʸ-trans (M.⇛-natural _) (M.⇛-cong (ty-closed T) (ty-closed S))
ty-closed (T ⊠ S) = M.≅ᵗʸ-trans (M.⊠-natural _) (M.⊠-cong (ty-closed T) (ty-closed S))

⟦_⟧var : Var Γ T → Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty
⟦ vzero {_} {T} ⟧var = M.ι⁻¹[ ty-closed T ] M.ξ
⟦ vsuc {_} {T} x ⟧var = M.ι⁻¹[ ty-closed T ] (⟦ x ⟧var M.[ M.π ]')

⟦_⟧tm : TmExpr Γ T → Tm ⟦ Γ ⟧ctx ⟦ T ⟧ty
⟦ var x ⟧tm = ⟦ x ⟧var
⟦ lam {_} {S} t ⟧tm = M.lam _ (M.ι[ ty-closed S ] ⟦ t ⟧tm)
⟦ f ∙ t ⟧tm = M.app ⟦ f ⟧tm ⟦ t ⟧tm
⟦ lit n ⟧tm = M.discr n
⟦ suc ⟧tm = M.suc'
⟦ nat-elim a f ⟧tm = M.nat-elim _ ⟦ a ⟧tm ⟦ f ⟧tm
⟦ true ⟧tm = M.true'
⟦ false ⟧tm = M.false'
⟦ if b t f ⟧tm = M.if' ⟦ b ⟧tm then' ⟦ t ⟧tm else' ⟦ f ⟧tm
⟦ pair t s ⟧tm = M.prim-pair ⟦ t ⟧tm ⟦ s ⟧tm
⟦ fst p ⟧tm = M.prim-fst ⟦ p ⟧tm
⟦ snd p ⟧tm = M.prim-snd ⟦ p ⟧tm


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

multi-weaken-tm : TmExpr (Γ ++ctx Δ) T → TmExpr ((Γ ,, S) ++ctx Δ) T
multi-weaken-tm {Γ} {Δ} (var x) = var (multi-weaken-var Δ x)
multi-weaken-tm {Γ} {Δ} (lam t) = lam (multi-weaken-tm {Γ} {Δ ,, _} t)
multi-weaken-tm (f ∙ t) = multi-weaken-tm f ∙ multi-weaken-tm t
multi-weaken-tm (lit n) = lit n
multi-weaken-tm suc = suc
multi-weaken-tm (nat-elim a f) = nat-elim (multi-weaken-tm a) (multi-weaken-tm f)
multi-weaken-tm true = true
multi-weaken-tm false = true
multi-weaken-tm (if b t f) = if (multi-weaken-tm b) (multi-weaken-tm t) (multi-weaken-tm f)
multi-weaken-tm (pair t s) = pair (multi-weaken-tm t) (multi-weaken-tm s)
multi-weaken-tm (fst p) = fst (multi-weaken-tm p)
multi-weaken-tm (snd p) = snd (multi-weaken-tm p)

weaken-tm : TmExpr Γ T → TmExpr (Γ ,, S) T
weaken-tm t = multi-weaken-tm {Δ = ◇} t


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
⟦ _∷_ {_} {T} σ t ⟧subst = M.to-ext-subst _ ⟦ σ ⟧subst (M.ι[ ty-closed T ] ⟦ t ⟧tm)

tm-subst-sound : (t : TmExpr Γ T) (σ : SubstExpr Δ Γ) → (M.ι[ ty-closed T ] ⟦ t [ σ ]tm ⟧tm) M.≅ᵗᵐ ⟦ t ⟧tm M.[ ⟦ σ ⟧subst ]'
tm-subst-sound {T = T} (var vzero)    (σ ∷ t) = record { eq = {!!} }
  -- M.≅ᵗᵐ-sym (M.≅ᵗᵐ-trans (M.≅ᵗᵐ-sym (M.ι-subst-commute ⟦ σ ∷ t ⟧subst (M.≅ᵗʸ-sym (ty-closed T)) M.ξ)) (M.≅ᵗᵐ-trans (M.ι-cong α (M.ctx-ext-subst-β₂ _ _)) {!!}))
  -- where
  --   α = M.ty-subst-cong-ty
  --      (M.to-ext-subst ⟦ T ⟧ty ⟦ σ ⟧subst (M.ι[ ty-closed T ] ⟦ t ⟧tm))
  --      (M.≅ᵗʸ-sym (ty-closed T))
tm-subst-sound (var (vsuc x)) (σ ∷ t) = record { eq = {!!} }
tm-subst-sound (lam t) σ = record { eq = λ _ → M.to-pshfun-eq {!!} }
tm-subst-sound (f ∙ t) σ = {!!}
tm-subst-sound (lit n) σ = M.≅ᵗᵐ-sym (M.discr-natural n ⟦ σ ⟧subst)
tm-subst-sound suc σ = {!!}
tm-subst-sound (nat-elim a f) σ = {!!}
tm-subst-sound true σ = M.≅ᵗᵐ-sym (M.discr-natural _ _)
tm-subst-sound false σ = M.≅ᵗᵐ-sym (M.discr-natural _ _)
tm-subst-sound (if b t f) σ = {!!}
tm-subst-sound (pair t s) σ = {!!}
tm-subst-sound (fst {T = T} {S = S} p) σ = {!!} -- M.≅ᵗᵐ-trans (M.prim-fst-ι (ty-closed T) (ty-closed S) ⟦ p [ σ ]tm ⟧tm) {!tm-subst-sound p σ!}
tm-subst-sound (snd p) σ = {!!}
