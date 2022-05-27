module Experimental.ProgramLogic.AlternativeClosedTypes.Derivation where

open import Data.Nat
import Relation.Binary.PropositionalEquality as A≡

open import Model.BaseCategory
open import Model.CwF-Structure as M using (Ctx; Ty; Tm)
open import Model.CwF-Structure.Reflection.SubstitutionSequence renaming (_∷_ to _∷ˢ_)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Discrete as M
import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M
import Experimental.DependentTypes.Model.Function as MDF

import Experimental.ClosedTypes as M
import Experimental.ClosedTypes.Pi as M

open import Experimental.ProgramLogic.AlternativeClosedTypes.STT
open import Experimental.ProgramLogic.AlternativeClosedTypes.Formula

private variable
  Γ Δ : CtxExpr
  T S : TyExpr
  φ ψ : Formula Γ


-- Environment consisiting of (STT) variables and formulas.
data Env : Set
to-ctx : Env → CtxExpr

infixl 2 _∷ᵛ_ _∷ᶠ_
data Env where
  [] : Env
  _∷ᵛ_ : (Ξ : Env) (T : TyExpr) → Env
  _∷ᶠ_ : (Ξ : Env) (φ : Formula (to-ctx Ξ)) → Env

to-ctx []       = ◇
to-ctx (Ξ ∷ᵛ T) = to-ctx Ξ ,, T
to-ctx (Ξ ∷ᶠ φ) = to-ctx Ξ

private variable
  Ξ : Env


data Assumption : (Ξ : Env) → Formula (to-ctx Ξ) → Set where
  azero : Assumption (Ξ ∷ᶠ φ) φ
  asuc  : Assumption Ξ φ → Assumption (Ξ ∷ᶠ ψ) φ
  skip-var : Assumption Ξ φ → Assumption (Ξ ∷ᵛ T) (φ [ π ]frm)


infix 1 _⊢_
data _⊢_ : (Ξ : Env) → Formula (to-ctx Ξ) → Set where
  -- Structural rules for ≡ᶠ
  refl : {t : TmExpr (to-ctx Ξ) T} → Ξ ⊢ t ≡ᶠ t
  sym : {t1 t2 : TmExpr (to-ctx Ξ) T} → (Ξ ⊢ t1 ≡ᶠ t2) → (Ξ ⊢ t2 ≡ᶠ t1)
  trans : {t1 t2 t3 : TmExpr (to-ctx Ξ) T} →
          (Ξ ⊢ t1 ≡ᶠ t2) → (Ξ ⊢ t2 ≡ᶠ t3) →
          (Ξ ⊢ t1 ≡ᶠ t3)
  cong : (f : TmExpr (to-ctx Ξ) (T ⇛ S)) {t1 t2 : TmExpr (to-ctx Ξ) T} →
         (Ξ ⊢ t1 ≡ᶠ t2) →
         (Ξ ⊢ f ∙ t1 ≡ᶠ f ∙ t2)
  fun-cong : {f g : TmExpr (to-ctx Ξ) (T ⇛ S)} →
             (Ξ ⊢ f ≡ᶠ g) →
             (t : TmExpr (to-ctx Ξ) T) →
             (Ξ ⊢ f ∙ t ≡ᶠ g ∙ t)

  -- Introduction and elimination for logical combinators ⊃, ∧ and ∀.
  assume : (Ξ ∷ᶠ φ ⊢ ψ) → (Ξ ⊢ φ ⊃ ψ)
  assumption : Assumption Ξ φ → Ξ ⊢ φ
  ∧-intro : (Ξ ⊢ φ) → (Ξ ⊢ ψ) → (Ξ ⊢ φ ∧ ψ)
  ∧-elimˡ : (Ξ ⊢ φ ∧ ψ) → (Ξ ⊢ φ)
  ∧-elimʳ : (Ξ ⊢ φ ∧ ψ) → (Ξ ⊢ ψ)
  ∀-intro : (Ξ ∷ᵛ T ⊢ φ) → (Ξ ⊢ ∀[ T ] φ)
  ∀-elim : (Ξ ⊢ ∀[ T ] φ) → (t : TmExpr (to-ctx Ξ) T) → (Ξ ⊢ φ [ t /var0 ]frm)

  -- Specific computation rules for term formers (currently no eta rules).
  fun-β : {b : TmExpr (to-ctx Ξ ,, T) S} {t : TmExpr (to-ctx Ξ) T} →
          (Ξ ⊢ lam b ∙ t ≡ᶠ (b [ t /var0 ]tm))
  suc-lit : {n : ℕ} → (Ξ ⊢ (suc ∙ lit n) ≡ᶠ lit (suc n))
  nat-elim-β-zero : {A : TyExpr} {a : TmExpr (to-ctx Ξ) A} {f : TmExpr (to-ctx Ξ) (A ⇛ A)} →
                    (Ξ ⊢ nat-elim a f ∙ lit 0 ≡ᶠ a)
  nat-elim-β-suc : {A : TyExpr} {a : TmExpr (to-ctx Ξ) A} {f : TmExpr (to-ctx Ξ) (A ⇛ A)} {n : TmExpr (to-ctx Ξ) Nat'} →
                   (Ξ ⊢ nat-elim a f ∙ (suc ∙ n) ≡ᶠ f ∙ (nat-elim a f ∙ n))
  if-β-true : {t f : TmExpr (to-ctx Ξ) T} → (Ξ ⊢ if true t f ≡ᶠ t)
  if-β-false : {t f : TmExpr (to-ctx Ξ) T} → (Ξ ⊢ if false t f ≡ᶠ f)
  pair-β-fst : {t : TmExpr (to-ctx Ξ) T} {s : TmExpr (to-ctx Ξ) S} →
               (Ξ ⊢ fst (pair t s) ≡ᶠ t)
  pair-β-snd : {t : TmExpr (to-ctx Ξ) T} {s : TmExpr (to-ctx Ξ) S} →
               (Ξ ⊢ snd (pair t s) ≡ᶠ s)

  -- Induction schemata for Bool' and Nat'.
  bool-induction : (Ξ ⊢ φ [ true /var0 ]frm) →
                   (Ξ ⊢ φ [ false /var0 ]frm) →
                   (Ξ ∷ᵛ Bool' ⊢ φ)
  nat-induction : (Ξ ⊢ φ [ lit 0 /var0 ]frm) →
                  (Ξ ∷ᵛ Nat' ∷ᶠ φ ⊢ φ [ π ∷ (suc ∙ var vzero) ]frm) →
                  (Ξ ∷ᵛ Nat' ⊢ φ)


⟦_⟧env : Env → Ctx ★
to-ctx-subst : (Ξ : Env) → ⟦ Ξ ⟧env M.⇒ ⟦ to-ctx Ξ ⟧ctx

⟦ [] ⟧env = M.◇
⟦ Ξ ∷ᵛ T ⟧env = ⟦ Ξ ⟧env M.,,ₛ ⟦ T ⟧ty
⟦ Ξ ∷ᶠ φ ⟧env = ⟦ Ξ ⟧env M.,, (⟦ φ ⟧frm M.[ to-ctx-subst Ξ ])

to-ctx-subst [] = M.id-subst M.◇
to-ctx-subst (Ξ ∷ᵛ T) = to-ctx-subst Ξ M.s⊹
to-ctx-subst (Ξ ∷ᶠ φ) = to-ctx-subst Ξ M.⊚ M.π

interpret-assumption : Assumption Ξ φ → Tm ⟦ Ξ ⟧env (⟦ φ ⟧frm M.[ to-ctx-subst Ξ ])
interpret-assumption azero = M.ι⁻¹[ M.ty-subst-comp _ _ _ ] M.ξ
interpret-assumption (asuc x) = M.ι⁻¹[ M.ty-subst-comp _ _ _ ] (interpret-assumption x M.[ M.π ]')
interpret-assumption (skip-var {Ξ = Ξ} {φ = φ} {T = T} x) =
  M.ι⁻¹[ M.≅ᵗʸ-trans (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm subst-eq-proof)
                     (M.ty-subst-cong-ty _ (frm-subst-sound φ π))
       ]
  (interpret-assumption x M.[ M.π ]')
  where
    subst-eq-proof : _ M.≅ˢ _
    subst-eq-proof = M.≅ˢ-trans (M.≅ˢ-sym (M.,ₛ-β1 _ M.sξ)) (M.⊚-congʳ (π-sound (to-ctx Ξ) T))

⟦_⟧der : (Ξ ⊢ φ) → Tm ⟦ Ξ ⟧env (⟦ φ ⟧frm M.[ to-ctx-subst Ξ ])
⟦ refl ⟧der = M.refl' _ M.[ _ ]'
⟦ sym d ⟧der = M.ι[ M.Id-natural _ ] M.sym' (M.ι⁻¹[ M.Id-natural _ ] ⟦ d ⟧der)
⟦ trans d1 d2 ⟧der = M.ι[ M.Id-natural _ ] M.trans' (M.ι⁻¹[ M.Id-natural _ ] ⟦ d1 ⟧der) (M.ι⁻¹[ M.Id-natural _ ] ⟦ d2 ⟧der)
⟦ cong f {t1} {t2} d ⟧der =
  M.ι[ M.≅ᵗʸ-trans (M.Id-natural _ {⟦ f ⟧tm M.∙ₛ ⟦ t1 ⟧tm} {⟦ f ⟧tm M.∙ₛ ⟦ t2 ⟧tm}) (M.Id-cong' (M.app-natural _ _ _) (M.app-natural _ _ _)) ]
    M.cong' (M.ι⁻¹[ M.⇛-natural _ ] ((M.ι⁻¹[ M.⇛-natural _ ] ⟦ f ⟧tm ) M.[ _ ]')) (M.ι⁻¹[ M.Id-natural _ {⟦ t1 ⟧tm} {⟦ t2 ⟧tm} ] ⟦ d ⟧der)
⟦ fun-cong {Ξ = Ξ} d t ⟧der =
  M.ι[ M.≅ᵗʸ-trans (M.Id-natural _) (M.Id-cong' (M.app-natural _ _ ⟦ t ⟧tm) (M.app-natural _ _ ⟦ t ⟧tm)) ]
    M.fun-cong' (M.≅ᵗᵐ-to-Id f=g) (⟦ t ⟧tm M.[ _ ]')
  where
    f=g : _ M.≅ᵗᵐ _
    M._≅ᵗᵐ_.eq f=g γ = A≡.cong (λ x → M.pshfun-subst-from _ _ _ (M.pshfun-subst-from _ _ _ x)) (M.eq (M.eq-reflect (M.ι⁻¹[ M.Id-natural _ ] ⟦ d ⟧der)) γ)
⟦ assume d ⟧der = M.ι[ M.⇛-natural _ ] M.lam _ (M.ι[ M.ty-subst-comp _ _ _ ] ⟦ d ⟧der)
⟦ assumption x ⟧der = interpret-assumption x
⟦ ∧-intro d1 d2 ⟧der = M.ι[ M.⊠-natural _ ] M.prim-pair ⟦ d1 ⟧der ⟦ d2 ⟧der
⟦ ∧-elimˡ d ⟧der = M.prim-fst (M.ι⁻¹[ M.⊠-natural _ ] ⟦ d ⟧der)
⟦ ∧-elimʳ d ⟧der = M.prim-snd (M.ι⁻¹[ M.⊠-natural _ ] ⟦ d ⟧der)
⟦ ∀-intro d ⟧der = M.ι[ M.sPi-natural _ ] (M.sdλ[ _ ] ⟦ d ⟧der)
⟦ ∀-elim {Ξ = Ξ} {φ = φ} d t ⟧der =
  M.ι[ M.≅ᵗʸ-trans (M.≅ᵗʸ-sym (M.ty-subst-cong-ty _ (frm-subst-sound φ (t /var0))))
                   (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm (subst-lemma (to-ctx Ξ) (to-ctx-subst Ξ) ⟦ t ⟧tm))
     ]
  (M.sdapp (M.ι⁻¹[ M.sPi-natural _ ] ⟦ d ⟧der) (⟦ t ⟧tm M.[ to-ctx-subst Ξ ]s))
⟦ fun-β {Ξ = Ξ} {b = b} {t = t} ⟧der =
  (M.≅ᵗᵐ-to-Id (M.≅ᵗᵐ-trans (M.sfun-β _ _)
                            (M.≅ᵗᵐ-trans (M.stm-subst-cong-subst _ (M.,ₛ-cong1 (id-subst-sound (to-ctx Ξ)) _))
                                         (tm-subst-sound b (id-subst _ ∷ t)))))
  M.[ _ ]'
⟦ suc-lit ⟧der = (M.≅ᵗᵐ-to-Id M.ssuc-sdiscr) M.[ _ ]'
⟦ nat-elim-β-zero ⟧der = (M.≅ᵗᵐ-to-Id (M.snat-β-zero _ _)) M.[ _ ]'
⟦ nat-elim-β-suc ⟧der = (M.≅ᵗᵐ-to-Id (M.snat-β-suc _ _ _)) M.[ _ ]'
⟦ if-β-true ⟧der = (M.≅ᵗᵐ-to-Id (M.sif-β-true _ _)) M.[ _ ]'
⟦ if-β-false ⟧der = (M.≅ᵗᵐ-to-Id (M.sif-β-false _ _)) M.[ _ ]'
⟦ pair-β-fst ⟧der = (M.≅ᵗᵐ-to-Id (M.sprod-β-fst _ _)) M.[ _ ]'
⟦ pair-β-snd ⟧der = (M.≅ᵗᵐ-to-Id (M.sprod-β-snd _ _)) M.[ _ ]'
⟦ bool-induction {Ξ = Ξ} {φ = φ} d1 d2 ⟧der =
  M.sbool-induction _ (M.ι[ M.≅ᵗʸ-trans (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm
                                                           (M.≅ˢ-trans (M.⊚-congˡ (M.,ₛ-cong2 _ (M.≅ᵗᵐ-sym (M.sdiscr-natural _))))
                                                                       (M.≅ˢ-sym (subst-lemma (to-ctx Ξ) (to-ctx-subst Ξ) M.strue))))
                                        (M.ty-subst-cong-ty _ (frm-subst-sound φ (true /var0)))
                          ] ⟦ d1 ⟧der)
                      (M.ι[ M.≅ᵗʸ-trans (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm
                                                           (M.≅ˢ-trans (M.⊚-congˡ (M.,ₛ-cong2 _ (M.≅ᵗᵐ-sym (M.sdiscr-natural _))))
                                                                       (M.≅ˢ-sym (subst-lemma (to-ctx Ξ) (to-ctx-subst Ξ) M.sfalse))))
                                        (M.ty-subst-cong-ty _ (frm-subst-sound φ (false /var0)))
                          ] ⟦ d2 ⟧der)
⟦ nat-induction {Ξ = Ξ} {φ = φ} d1 d2 ⟧der =
  M.snat-induction _ (M.ι[ M.≅ᵗʸ-trans (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm
                                                           (M.≅ˢ-trans (M.⊚-congˡ (M.,ₛ-cong2 _ (M.≅ᵗᵐ-sym (M.sdiscr-natural _))))
                                                                       (M.≅ˢ-sym (subst-lemma (to-ctx Ξ) (to-ctx-subst Ξ) M.szero))))
                                       (M.ty-subst-cong-ty _ (frm-subst-sound φ (lit 0 /var0)))
                         ] ⟦ d1 ⟧der)
                     (M.ι[ M.≅ᵗʸ-trans (ty-subst-seq-cong (_ ∷ˢ _ ◼) (_ ∷ˢ _ ◼) ⟦ φ ⟧frm subst-eq-proof)
                                       (M.ty-subst-cong-ty _ (frm-subst-sound φ _)) ] ⟦ d2 ⟧der)
  where
    subst-eq-proof : _ M.≅ˢ _
    subst-eq-proof =
      M.≅ˢ-trans (M.≅ˢ-sym M.⊚-assoc) (M.≅ˢ-trans (M.⊚-congʳ (M.≅ˢ-trans (M.,ₛ-⊚ _ _ _) (M.≅ˢ-trans
      (M.≅ˢ-trans (M.,ₛ-cong1 (M.≅ˢ-trans M.⊚-assoc (M.≅ˢ-trans (M.⊚-congˡ (M.,ₛ-β1 _ _)) (M.≅ˢ-trans (M.≅ˢ-sym (M.,ₛ-β1 _ _)) (M.⊚-congʳ (π-sound (to-ctx Ξ) _))))) _)
                  (M.,ₛ-cong2 _ (M.≅ᵗᵐ-trans (M.,ₛ-β2 _ _) (M.≅ᵗᵐ-sym (M.≅ᵗᵐ-trans (M.∙ₛ-natural _) (M.∙ₛ-cong (M.sdiscr-func-natural _) (M.,ₛ-β2 _ _)))))))
      (M.≅ˢ-sym (M.,ₛ-⊚ _ _ _))))) M.⊚-assoc)
