--------------------------------------------------
-- Interpretation of STT contexts and terms in the presheaf
--   model over the trivial base category
--------------------------------------------------

module Experimental.LogicalFramework.NamedVariables.STT.Interpretation where

open import Data.Maybe
open import Data.String
open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory
open import Model.CwF-Structure as M using (Ctx; Ty; Tm)
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Discrete as M

open import Experimental.ClosedTypes as M

open import Experimental.LogicalFramework.NamedVariables.STT.Syntax.Named
import Experimental.LogicalFramework.NamedVariables.STT.Syntax.Nameless as DB
open import Experimental.LogicalFramework.NamedVariables.STT.AlphaEquivalence
open import Experimental.LogicalFramework.NamedVariables.STT.Interpretation.Nameless as DBInt

private variable
  Γ Δ : CtxExpr
  T S : TyExpr


--------------------------------------------------
-- Re-export interpretation of types

open DBInt public using (⟦_⟧ty)


--------------------------------------------------
-- Definition of the interpretation of contexts and terms
--   Note that these are defined in terms of the interpretation for
--   nameless syntax. This will make it almost trivial to prove that
--   α-equivalent terms have the same interpretation.

⟦_⟧ctx : CtxExpr → Ctx ★
⟦ Γ ⟧ctx = ⟦ erase-names-ctx Γ ⟧ctx-nmls

⟦_⟧tm : TmExpr Γ T → SimpleTm ⟦ Γ ⟧ctx ⟦ T ⟧ty
⟦ t ⟧tm = ⟦ erase-names-tm t ⟧tm-nmls


--------------------------------------------------
-- Proof that weakening a term semantically corresponds to applying a π substitution

mid-weaken-sem-subst : (x : String) {Γ : CtxExpr} (S : TyExpr) (Δ : CtxExpr) → ⟦ (Γ ,, x ∈ S) ++ctx Δ ⟧ctx M.⇒ ⟦ Γ ++ctx Δ ⟧ctx
mid-weaken-sem-subst _ S ◇ = M.π
mid-weaken-sem-subst x S (Δ ,, _ ∈ T) = mid-weaken-sem-subst x S Δ s⊹

mid-weaken-var-sound : ∀ {x y} {Γ : CtxExpr} (Δ : CtxExpr) (v : Var x (Γ ++ctx Δ)) →
                       (⟦ var' x {v} {refl} ⟧tm [ mid-weaken-sem-subst y S Δ ]s) M.≅ᵗᵐ ⟦ var' x {mid-weaken-var Δ v} {mid-weaken-var-ty Δ v} ⟧tm
mid-weaken-var-sound ◇ vzero    = M.≅ᵗᵐ-refl
mid-weaken-var-sound ◇ (vsuc v) = M.≅ᵗᵐ-refl
mid-weaken-var-sound (Δ ,, _ ∈ T) vzero    = ,ₛ-β2 _ sξ
mid-weaken-var-sound (Δ ,, _ ∈ T) (vsuc v) =
  M.≅ᵗᵐ-trans (stm-subst-comp _ M.π _)
              (M.≅ᵗᵐ-trans (stm-subst-cong-subst _ (,ₛ-β1 _ sξ))
                           (M.≅ᵗᵐ-trans (M.≅ᵗᵐ-sym (stm-subst-comp _ _ M.π))
                                        (stm-subst-cong-tm (mid-weaken-var-sound Δ v) M.π)))

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

weaken-tm-sound : ∀ {x} {S : TyExpr} (t : TmExpr Γ T) → (⟦ t ⟧tm [ M.π ]s) M.≅ᵗᵐ ⟦ weaken-tm {x = x} {S = S} t ⟧tm
weaken-tm-sound t = mid-weaken-tm-sound ◇ t


--------------------------------------------------
-- Interpretation of substitutions as presheaf morphisms
--   and soundness proof of term substitution

⟦_⟧subst : SubstExpr Δ Γ → (⟦ Δ ⟧ctx M.⇒ ⟦ Γ ⟧ctx)
⟦ [] ⟧subst = M.!◇ _
⟦ _∷_/_ {_} {T} σ t _ ⟧subst = ⟦ σ ⟧subst ,ₛ ⟦ t ⟧tm
⟦ id-subst Γ ⟧subst = M.id-subst _
⟦ σ ⊚πs⟨ ◇ ⟩      ⟧subst = ⟦ σ ⟧subst
⟦ σ ⊚πs⟨ Δ ,, _ ∈ T ⟩ ⟧subst = ⟦ σ ⊚πs⟨ Δ ⟩ ⟧subst M.⊚ M.π

⊹-sound : ∀ {x} (σ : SubstExpr Δ Γ) {T : TyExpr} → (⟦ σ ⟧subst s⊹) M.≅ˢ ⟦ _⊹⟨_⟩ {T = T} σ x ⟧subst
⊹-sound σ = M.≅ˢ-refl

subst-var-sound : ∀ {x} (v : Var x Γ) (σ : SubstExpr Δ Γ) → (⟦ var' x {v} {refl} ⟧tm [ ⟦ σ ⟧subst ]s) M.≅ᵗᵐ ⟦ subst-var v σ refl ⟧tm
subst-var-sound vzero    (σ ∷ t / x) = ,ₛ-β2 ⟦ σ ⟧subst ⟦ t ⟧tm
subst-var-sound (vsuc v) (σ ∷ t / x) =
  M.≅ᵗᵐ-trans (stm-subst-comp _ M.π (⟦ σ ⟧subst ,ₛ ⟦ t ⟧tm))
              (M.≅ᵗᵐ-trans (stm-subst-cong-subst _ (,ₛ-β1 ⟦ σ ⟧subst ⟦ t ⟧tm))
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
tm-subst-sound (var' x {v} {refl}) σ    | nothing = subst-var-sound v σ
tm-subst-sound (lam[ x ∈ _ ] t) σ       | nothing =
  M.≅ᵗᵐ-trans (sλ-natural {b = ⟦ t ⟧tm} ⟦ σ ⟧subst)
              (sλ-cong (tm-subst-sound t (σ ⊹⟨ x ⟩)))
tm-subst-sound (f ∙ t) σ                | nothing =
  M.≅ᵗᵐ-trans (∙ₛ-natural _) (∙ₛ-cong (tm-subst-sound f σ) (tm-subst-sound t σ))
tm-subst-sound zero σ                   | nothing = sdiscr-natural _
tm-subst-sound suc σ                    | nothing = sdiscr-func-natural _
tm-subst-sound (nat-elim a f) σ         | nothing =
  M.≅ᵗᵐ-trans (snat-elim-natural _) (snat-elim-cong (tm-subst-sound a σ) (tm-subst-sound f σ))
tm-subst-sound true σ                   | nothing = sdiscr-natural _
tm-subst-sound false σ                  | nothing = sdiscr-natural _
tm-subst-sound (if b t f) σ             | nothing =
  M.≅ᵗᵐ-trans (sif-natural _) (sif-cong (tm-subst-sound b σ) (tm-subst-sound t σ) (tm-subst-sound f σ))
tm-subst-sound (pair t s) σ             | nothing =
  M.≅ᵗᵐ-trans (spair-natural _) (spair-cong (tm-subst-sound t σ) (tm-subst-sound s σ))
tm-subst-sound (fst p) σ                | nothing = M.≅ᵗᵐ-trans (sfst-natural _) (sfst-cong (tm-subst-sound p σ))
tm-subst-sound (snd p) σ                | nothing = M.≅ᵗᵐ-trans (ssnd-natural _) (ssnd-cong (tm-subst-sound p σ))


--------------------------------------------------
-- Proof of a lemma needed in the soundness proof of the logical framework

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
