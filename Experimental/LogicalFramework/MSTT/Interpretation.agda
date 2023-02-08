--------------------------------------------------
-- Interpretation of MSTT contexts and terms in a presheaf model
--------------------------------------------------

module Experimental.LogicalFramework.MSTT.Interpretation where

open import Data.Maybe
open import Data.String
open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory
open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
import Model.Modality as M
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Constant as M

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Syntax.Named as Syn
open Syn.AtomicSub
import Experimental.LogicalFramework.MSTT.Syntax.Nameless as DB
open import Experimental.LogicalFramework.MSTT.AlphaEquivalence
open import Experimental.LogicalFramework.MSTT.Interpretation.Nameless as DBInt
open import Experimental.LogicalFramework.MSTT.Interpretation.ModeTheory as MTInt

private variable
  m n : Mode
  Γ Δ : Ctx m
  T S : Ty m


--------------------------------------------------
-- Re-export interpretation of modes, modalities, and types

open DBInt public using (⟦_⟧ty; ty-natural; ty-closed-natural)
open MTInt public


--------------------------------------------------
-- Definition of the interpretation of contexts and terms
--   Note that these are defined in terms of the interpretation for
--   nameless syntax. This will make it almost trivial to prove that
--   α-equivalent terms have the same interpretation.

⟦_⟧ctx : Ctx m → SemCtx ⟦ m ⟧mode
⟦ Γ ⟧ctx = ⟦ erase-names-ctx Γ ⟧ctx-nmls

⟦_⟧tm : Tm Γ T → SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty
⟦ t ⟧tm = ⟦ erase-names-tm t ⟧tm-nmls

{-
--------------------------------------------------
-- Proof that weakening a term semantically corresponds to applying a π substitution

mid-weaken-sem-subst : (x : String) {Γ : Ctx} (S : Ty) (Δ : Ctx) → ⟦ (Γ ,, x ∈ S) ++ctx Δ ⟧ctx M.⇒ ⟦ Γ ++ctx Δ ⟧ctx
mid-weaken-sem-subst _ S ◇ = M.π
mid-weaken-sem-subst x S (Δ ,, _ ∈ T) = mid-weaken-sem-subst x S Δ s⊹

mid-weaken-var-sound : ∀ {x y} {Γ : Ctx} (Δ : Ctx) (v : Var x (Γ ++ctx Δ) T) →
                       (⟦ var' x {v} ⟧tm [ mid-weaken-sem-subst y S Δ ]s) M.≅ᵗᵐ ⟦ var' x {mid-weaken-var Δ v} ⟧tm
mid-weaken-var-sound ◇ vzero    = M.reflᵗᵐ
mid-weaken-var-sound ◇ (vsuc v) = M.reflᵗᵐ
mid-weaken-var-sound (Δ ,, _ ∈ T) vzero    = ,ₛ-β2 _ sξ
mid-weaken-var-sound (Δ ,, _ ∈ T) (vsuc v) =
  M.transᵗᵐ (stm-subst-comp _ M.π _)
            (M.transᵗᵐ (stm-subst-cong-subst _ (,ₛ-β1 _ sξ))
                       (M.transᵗᵐ (M.symᵗᵐ (stm-subst-comp _ _ M.π))
                                  (stm-subst-cong-tm (mid-weaken-var-sound Δ v) M.π)))

mid-weaken-tm-sound : ∀ {x} {S : Ty} (Δ : Ctx) (t : Tm (Γ ++ctx Δ) T) →
                      (⟦ t ⟧tm [ mid-weaken-sem-subst x S Δ ]s) M.≅ᵗᵐ ⟦ mid-weaken-tm {S = S} Δ t ⟧tm
mid-weaken-tm-sound Δ (var' x {v}) = mid-weaken-var-sound Δ v
mid-weaken-tm-sound Δ (lam[ _ ∈ _ ] t) = M.transᵗᵐ (sλ-natural _) (sλ-cong (mid-weaken-tm-sound (Δ ,, _ ∈ _) t))
mid-weaken-tm-sound Δ (f ∙ t) = M.transᵗᵐ (∙ₛ-natural _) (∙ₛ-cong (mid-weaken-tm-sound Δ f) (mid-weaken-tm-sound Δ t))
mid-weaken-tm-sound Δ zero = sconst-natural _
mid-weaken-tm-sound Δ suc = sconst-func-natural _
mid-weaken-tm-sound Δ (nat-elim a f) = M.transᵗᵐ (snat-elim-natural _) (snat-elim-cong (mid-weaken-tm-sound Δ a) (mid-weaken-tm-sound Δ f))
mid-weaken-tm-sound Δ true = sconst-natural _
mid-weaken-tm-sound Δ false = sconst-natural _
mid-weaken-tm-sound Δ (if b t f) =
  M.transᵗᵐ (sif-natural _) (sif-cong (mid-weaken-tm-sound Δ b) (mid-weaken-tm-sound Δ t) (mid-weaken-tm-sound Δ f))
mid-weaken-tm-sound Δ (pair t s) = M.transᵗᵐ (spair-natural _) (spair-cong (mid-weaken-tm-sound Δ t) (mid-weaken-tm-sound Δ s))
mid-weaken-tm-sound Δ (fst p) = M.transᵗᵐ (sfst-natural _) (sfst-cong (mid-weaken-tm-sound Δ p))
mid-weaken-tm-sound Δ (snd p) = M.transᵗᵐ (ssnd-natural _) (ssnd-cong (mid-weaken-tm-sound Δ p))

weaken-tm-sound : ∀ {x} {S : Ty} (t : Tm Γ T) → (⟦ t ⟧tm [ M.π ]s) M.≅ᵗᵐ ⟦ weaken-tm {x = x} {S = S} t ⟧tm
weaken-tm-sound t = mid-weaken-tm-sound ◇ t
-}

--------------------------------------------------
-- Interpretation of substitutions as presheaf morphisms
--   and soundness proof of term substitution

⟦⟧ltel : {Γ : Ctx m} (Λ : LockTele m n) → ⟦ Γ ++ltel Λ ⟧ctx M.≅ᶜ M.lock ⟦ locks-ltel Λ ⟧mod ⟦ Γ ⟧ctx
⟦⟧ltel {m} ◇ = M.reflᶜ
⟦⟧ltel (Λ ,lock⟨ μ ⟩) =
  M.transᶜ (M.ctx-functor-cong (M.ctx-functor ⟦ μ ⟧mod) (⟦⟧ltel Λ))
           (M.symᶜ (M.eq-lock (⟦ⓜ⟧-sound (locks-ltel Λ) μ) _))

⟦_⟧asub : AtomicSub Δ Γ → (⟦ Δ ⟧ctx M.⇒ ⟦ Γ ⟧ctx)
⟦ []as ⟧asub = M.!◇ _
⟦ _∷ᵃˢ_/_ {μ = μ} {T = T} σ t x ⟧asub = M.to-ext-subst _ ⟦ σ ⟧asub (M.ι[ ty-natural ⟨ μ ∣ T ⟩ ] M.mod-intro ⟦ μ ⟧mod ⟦ t ⟧tm)
⟦ σ ⊚ᵃˢπ ⟧asub = ⟦ σ ⟧asub M.⊚ M.π
⟦ σ ,aslock⟨ μ ⟩ ⟧asub = M.lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧asub
⟦ atomic-key-sub Λ₁ Λ₂ α ⟧asub =
  M.to (⟦⟧ltel Λ₂)
  M.⊚ (M.key-subst ⟦ α ⟧two-cell)
  M.⊚ M.from (⟦⟧ltel Λ₁)

⟦_⟧sub : Sub Δ Γ → (⟦ Δ ⟧ctx M.⇒ ⟦ Γ ⟧ctx)
⟦ id-sub ⟧sub = M.id-subst _
⟦ σ ⊚a τᵃ ⟧sub = ⟦ σ ⟧sub M.⊚ ⟦ τᵃ ⟧asub


{-
⊹-sound : ∀ {x} (σ : Subst Δ Γ) {T : Ty} → (⟦ σ ⟧subst s⊹) M.≅ˢ ⟦ _⊹⟨_⟩ {T = T} σ x ⟧subst
⊹-sound σ = M.reflˢ

subst-var-sound : ∀ {x} (v : Var x Γ T) (σ : Subst Δ Γ) → (⟦ var' x {v} ⟧tm [ ⟦ σ ⟧subst ]s) M.≅ᵗᵐ ⟦ subst-var v σ ⟧tm
subst-var-sound vzero    (σ ∷ t / x) = ,ₛ-β2 ⟦ σ ⟧subst ⟦ t ⟧tm
subst-var-sound (vsuc v) (σ ∷ t / x) =
  M.transᵗᵐ (stm-subst-comp _ M.π (⟦ σ ⟧subst ,ₛ ⟦ t ⟧tm))
            (M.transᵗᵐ (stm-subst-cong-subst _ (,ₛ-β1 ⟦ σ ⟧subst ⟦ t ⟧tm))
                       (subst-var-sound v σ))
subst-var-sound v (id-subst Γ) = stm-subst-id _
subst-var-sound v (σ ⊚πs⟨ ◇ ⟩)      = subst-var-sound v σ
subst-var-sound v (σ ⊚πs⟨ Δ ,, _ ∈ T ⟩) =
  M.transᵗᵐ (M.symᵗᵐ (stm-subst-comp _ _ _))
            (M.transᵗᵐ (stm-subst-cong-tm (subst-var-sound v (σ ⊚πs⟨ Δ ⟩)) _)
                       (weaken-tm-sound (subst-var v (σ ⊚πs⟨ Δ ⟩))))

tm-subst-sound : (t : Tm Γ T) (σ : Subst Δ Γ) → (⟦ t ⟧tm [ ⟦ σ ⟧subst ]s) M.≅ᵗᵐ ⟦ t [ σ ]tm ⟧tm
tm-subst-sound t σ with is-special-subst? σ
tm-subst-sound t .(id-subst Γ)          | just (id-subst Γ) = stm-subst-id ⟦ t ⟧tm
tm-subst-sound t .(σ ⊚πs⟨ ◇ ⟩)          | just (σ ⊚πs⟨ ◇ ⟩) = tm-subst-sound t σ
tm-subst-sound t .(σ ⊚πs⟨ Θ ,, _ ∈ T ⟩) | just (σ ⊚πs⟨ Θ ,, _ ∈ T ⟩) =
  M.transᵗᵐ (M.symᵗᵐ (M.stm-subst-comp _ _ _))
            (M.transᵗᵐ (stm-subst-cong-tm (tm-subst-sound t (σ ⊚πs⟨ Θ ⟩)) _)
                       (weaken-tm-sound (t [ σ ⊚πs⟨ Θ ⟩ ]tm)))
tm-subst-sound (var' x {v}) σ           | nothing = subst-var-sound v σ
tm-subst-sound (lam[ x ∈ _ ] t) σ       | nothing =
  M.transᵗᵐ (sλ-natural {b = ⟦ t ⟧tm} ⟦ σ ⟧subst)
            (sλ-cong (tm-subst-sound t (σ ⊹⟨ x ⟩)))
tm-subst-sound (f ∙ t) σ                | nothing =
  M.transᵗᵐ (∙ₛ-natural _) (∙ₛ-cong (tm-subst-sound f σ) (tm-subst-sound t σ))
tm-subst-sound zero σ                   | nothing = sconst-natural _
tm-subst-sound suc σ                    | nothing = sconst-func-natural _
tm-subst-sound (nat-elim a f) σ         | nothing =
  M.transᵗᵐ (snat-elim-natural _) (snat-elim-cong (tm-subst-sound a σ) (tm-subst-sound f σ))
tm-subst-sound true σ                   | nothing = sconst-natural _
tm-subst-sound false σ                  | nothing = sconst-natural _
tm-subst-sound (if b t f) σ             | nothing =
  M.transᵗᵐ (sif-natural _) (sif-cong (tm-subst-sound b σ) (tm-subst-sound t σ) (tm-subst-sound f σ))
tm-subst-sound (pair t s) σ             | nothing =
  M.transᵗᵐ (spair-natural _) (spair-cong (tm-subst-sound t σ) (tm-subst-sound s σ))
tm-subst-sound (fst p) σ                | nothing = M.transᵗᵐ (sfst-natural _) (sfst-cong (tm-subst-sound p σ))
tm-subst-sound (snd p) σ                | nothing = M.transᵗᵐ (ssnd-natural _) (ssnd-cong (tm-subst-sound p σ))


--------------------------------------------------
-- Proof of a lemma needed in the soundness proof of the logical framework

subst-lemma : (Δ : Ctx) {Γ : M.Ctx ★} {T : ClosedTy ★}
              (σ : Γ M.⇒ ⟦ Δ ⟧ctx) (t : SimpleTm ⟦ Δ ⟧ctx T) →
              (⟦ id-subst Δ ⟧subst ,ₛ t) M.⊚ σ M.≅ˢ (σ s⊹) M.⊚ (M.id-subst Γ ,ₛ (t [ σ ]s))
subst-lemma Δ σ t =
  M.transˢ (M.,ₛ-⊚ _ _ _)
           (M.transˢ (M.,ₛ-cong1 (M.⊚-id-substˡ _) _)
                     (M.symˢ (M.transˢ (M.,ₛ-⊚ _ _ _)
                                       (M.transˢ (M.,ₛ-cong2 _ (M.,ₛ-β2 _ _))
                                                 (M.,ₛ-cong1 (M.transˢ M.⊚-assoc (M.transˢ (M.⊚-congˡ (M.,ₛ-β1 _ _))
                                                                                           (M.⊚-id-substʳ _))) _)))))
-}
