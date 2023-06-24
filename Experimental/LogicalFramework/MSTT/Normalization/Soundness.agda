open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheorySemantics

module Experimental.LogicalFramework.MSTT.Normalization.Soundness
  (ℳ : ModeTheory) (⟦ℳ⟧ : ModeTheorySemantics ℳ)
  where

open import Data.Nat
open import Data.Maybe as Mb using (Maybe; just; nothing)
open import Data.Unit.Polymorphic
open import Level using (Level)

open ModeTheory ℳ
open ModeTheorySemantics ⟦ℳ⟧

open import Model.BaseCategory
open import Model.CwF-Structure as M
  renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.CwF-Structure.ClosedType
import Model.Type.Function as M
import Model.Type.Product as M
import Model.Type.Constant as M
import Model.Modality as M

open import Experimental.LogicalFramework.MSTT.Syntax.Nameless ℳ
open import Experimental.LogicalFramework.MSTT.Interpretation.Nameless ℳ ⟦ℳ⟧ renaming (⟦_⟧tm-nmls to ⟦_⟧tm)
import Experimental.LogicalFramework.MSTT.Normalization.Helpers as Mb
open import Experimental.LogicalFramework.MSTT.Normalization ℳ

private variable
  ℓ ℓ' : Level
  A B : Set ℓ
  m n : Mode
  Γ Δ : Ctx m
  T S : Ty m  


-- Lifting a predicate to the Maybe monad
data Lift (P : A → Set ℓ) : Maybe A → Set ℓ where
  lift-just : {a : A} → P a → Lift P (just a)
  lift-nothing : Lift P nothing

return : {P : A → Set ℓ} {a : A} → P a → Lift P (just a)
return = lift-just

_>>=_ : {P : A → Set ℓ} {Q : B → Set ℓ'} {ma : Maybe A} {f : A → Maybe B} →
        Lift P ma → (∀ {a} → P a → Lift Q (f a)) → Lift Q (ma Mb.>>= f)
lift-just p  >>= f-pres = f-pres p
lift-nothing >>= f-pres = lift-nothing

infixl 4 _<$>_ _<*>_ _<∙>_
_<$>_ : {P : A → Set} {Q : B → Set} {ma : Maybe A} {f : A → B} →
        (∀ {a} → P a → Q (f a)) → Lift P ma → Lift Q (f Mb.<$> ma)
f-pres <$> lift-just p  = lift-just (f-pres p)
f-pres <$> lift-nothing = lift-nothing

_<*>_ : {P : A → Set} {Q : B → Set} {ma : Maybe A} {f : Maybe (A → B)} →
        Lift (λ g → ∀ {a} → P a → Q (g a)) f → Lift P ma → Lift Q (f Mb.<*> ma)
lift-just f-pres <*> lift-just p  = lift-just (f-pres p)
lift-just f-pres <*> lift-nothing = lift-nothing
lift-nothing     <*> mp           = lift-nothing

_<∙>_ : {P Q : A → Set} {ma : Maybe A} →
        (∀ {a} → P a → Q a) → Lift P ma → Lift Q ma
impl <∙> lift-just p  = lift-just (impl p)
impl <∙> lift-nothing = lift-nothing


-- Proving soundness of the normalization function
NormalizeSoundness : Tm Γ T → NF Γ T → Set
NormalizeSoundness t nf = ⟦ nf-to-tm nf ⟧tm M.≅ᵗᵐ ⟦ t ⟧tm

normalize-sound : (n : ℕ) (t : Tm Γ T) → Lift (NormalizeSoundness t) (normalize n t)
normalize-sound zero t = lift-nothing
normalize-sound (suc n) (var' x α) = return M.reflᵗᵐ
normalize-sound (suc n) (mod⟨ μ ⟩ t) = M.mod-intro-cong ⟦ μ ⟧mod <$> normalize-sound (suc n) t
normalize-sound (suc n) (mod-elim ρ μ x t s) = {!!}
normalize-sound (suc n) (lam[ μ ∣ x ∈ T ] s) = return M.reflᵗᵐ
normalize-sound (suc n) (f ∙ t) = {!!}
normalize-sound (suc n) zero = return M.reflᵗᵐ
normalize-sound (suc n) (suc t) = M.const-map-cong suc <$> normalize-sound (suc n) t
normalize-sound (suc n) (nat-rec z s t) = normalize-sound (suc n) t >>= (λ {x} → normalize-nat-rec-sound n z s t {x})
  where
    normalize-nat-rec-sound : (n : ℕ) (z : Tm Γ T) (s : Tm Γ (T ⇛ T)) (t : Tm Γ Nat') {nft : NF Γ Nat'} →
                              NormalizeSoundness t nft → Lift (NormalizeSoundness (nat-rec z s t)) (NormalizeNatElim.normalize-nat-rec n z s t (suc n) nft)
    normalize-nat-rec-sound n z s t {neutral net} et = (λ ez → M.nat-rec-cong ez M.reflᵗᵐ et) <$> normalize-sound (suc n) z
    normalize-nat-rec-sound n z s t {zero}        et = (λ ez → M.transᵗᵐ (M.symᵗᵐ (M.β-nat-zero _ _)) (M.nat-rec-cong ez M.reflᵗᵐ et)) <∙> normalize-sound (suc n) z
    normalize-nat-rec-sound n z s t {suc nft}     et = {!{!!} <∙> normalize-sound n (s ∙¹ nat-rec z s (nf-to-tm nft))!}
normalize-sound (suc n) true = return M.reflᵗᵐ
normalize-sound (suc n) false = return M.reflᵗᵐ
normalize-sound (suc n) (if b t f) =
  (λ {x} → normalize-if-sound b t f {x}) <$> normalize-sound (suc n) b <*> normalize-sound (suc n) t <*> normalize-sound (suc n) f
  where
    normalize-if-sound : (b : Tm Γ Bool') (t f : Tm Γ T)
                         {nfb : NF Γ Bool'} → NormalizeSoundness b nfb →
                         {nft : NF Γ T} →     NormalizeSoundness t nft →
                         {nff : NF Γ T} →     NormalizeSoundness f nff →
                         NormalizeSoundness (if b t f) (NormalizeIf.normalize-if n b t f nfb nft nff)
    normalize-if-sound b t f {neutral neb} eb et ef = M.if'-cong eb et ef
    normalize-if-sound b t f {true}        eb et ef = M.transᵗᵐ (M.symᵗᵐ (M.β-bool-true _ _)) (M.if'-cong eb et ef)
    normalize-if-sound b t f {false}       eb et ef = M.transᵗᵐ (M.symᵗᵐ (M.β-bool-false _ _)) (M.if'-cong eb et ef)
normalize-sound (suc n) (pair t s) =
  (λ e e' → M.pair-cong e e') <$> normalize-sound (suc n) t <*> normalize-sound (suc n) s
normalize-sound (suc n) (fst p) = (λ {x} → normalize-fst-sound p {x}) <$> normalize-sound (suc n) p
  where
    normalize-fst-sound : (p : Tm Γ (T ⊠ S)) {nf : NF Γ (T ⊠ S)} →
                          NormalizeSoundness p nf → NormalizeSoundness (fst p) (NormalizeFst.normalize-fst n p nf)
    normalize-fst-sound p {neutral nep} = M.fst-cong
    normalize-fst-sound p {pair nft _}  = λ e → M.transᵗᵐ (M.symᵗᵐ (M.β-⊠-fst _ _)) (M.fst-cong e)
normalize-sound (suc n) (snd p) = (λ {x} → normalize-snd-sound p {x}) <$> normalize-sound (suc n) p
  where
    normalize-snd-sound : (p : Tm Γ (T ⊠ S)) {nf : NF Γ (T ⊠ S)} →
                          NormalizeSoundness p nf → NormalizeSoundness (snd p) (NormalizeSnd.normalize-snd n p nf)
    normalize-snd-sound p {neutral nep} = M.snd-cong
    normalize-snd-sound p {pair nft _}  = λ e → M.transᵗᵐ (M.symᵗᵐ (M.β-⊠-snd _ _)) (M.snd-cong e)
