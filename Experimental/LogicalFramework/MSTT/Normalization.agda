open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.MSTT.Normalization
  (𝒫 : MSTT-Parameter)
  where

open import Data.Nat hiding (_/_)
open import Data.Maybe
open import Function

open MSTT-Parameter 𝒫

import Model.CwF-Structure as M
import Model.DRA as M
import Model.Type.Function as M
import Model.Type.Constant as M
import Model.Type.Product as M

open import Experimental.LogicalFramework.MSTT.Normalization.Helpers
open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.MSTT.Soundness.Substitution 𝒫

private variable
  m n o : Mode
  μ ρ : Modality m n
  T S : Ty m
  Γ Δ : Ctx m


Fuel : Set
Fuel = ℕ

record NormalizeResult (t : Tm Γ T) : Set where
  constructor normres
  field
    nt : Tm Γ T
    sound : ⟦ t ⟧tm M.≅ᵗᵐ ⟦ nt ⟧tm


normalize : Fuel → (t : Tm Γ T) → Maybe (NormalizeResult t)
normalize zero t = nothing -- not enough fuel left
normalize (suc n) (var' x {v}) = just $ normres (var' x {v}) M.reflᵗᵐ
normalize (suc n) (mod⟨ μ ⟩ t) = normalize-mod <$> normalize (suc n) t
  where
    normalize-mod : NormalizeResult t → NormalizeResult (mod⟨ μ ⟩ t)
    normalize-mod (normres nt et) = normres (mod⟨ μ ⟩ nt) (M.dra-intro-cong ⟦ μ ⟧mod et)
normalize (suc n) (mod-elim {T = T} {S = S} ρ μ x t s) = normalize (suc n) t >>= normalize-mod-elim
  where
    normalize-mod-elim : NormalizeResult t → Maybe (NormalizeResult (mod-elim ρ μ x t s))
    normalize-mod-elim (normres (mod⟨ μ ⟩ nt) et) = do
      normres ns es ← normalize n (s [ fuselocks-tm nt / x ]tmˢ)
      just $ normres ns (
        M.transᵗᵐ (M.cl-tm-subst-cong-subst-2-1 (ty-closed-natural S) (
          M.transˢ (M.⊚-congʳ (M.symˢ (M./cl-cong-cl (M.ⓓ-preserves-cl ⟦ ρ ⟧mod ⟦ μ ⟧mod (ty-closed-natural T))))) (
          M.transˢ (M./cl-,,-cong (M.symᶜᵗʸ (M.eq-dra-closed (⟦ⓜ⟧-sound ρ μ) (ty-closed-natural T))) _) (
          M.transˢ (M./cl-cong (ty-closed-natural ⟨ ρ ⓜ μ ∣ T ⟩) (M.move-ι⁻¹-left (M.symᵗᵐ (
            M.transᵗᵐ (M.eq-dra-intro-closed (⟦ⓜ⟧-sound ρ μ) (ty-closed-natural T) _) (M.dra-intro-cong ⟦ ρ ⟧mod (
            M.transᵗᵐ (M.dra-intro-cong ⟦ μ ⟧mod (
              M.transᵗᵐ (M.cl-tm-subst-cong-tm (ty-closed-natural T) (fuselocks-tm-sound ρ μ nt)) (
              M.cl-tm-subst-cong-subst-2-0 (ty-closed-natural T) (M.key-subst-eq (M.isoʳ (⟦ⓜ⟧-sound ρ μ)))))) (
            M.symᵗᵐ et))))))) (
          /cl-sound (fuselocks-tm nt) x))))) (
        M.transᵗᵐ (tm-sub-sound s (fuselocks-tm nt / x))
        es))
    normalize-mod-elim (normres nt            et) = do
      normres ns es ← normalize n s
      just $ normres (mod-elim ρ μ x nt ns)
                     (M.dra-let-cong ⟦ ρ ⟧mod ⟦ μ ⟧mod
                                     (ty-closed-natural T)
                                     (ty-closed-natural S)
                                     et
                                     (M.cl-tm-subst-cong-tm (ty-closed-natural S) es))
normalize (suc n) (lam[ μ ∣ _ ∈ T ] b) = normalize-lam <$> normalize (suc n) b
  where
    normalize-lam : NormalizeResult b → NormalizeResult (lam[ μ ∣ _ ∈ T ] b)
    normalize-lam (normres nb eb) = normres (lam[ μ ∣ _ ∈ T ] nb) (M.lam-cong _ (M.ι-cong eb))
normalize (suc n) (_∙_ {S = S} {μ = μ} f t) = do
  nrf ← normalize (suc n) f
  nrt ← normalize (suc n) t
  normalize-app nrf nrt
  where
    normalize-app : NormalizeResult f → NormalizeResult t → Maybe (NormalizeResult (f ∙ t))
    normalize-app (normres (lam[ μ ∣ x ∈ T ] b) ef) (normres nt et) = do
      normres nb eb ← normalize n (b [ nt / x ]tmˢ)
      just $ normres nb
        (M.transᵗᵐ (M.app-cong ef (M.dra-intro-cong ⟦ μ ⟧mod et)) (
         M.transᵗᵐ (M.⇛-cl-β (ty-closed-natural ⟨ μ ∣ T ⟩) (ty-closed-natural S) _ _) (
         M.transᵗᵐ (M.cl-tm-subst-cong-subst (ty-closed-natural S) (/cl-sound nt x)) (
         M.transᵗᵐ (tm-sub-sound b (nt / x))
         eb))))
    normalize-app (normres nf ef)                   (normres nt et) = just $ normres (nf ∙ nt) (M.app-cong ef (M.dra-intro-cong ⟦ μ ⟧mod et))
normalize (suc n) zero = just $ normres zero M.reflᵗᵐ
normalize (suc n) (suc t) = normalize-suc <$> normalize (suc n) t
  where
    normalize-suc : NormalizeResult t → NormalizeResult (suc t)
    normalize-suc (normres nt et) = normres (suc nt) (M.const-map-cong suc et)
normalize (suc n) (nat-rec z s t) = normalize (suc n) t >>= normalize-nat-rec
  where
    normalize-nat-rec : NormalizeResult t → Maybe (NormalizeResult (nat-rec z s t))
    normalize-nat-rec (normres zero     et) = do
      normres nz ez ← normalize n z
      just $ normres nz (M.transᵗᵐ (M.nat-rec-cong ez M.reflᵗᵐ et) (M.nat-rec-β-zero _ _))
    normalize-nat-rec (normres (suc nt) et) = do
      normres nr er ← normalize n (s ∙¹ nat-rec z s nt)
      just $ normres nr
        (M.transᵗᵐ (M.nat-rec-cong M.reflᵗᵐ M.reflᵗᵐ et) (
         M.transᵗᵐ (M.nat-rec-β-suc _ _ _) (
         M.transᵗᵐ (M.symᵗᵐ (∙¹-sound s (nat-rec z s nt)))
         er)))
    normalize-nat-rec (normres nt       et) = do
      normres nz ez ← normalize n z
      normres ns es ← normalize n s
      just $ normres (nat-rec nz ns nt) (M.nat-rec-cong ez es et)
normalize (suc n) true = just $ normres true M.reflᵗᵐ
normalize (suc n) false = just $ normres false M.reflᵗᵐ
normalize (suc n) (if b t f) = normalize-if <$> normalize (suc n) b <*> normalize (suc n) t <*> normalize (suc n) f
  where
    normalize-if : NormalizeResult b → NormalizeResult t → NormalizeResult f → NormalizeResult (if b t f)
    normalize-if (normres true  eb) (normres nt et) _               = normres nt (M.transᵗᵐ (M.if'-cong eb et M.reflᵗᵐ) (M.if-β-true _ _))
    normalize-if (normres false eb) _               (normres nf ef) = normres nf (M.transᵗᵐ (M.if'-cong eb M.reflᵗᵐ ef) (M.if-β-false _ _))
    normalize-if (normres nb    eb) (normres nt et) (normres nf ef) = normres (if nb nt nf) (M.if'-cong eb et ef)
normalize (suc n) (pair t s) = normalize-pair <$> normalize (suc n) t <*> normalize (suc n) s
  where
    normalize-pair : NormalizeResult t → NormalizeResult s → NormalizeResult (pair t s)
    normalize-pair (normres nt et) (normres ns es) = normres (pair nt ns) (M.pair-cong et es)
normalize (suc n) (fst p) = normalize-fst <$> normalize (suc n) p
  where
    normalize-fst : NormalizeResult p → NormalizeResult (fst p)
    normalize-fst (normres (pair nt _) ep) = normres nt (M.transᵗᵐ (M.fst-cong ep) (M.⊠-β-fst _ _))
    normalize-fst (normres np          ep) = normres (fst np) (M.fst-cong ep)
normalize (suc n) (snd p) = normalize-snd <$> normalize (suc n) p
  where
    normalize-snd : NormalizeResult p → NormalizeResult (snd p)
    normalize-snd (normres (pair _ ns) ep) = normres ns (M.transᵗᵐ (M.snd-cong ep) (M.⊠-β-snd _ _))
    normalize-snd (normres np          ep) = normres (snd np) (M.snd-cong ep)
normalize (suc n) (ext c args e) = {!!}
