open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Experimental.LogicalFramework.Parameter.bPropExtensionSemantics
open import Data.String

module Experimental.LogicalFramework.Proof.Context
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 String 𝓉)
  (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 _ _)
  where

open import Data.String as Str
open import Function using (id)
import Relation.Binary.PropositionalEquality as Ag
open import Relation.Nullary

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.DRA as DRA hiding (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; TwoCell)

open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.bProp 𝒫 𝒷 ⟦𝒷⟧
open import Experimental.LogicalFramework.Proof.CheckingMonad

open import Experimental.LogicalFramework.Proof.Equality 𝒫 𝒷
open import Experimental.LogicalFramework.Postulates 𝒫 𝒷 ⟦𝒷⟧

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  Γ Δ : Ctx m
  Λ : LockTele m n
  T S R U : Ty m
  φ ψ : bProp Γ
  x y : String


-- A proof context can, apart from MSTT variables, also consist of propositions (assumptions).
data ProofCtx (m : Mode) : Set
to-ctx : ProofCtx m → Ctx m

infixl 2 _,,ᵛ_∣_∈_ _,,ᵇ_∣_∈_
data ProofCtx m where
  ◇ : ProofCtx m
  _,,ᵛ_∣_∈_ : (Ξ : ProofCtx m) (μ : Modality n m) (x : String) (T : Ty n) → ProofCtx m
  _,,ᵇ_∣_∈_ : (Ξ : ProofCtx m) (μ : Modality n m) (x : String) (φ : bProp ((to-ctx Ξ) ,lock⟨ μ ⟩)) → ProofCtx m
  _,lock⟨_⟩ : (Ξ : ProofCtx n) (μ : Modality m n) → ProofCtx m

to-ctx ◇               = ◇
to-ctx (Ξ ,,ᵛ μ ∣ x ∈ T) = (to-ctx Ξ) ,, μ ∣ x ∈ T
to-ctx (Ξ ,,ᵇ _ ∣ _ ∈ _) = to-ctx Ξ
to-ctx (Ξ ,lock⟨ μ ⟩)   = (to-ctx Ξ) ,lock⟨ μ ⟩

private variable
  Ξ : ProofCtx m


-- In the same way as variables in MSTT, assumptions are internally
--  referred to using De Bruijn indices, but we keep track of their
--  names. The (proof-relevant) predicate Assumption x Ξ Λ expresses
--  that an assumption with name x is present in proof context Ξ ,ˡᵗ Λ.
--  Note that we do not keep track of the proposition in the
--  Assumption type (in contrast to the type of variables in MSTT).
--  It is not guaranteed that the assumption can be used. For that purpose,
--  an additional 2-cell is needed.
data Assumption (x : String) : ProofCtx m → LockTele m n → Set where
  azero : {Ξ : ProofCtx m} {μ : Modality n m} {φ : bProp (to-ctx Ξ ,lock⟨ μ ⟩)} {Λ : LockTele m n} →
          Assumption x (Ξ ,,ᵇ μ ∣ x ∈ φ) Λ
  asuc  : {Ξ : ProofCtx m} {Λ : LockTele m n}
          {ρ : Modality o m} {y : String} {ψ : bProp (to-ctx Ξ ,lock⟨ ρ ⟩)} →
          Assumption x Ξ Λ →
          Assumption x (Ξ ,,ᵇ ρ ∣ y ∈ ψ) Λ
  avar  : {Ξ : ProofCtx m} {Λ : LockTele m n}
          {ρ : Modality o m} {y : String} {T : Ty o} →
          Assumption x Ξ Λ →
          Assumption x (Ξ ,,ᵛ ρ ∣ y ∈ T) Λ
  alock : {Ξ : ProofCtx p} {ρ : Modality m p} {Λ : LockTele m n} →
          Assumption x Ξ (lock⟨ ρ ⟩, Λ) →
          Assumption x (Ξ ,lock⟨ ρ ⟩) Λ

as-cod-mode : Assumption x Ξ Λ → Mode
as-cod-mode (azero {m = m}) = m
as-cod-mode (asuc a) = as-cod-mode a
as-cod-mode (avar a) = as-cod-mode a
as-cod-mode (alock a) = as-cod-mode a

as-mod : {Λ : LockTele m n} (a : Assumption x Ξ Λ) → Modality n (as-cod-mode a)
as-mod (azero {μ = μ}) = μ
as-mod (asuc a) = as-mod a
as-mod (avar a) = as-mod a
as-mod (alock a) = as-mod a

as-lt : {Λ : LockTele m n} (a : Assumption x Ξ Λ) → LockTele (as-cod-mode a) n
as-lt (azero {Λ = Λ}) = Λ
as-lt (asuc a) = as-lt a
as-lt (avar a) = as-lt a
as-lt (alock a) = as-lt a

lookup-assumption : {Ξ : ProofCtx m} {Λ : LockTele m n}
                    (a : Assumption x Ξ Λ) →
                    TwoCell (as-mod a) (locksˡᵗ (as-lt a)) →
                    bProp (to-ctx Ξ ,ˡᵗ Λ)
lookup-assumption (azero {μ = μ} {φ = φ} {Λ = Λ}) α = φ [ keyʳ Λ (lock⟨ μ ⟩, ◇) α ]bpropʳ
lookup-assumption (asuc a) α = lookup-assumption a α
lookup-assumption (avar {Λ = Λ} a) α = (lookup-assumption a α) [ πʳ ,locksʳ⟨ Λ ⟩ ]bpropʳ
lookup-assumption (alock a) α = lookup-assumption a α


contains-assumption? : (x : String) (Ξ : ProofCtx m) (Λ : LockTele m n) →
                       PCM (Assumption x Ξ Λ)
contains-assumption? x ◇                 Λ = throw-error "Assumption not found in context."
contains-assumption? x (Ξ ,,ᵛ μ ∣ y ∈ T) Λ = avar <$> contains-assumption? x Ξ Λ
contains-assumption? {n = m} x (_,,ᵇ_∣_∈_ {n = n} Ξ μ y φ) Λ with x Str.≟ y
... | yes refl = do
  refl ← n ≟mode m
  return azero
... | no _     = asuc <$> contains-assumption? x Ξ Λ
contains-assumption? x (Ξ ,lock⟨ μ ⟩)    Λ = alock <$> contains-assumption? x Ξ (lock⟨ μ ⟩, Λ)


⟦_⟧pctx : ProofCtx m → SemCtx ⟦ m ⟧mode
to-ctx-subst : (Ξ : ProofCtx m) → ⟦ Ξ ⟧pctx M.⇒ ⟦ to-ctx Ξ ⟧ctx

⟦ ◇ ⟧pctx = M.◇
⟦ Ξ ,,ᵛ μ ∣ _ ∈ T ⟧pctx = ⟦ Ξ ⟧pctx M.,, DRA.⟨ ⟦ μ ⟧mod ∣ ⟦ T ⟧ty ⟩
⟦ Ξ ,,ᵇ μ ∣ _ ∈ φ ⟧pctx = ⟦ Ξ ⟧pctx M.,, (DRA.⟨ ⟦ μ ⟧mod ∣ ⟦ φ ⟧bprop ⟩ M.[ to-ctx-subst Ξ ])
⟦ Ξ ,lock⟨ μ ⟩ ⟧pctx = DRA.lock ⟦ μ ⟧mod ⟦ Ξ ⟧pctx

to-ctx-subst ◇ = M.id-subst M.◇
to-ctx-subst (Ξ ,,ᵛ μ ∣ _ ∈ T) = M.lift-cl-subst (ty-closed-natural ⟨ μ ∣ T ⟩) (to-ctx-subst Ξ)
to-ctx-subst (Ξ ,,ᵇ _ ∣ _ ∈ _) = to-ctx-subst Ξ M.⊚ M.π
to-ctx-subst (Ξ ,lock⟨ μ ⟩) = DRA.lock-fmap ⟦ μ ⟧mod (to-ctx-subst Ξ)


interp-assumption-helper :
  {Ξ : ProofCtx m} {Λ : LockTele m n}
  (a : Assumption x Ξ Λ) (α : TwoCell (as-mod a) (locksˡᵗ (as-lt a))) →
  SemTm (⟦ Ξ ⟧pctx DRA.,lock⟨ ⟦ locksˡᵗ Λ ⟧mod ⟩)
        ((⟦ lookup-assumption a α ⟧bprop M.[ M.to (,ˡᵗ-sound Λ) ]) M.[ lock-fmap ⟦ locksˡᵗ Λ ⟧mod (to-ctx-subst Ξ) ])
interp-assumption-helper (azero {μ = μ} {φ = φ} {Λ = Λ}) α =
  M.ι[ M.ty-subst-cong-ty _ (M.ty-subst-cong-ty _ (M.transᵗʸ (rename-bprop-sound φ _) (M.ty-subst-cong-subst (M.symˢ (ren-key-sound-cod Λ α)) _))) ] (
  M.ι[ M.ty-subst-cong-ty _ (M.ty-subst-cong-subst-2-1 _ (M.transˢ M.⊚-assoc (M.transˢ (M.⊚-congʳ (M.isoʳ (,ˡᵗ-sound Λ))) (M.id-subst-unitʳ _)))) ] (
  M.ι[ M.ty-subst-cong-subst-2-2 _ (DRA.key-subst-natural ⟦ α ⟧two-cell) ] (
  dra-elim ⟦ μ ⟧mod (M.ι⁻¹[ M.transᵗʸ (M.ty-subst-comp _ _ _) (dra-natural ⟦ μ ⟧mod _) ] M.ξ)
    M.[ DRA.key-subst ⟦ α ⟧two-cell ]')))
interp-assumption-helper (asuc {Λ = Λ} a) α =
  M.ι⁻¹[ M.ty-subst-cong-subst-2-1 _ (M.symˢ (DRA.lock-fmap-⊚ ⟦ locksˡᵗ Λ ⟧mod _ _)) ]
  ((interp-assumption-helper a α) M.[ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod M.π ]')
interp-assumption-helper (avar {Ξ = Ξ} {Λ = Λ} {ρ = ρ} {y = y} {T = T} a) α =
  M.ι[ M.ty-subst-cong-ty _ (M.ty-subst-cong-ty _ (rename-bprop-sound (lookup-assumption a α) _)) ] (
  M.ι[ M.ty-subst-cong-ty _ (M.ty-subst-cong-subst-2-2 _ (,ˡᵗ-sound-to-naturalʳ Λ πʳ)) ] (
  M.ι[ M.ty-subst-cong-subst-2-2 _ (M.ctx-fmap-cong-2-2 (ctx-functor ⟦ locksˡᵗ Λ ⟧mod) (
       M.transˢ (M.⊚-congˡ (ren-π-sound (to-ctx Ξ) y ρ T))
                (M.lift-cl-subst-π-commute (ty-closed-natural ⟨ ρ ∣ T ⟩)))) ] (
  (interp-assumption-helper a α)
    M.[ lock-fmap ⟦ locksˡᵗ Λ ⟧mod M.π ]')))
interp-assumption-helper (alock {ρ = ρ} {Λ = Λ} a) α =
  M.ι⁻¹[ M.ty-subst-cong-subst-2-0 _ (M.isoʳ (lock-iso (⟦ⓜ⟧-sound ρ (locksˡᵗ Λ)))) ] (
    (M.ι⁻¹[ M.ty-subst-cong-subst-2-2 _ (key-subst-natural (DRA.to (⟦ⓜ⟧-sound ρ (locksˡᵗ Λ)))) ] (
     M.ι[ M.ty-subst-cong-ty _ (M.ty-subst-comp _ _ _) ] (
     interp-assumption-helper a α)))
      M.[ M.to (lock-iso (⟦ⓜ⟧-sound ρ (locksˡᵗ Λ))) ]')

⟦_,_⟧assumption : {Ξ : ProofCtx m} (a : Assumption x Ξ ◇) (α : TwoCell (as-mod a) (locksˡᵗ (as-lt a))) →
                  SemTm ⟦ Ξ ⟧pctx (⟦ lookup-assumption a α ⟧bprop M.[ to-ctx-subst Ξ ])
⟦ a , α ⟧assumption = M.ι⁻¹[ M.ty-subst-cong-ty _ (M.ty-subst-id _) ] (interp-assumption-helper a α)
