open import Experimental.LogicalFramework.MSTT.Parameter

module Experimental.LogicalFramework.Proof.Context (𝒫 : MSTT-Parameter) where

open import Data.String as Str
open import Function using (id)
import Relation.Binary.PropositionalEquality as Ag
open import Relation.Nullary

open import Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import Model.DRA as DRA hiding (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; TwoCell)

open MSTT-Parameter 𝒫

open import Experimental.LogicalFramework.MSTT 𝒫
open import Experimental.LogicalFramework.bProp 𝒫
open import Experimental.LogicalFramework.Proof.CheckingMonad
open import Experimental.LogicalFramework.Proof.Equality 𝒫
open import Experimental.LogicalFramework.Postulates 𝒫

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  Γ Δ : Ctx m
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
--  names. The (proof-relevant) predicate Assumption x μ κ Ξ expresses
--  that an assumption with name x is present in proof context Ξ under
--  modality μ and with κ the composition of all locks to the right of
--  x. Note that we do not keep track of the proposition in the Assumption
--  type (in contrast to the type of variables in MSTT).
data Assumption (x : String) (μ : Modality n o) : Modality m o → ProofCtx m → Set where
  azero : Assumption x μ 𝟙 (Ξ ,,ᵇ μ ∣ x ∈ φ)
  asuc  : Assumption x μ κ Ξ → Assumption x μ κ (Ξ ,,ᵇ ρ ∣ y ∈ ψ)
  skip-var : Assumption x μ κ Ξ → Assumption x μ κ (Ξ ,,ᵛ ρ ∣ y ∈ T)
  skip-lock : (ρ : Modality m p) → Assumption x μ κ Ξ → Assumption x μ (κ ⓜ ρ) (Ξ ,lock⟨ ρ ⟩)

lookup-assumption' : Assumption x μ κ Ξ → (ρ : Modality _ _) →
                     TwoCell μ (κ ⓜ ρ) → bProp ((to-ctx Ξ) ,lock⟨ ρ ⟩)
lookup-assumption' (azero {φ = φ}) ρ α = φ [ key-sub (◇ ,lock⟨ ρ ⟩) (◇ ,lock⟨ _ ⟩) α ]bprop
lookup-assumption' (asuc a) ρ α = lookup-assumption' a ρ α
lookup-assumption' (skip-var a) ρ α = (lookup-assumption' a ρ α) [ π ,slock⟨ ρ ⟩ ]bprop
lookup-assumption' (skip-lock {κ = κ} ρ' a) ρ α = unfuselocks-bprop (lookup-assumption' a (ρ' ⓜ ρ) (transp-cellʳ (mod-assoc κ) α))

lookup-assumption : Assumption x μ κ Ξ → TwoCell μ κ → bProp (to-ctx Ξ)
lookup-assumption a α = unlock𝟙-bprop (lookup-assumption' a 𝟙 (transp-cellʳ (Ag.sym mod-unitʳ) α))

record ContainsAssumption (x : String) (μ : Modality n o) (Ξ : ProofCtx m) : Set where
  constructor contains-assumption
  field
    locks : Modality m o
    as : Assumption x μ locks Ξ

map-contains : {m m' : Mode} {x : String} {μ : Modality n o}
               {Ξ : ProofCtx m} {Ξ' : ProofCtx m'}
               (F : Modality m o → Modality m' o) →
               (∀ {κ} → Assumption x μ κ Ξ → Assumption x μ (F κ) Ξ') →
               ContainsAssumption x μ Ξ → ContainsAssumption x μ Ξ'
map-contains F G (contains-assumption locks as) = contains-assumption (F locks) (G as)

contains-assumption? : (x : String) (μ : Modality n o) (Ξ : ProofCtx m) →
                       PCM (ContainsAssumption x μ Ξ)
contains-assumption? x μ ◇ = throw-error "Assumption not found in context."
contains-assumption? x μ (Ξ ,,ᵛ ρ ∣ y ∈ T) = map-contains id skip-var <$> contains-assumption? x μ Ξ
contains-assumption? x μ (Ξ ,,ᵇ ρ ∣ y ∈ φ) with x Str.≟ y
contains-assumption? {n = n} {o} {m} x μ (_,,ᵇ_∣_∈_ {n = n'} Ξ ρ .x φ) | yes refl = do
  refl ← m ≟mode o
  refl ← n ≟mode n'
  refl ← μ ≟mod ρ
  return (contains-assumption 𝟙 azero)
contains-assumption? x μ (Ξ ,,ᵇ ρ ∣ y ∈ φ) | no ¬x=y = map-contains id asuc <$> contains-assumption? x μ Ξ
contains-assumption? x μ (Ξ ,lock⟨ ρ ⟩) = map-contains (_ⓜ ρ) (skip-lock ρ) <$> contains-assumption? x μ Ξ


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


interp-assumption-helper : (a : Assumption x μ κ Ξ) (ρ : Modality _ _) (α : TwoCell μ (κ ⓜ ρ)) →
                           SemTm ⟦ Ξ ,lock⟨ ρ ⟩ ⟧pctx (⟦ lookup-assumption' a ρ α ⟧bprop M.[ to-ctx-subst (Ξ ,lock⟨ ρ ⟩) ])
interp-assumption-helper {μ = μ} (azero {Ξ = Ξ} {φ = φ}) ρ α =
  M.ι⁻¹[ M.ty-subst-cong-ty _ (M.transᵗʸ (M.ty-subst-cong-subst (key-sub-sound α {to-ctx Ξ}) _) (bprop-sub-sound φ _)) ] (
  M.ι[ M.ty-subst-cong-subst-2-2 _ (DRA.key-subst-natural ⟦ α ⟧two-cell) ] (
  dra-elim ⟦ μ ⟧mod (M.ι⁻¹[ M.transᵗʸ (M.ty-subst-comp _ _ _) (dra-natural ⟦ μ ⟧mod _) ] M.ξ)
  M.[ DRA.key-subst ⟦ α ⟧two-cell ]'))
interp-assumption-helper (asuc a) ρ α =
  M.ι⁻¹[ M.ty-subst-cong-subst-2-1 _ (M.symˢ (DRA.lock-fmap-⊚ ⟦ ρ ⟧mod _ _)) ] (
  interp-assumption-helper a ρ α
  M.[ DRA.lock-fmap ⟦ ρ ⟧mod M.π ]')
interp-assumption-helper (skip-var {Ξ = Ξ} {ρ = ρ'} {T = T} a) ρ α =
  let x = _
  in
  M.ι⁻¹[ M.ty-subst-cong-ty _ (M.transᵗʸ (M.ty-subst-cong-subst (M.symˢ (sub-lock-sound (π {Γ = to-ctx Ξ} {μ = ρ'} {x} {T}) ρ)) _)
                                         (bprop-sub-sound (lookup-assumption' a ρ α) ((π {x = x}) ,slock⟨ ρ ⟩))) ] (
  M.ι[ M.ty-subst-cong-subst-2-2 _ (M.ctx-fmap-cong-2-2 (DRA.ctx-functor ⟦ ρ ⟧mod) (M.transˢ (M.⊚-congˡ (sub-π-sound (to-ctx Ξ) x ρ' T))
                                                                                             (M.lift-cl-subst-π-commute (ty-closed-natural ⟨ ρ' ∣ T ⟩)))) ] (
  interp-assumption-helper a ρ α M.[ DRA.lock-fmap ⟦ ρ ⟧mod M.π ]'))
interp-assumption-helper (skip-lock {κ = κ} ρ' a) ρ α =
  M.ι[ M.ty-subst-cong-ty _ (unfuselocks-bprop-sound {μ = ρ'} (lookup-assumption' a (ρ' ⓜ ρ) (transp-cellʳ (mod-assoc κ) α))) ] (
  M.ι[ M.ty-subst-cong-subst-2-2 _ (eq-lock-natural-to (⟦ⓜ⟧-sound ρ' ρ) _) ] (
  interp-assumption-helper a (ρ' ⓜ ρ) (transp-cellʳ (mod-assoc κ) α)
  M.[ _ ]'))

⟦_,_⟧assumption : (a : Assumption x μ κ Ξ) (α : TwoCell μ κ) → SemTm ⟦ Ξ ⟧pctx (⟦ lookup-assumption a α ⟧bprop M.[ to-ctx-subst Ξ ])
⟦ a , α ⟧assumption = M.ι[ M.ty-subst-cong-ty _ (unlock𝟙-bprop-sound (lookup-assumption' a 𝟙 _)) ] interp-assumption-helper a 𝟙 _
