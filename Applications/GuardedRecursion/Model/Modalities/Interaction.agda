--------------------------------------------------
-- Proofs about the interactions between the different
-- modalities for guarded recursion
--------------------------------------------------

module Applications.GuardedRecursion.Model.Modalities.Interaction where

open import Data.Nat
open import Data.Unit
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.DRA
open import Applications.GuardedRecursion.Model.Modalities.Later
open import Applications.GuardedRecursion.Model.Modalities.Constantly
open import Applications.GuardedRecursion.Model.Modalities.Forever
open OmegaLimit


--------------------------------------------------
-- Interaction between the forever and later modalities

frvⓓltr≤frv : TwoCell (forever ⓓ later) forever
func (transf-op (transf frvⓓltr≤frv) Γ) γ = γ
_⇒_.naturality (transf-op (transf frvⓓltr≤frv) Γ) = refl
eq (CtxNatTransf.naturality (transf frvⓓltr≤frv) σ) _ = refl

frv≤frvⓓltr : TwoCell forever (forever ⓓ later)
transf-op (transf frv≤frvⓓltr) _ = from-earlier _
CtxNatTransf.naturality (transf frv≤frvⓓltr) σ = from-earlier-natural _

forever-later : forever ⓓ later ≅ᵈ forever
from forever-later = frvⓓltr≤frv
to forever-later = frv≤frvⓓltr
eq (key-subst-eq (isoˡ forever-later) {Γ = Γ}) _ = ctx-id Γ
eq (key-subst-eq (isoʳ forever-later) {Γ = Γ}) _ = ctx-id Γ

forever-later^[_] : (n : ℕ) → forever ⓓ later^[ n ] ≅ᵈ forever
forever-later^[ zero  ] = 𝟙-unitʳ _
forever-later^[ suc n ] =
  transᵈ (symᵈ (ⓓ-assoc _ _ _)) (transᵈ (ⓓ-congˡ _ forever-later) forever-later^[ n ])

forever-later'-ty : {Γ : Ctx ★} (T : Ty (constantly-ctx Γ)) →
                    forever-ty (▻' T) ≅ᵗʸ forever-ty T
forever-later'-ty = eq-dra-tyˡ forever-later


--------------------------------------------------
-- Interaction between the forever and constantly modalities

frvⓓcst≤𝟙 : TwoCell (forever ⓓ constantly) 𝟙
func (transf-op (transf frvⓓcst≤𝟙) Γ) γ = γ
_⇒_.naturality (transf-op (transf frvⓓcst≤𝟙) Γ) {f = tt} = refl
eq (CtxNatTransf.naturality (transf frvⓓcst≤𝟙) σ) _ = refl

𝟙≤frvⓓcst : TwoCell 𝟙 (forever ⓓ constantly)
func (transf-op (transf 𝟙≤frvⓓcst) Γ) γ = γ
_⇒_.naturality (transf-op (transf 𝟙≤frvⓓcst) Γ) {f = tt} = refl
eq (CtxNatTransf.naturality (transf 𝟙≤frvⓓcst) σ) _ = refl

forever-constantly : forever ⓓ constantly ≅ᵈ 𝟙
from forever-constantly = frvⓓcst≤𝟙
to forever-constantly = 𝟙≤frvⓓcst
eq (key-subst-eq (isoˡ forever-constantly)) _ = refl
eq (key-subst-eq (isoʳ forever-constantly)) _ = refl

now-constantly-ctx-intro : {A : ClosedTy ★} → IsClosedNatural A → {Γ : Ctx ★} →
                           Tm Γ A → Tm (now (constantly-ctx Γ)) A
now-constantly-ctx-intro clA t = unconstantly-tm (unforever-tm (ι[ eq-dra-ty-closed forever-constantly clA ] t))

to-constantly-now-ctx : (Γ : Ctx ω) → (Γ ⇒ constantly-ctx (now Γ))
func (to-constantly-now-ctx Γ) = Γ ⟪ z≤n ⟫_
_⇒_.naturality (to-constantly-now-ctx Γ) = ctx-cong-2-2 Γ refl

to-constantly-now-ctx-natural : {Δ Γ : Ctx ω} (σ : Δ ⇒ Γ) →
    to-constantly-now-ctx Γ ⊚ σ ≅ˢ ctx-fmap (constantly-ctx-functor ⓕ now-functor) σ ⊚ to-constantly-now-ctx Δ
eq (to-constantly-now-ctx-natural σ) δ = _⇒_.naturality σ

constantly∘forever≤𝟙 : TwoCell (constantly ⓓ forever) 𝟙
transf-op (transf constantly∘forever≤𝟙) = to-constantly-now-ctx
CtxNatTransf.naturality (transf constantly∘forever≤𝟙) = to-constantly-now-ctx-natural

from-constantly-forever-ty : {Γ : Ctx ω} {T : Ty (constantly-ctx (now Γ))} →
                             Tm Γ (constantly-ty (forever-ty T)) → Tm Γ (T [ to-constantly-now-ctx Γ ])
from-constantly-forever-ty {Γ = Γ} t = unforever-tm (unconstantly-tm t) [ to-constantly-now-ctx Γ ]'
