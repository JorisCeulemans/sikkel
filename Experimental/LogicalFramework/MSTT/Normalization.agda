open import Experimental.LogicalFramework.MSTT.ModeTheory

module Experimental.LogicalFramework.MSTT.Normalization (ℳ : ModeTheory) where

open import Data.Nat
open import Data.Maybe
open import Function

open ModeTheory ℳ

open import Experimental.LogicalFramework.MSTT.Normalization.Helpers
open import Experimental.LogicalFramework.MSTT.Syntax.Nameless ℳ

private variable
  m n o : Mode
  μ ρ : Modality m n
  T S : Ty m
  Γ Δ : Ctx m


data NF : Ctx m → Ty m → Set
data NE : Ctx m → Ty m → Set

data NF where
  neutral : NE Γ T → NF Γ T
  mod⟨_⟩_ : (μ : Modality n m) → NF (Γ ,lock⟨ μ ⟩) T → NF Γ ⟨ μ ∣ T ⟩
  lam[_∣_]_ : (μ : Modality n m) (T : Ty n) (b : Tm (Γ ,, μ ∣ _ ∈ T) S) → NF Γ (⟨ μ ∣ T ⟩⇛ S)
  zero : NF Γ Nat'
  suc : NF Γ Nat' → NF Γ Nat'
  true false : NF Γ Bool'
  pair : NF Γ T → NF Γ S → NF Γ (T ⊠ S)

data NE where
  var' : {μ κ : Modality m n} (v : Var _ μ T κ Γ) (α : TwoCell μ κ) → NE Γ T
  mod-elim : (ρ : Modality o m) (μ : Modality n o) →
             (t : NE (Γ ,lock⟨ ρ ⟩) ⟨ μ ∣ T ⟩) →
             (s : Tm (Γ ,, ρ ⓜ μ ∣ _ ∈ T) S) →
             NE Γ S
  _∙_ : {μ : Modality m n} (f : NE Γ (⟨ μ ∣ T ⟩⇛ S)) (t : NF (Γ ,lock⟨ μ ⟩) T) → NE Γ S
  nat-rec : {A : Ty m}
             (z : NF Γ A)→
             (s : Tm Γ (A ⇛ A)) →
             (n : NE Γ Nat') →
             NE Γ A
  if : {A : Ty m} (b : NE Γ Bool') (t f : NF Γ A) → NE Γ A
  fst : (p : NE Γ (T ⊠ S)) → NE Γ T
  snd : (p : NE Γ (T ⊠ S)) → NE Γ S

nf-to-tm : NF Γ T → Tm Γ T
ne-to-tm : NE Γ T → Tm Γ T

nf-to-tm (neutral ne) = ne-to-tm ne
nf-to-tm (mod⟨ μ ⟩ nf) = mod⟨ μ ⟩ nf-to-tm nf
nf-to-tm (lam[ μ ∣ T ] b) = lam[ μ ∣ _ ∈ T ] b
nf-to-tm zero = zero
nf-to-tm (suc nf) = suc (nf-to-tm nf)
nf-to-tm true = true
nf-to-tm false = false
nf-to-tm (pair nf1 nf2) = pair (nf-to-tm nf1) (nf-to-tm nf2)

ne-to-tm (var' v α) = var' _ {v} α
ne-to-tm (mod-elim ρ μ ne s) = mod-elim ρ μ _ (ne-to-tm ne) s
ne-to-tm (ne ∙ nf) = ne-to-tm ne ∙ nf-to-tm nf
ne-to-tm (nat-rec nfz s ne) = nat-rec (nf-to-tm nfz) s (ne-to-tm ne)
ne-to-tm (if ne nft nff) = if (ne-to-tm ne) (nf-to-tm nft) (nf-to-tm nff)
ne-to-tm (fst ne) = fst (ne-to-tm ne)
ne-to-tm (snd ne) = snd (ne-to-tm ne)

normalize : ℕ → Tm Γ T → Maybe (NF Γ T)
normalize zero t = nothing -- not enough fuel left
normalize (suc n) (var' _ {v} α) = just $ neutral (var' v α)
normalize (suc n) (mod⟨ μ ⟩ t) = mod⟨ μ ⟩_ <$> normalize (suc n) t
normalize (suc n) (mod-elim {T = T} {S} ρ μ _ t s) = do
  nft ← normalize (suc n) t
  normalize-mod-elim nft s
  where
    normalize-mod-elim : NF (Γ ,lock⟨ ρ ⟩) ⟨ μ ∣ T ⟩ → Tm (Γ ,, ρ ⓜ μ ∣ _ ∈ T) S → Maybe (NF Γ S)
    normalize-mod-elim (neutral net)   s = just $ neutral (mod-elim ρ μ net s)
    normalize-mod-elim (mod⟨ .μ ⟩ nft) s = normalize n (s [ fuselocks-tm (nf-to-tm nft) / _ ]tm)
normalize (suc n) (lam[ μ ∣ _ ∈ T ] b) = just $ lam[ μ ∣ T ] b -- At the moment, normalization does not proceed in bodies of lambdas.
normalize (suc n) (f ∙ t) = do
  nff ← normalize (suc n) f
  nft ← normalize (suc n) t
  normalize-app nff nft
  where
    normalize-app : NF Γ (⟨ μ ∣ T ⟩⇛ S) → NF (Γ ,lock⟨ μ ⟩) T → Maybe (NF Γ S)
    normalize-app (neutral nef)    nft = just $ neutral (nef ∙ nft)
    normalize-app (lam[ _ ∣ _ ] b) nft = normalize n (b [ nf-to-tm nft / _ ]tm)
normalize (suc n) zero = just zero
normalize (suc n) (suc t) = suc <$> normalize (suc n) t
normalize m@(suc n) (nat-rec {Γ = Γ} {A = A} z s t) = do
  nft ← normalize (suc n) t
  normalize-nat-rec (suc n) nft
  module NormalizeNatElim where
    -- Extra argument of type ℕ is needed to pass termination checking.
    normalize-nat-rec : ℕ → NF Γ Nat' → Maybe (NF Γ A)
    normalize-nat-rec n       (neutral ne) = (λ nfz → neutral (nat-rec nfz s ne)) <$> normalize n z
    normalize-nat-rec n       zero         = normalize n z
    normalize-nat-rec zero    (suc nf)     = nothing -- not enough fuel
    normalize-nat-rec (suc n) (suc nf)     = normalize n (s ∙¹ nat-rec z s (nf-to-tm nf))
normalize (suc n) true = just true
normalize (suc n) false = just false
normalize (suc n) (if b t f) = normalize-if <$> normalize (suc n) b <*> normalize (suc n) t <*> normalize (suc n) f
  module NormalizeIf where
    normalize-if : NF Γ Bool' → NF Γ T → NF Γ T → NF Γ T
    normalize-if (neutral ne) nt nf = neutral (if ne nt nf)
    normalize-if true         nt nf = nt
    normalize-if false        nt nf = nf
normalize (suc n) (pair t s) = pair <$> normalize (suc n) t <*> normalize (suc n) s
normalize (suc n) (fst p) = normalize-fst <$> normalize (suc n) p
  module NormalizeFst where
    normalize-fst : NF Γ (T ⊠ S) → NF Γ T
    normalize-fst (neutral nep) = neutral (fst nep)
    normalize-fst (pair nft _)  = nft
normalize (suc n) (snd p) = normalize-snd <$> normalize (suc n) p
  module NormalizeSnd where
    normalize-snd : NF Γ (T ⊠ S) → NF Γ S
    normalize-snd (neutral nep) = neutral (snd nep)
    normalize-snd (pair _ nfs)  = nfs

private
  plus : Tm Γ (Nat' ⇛ Nat' ⇛ Nat')
  plus = lam[ _ ∈ Nat' ] nat-rec (lam[ _ ∈ Nat' ] var' _ {vzero} id-cell)
                                 (lam[ _ ∈ Nat' ⇛ Nat' ] (lam[ _ ∈ Nat' ] suc (var' _ {vsuc vzero} id-cell ∙¹ var' _ {vzero} id-cell)))
                                 (var' _ {vzero} id-cell)

  test-nat : Tm Γ Nat'
  test-nat = plus ∙ suc zero ∙ suc (suc zero)

  open import Relation.Binary.PropositionalEquality
  test : ∀ {m} → normalize {m} {◇} 1000000000000 test-nat ≡ just (suc (suc (suc zero)))
  test = refl
