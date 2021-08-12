--------------------------------------------------
-- Definition of standard streams in mode ★
--------------------------------------------------

module GuardedRecursion.Streams.Standard where

open import Data.Nat
open import Data.Unit hiding (_≤_)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Vec.Properties
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories
open import CwF-Structure
open import Modalities
open import Types.Functions
open import Types.Instances
open import GuardedRecursion.Streams.Guarded
open import GuardedRecursion.Modalities
open import Reflection.Tactic.Lambda
open import Reflection.Tactic.Naturality
open import Translation

private
  variable
    Γ : Ctx ★


--------------------------------------------------
-- Definition of Stream' & corresponding constructor and destructors

Stream' : ClosedType ★ → ClosedType ★
Stream' A = allnow-ty (GStream A)

module _ {A : ClosedType ★} {{_ : IsClosedNatural A}} where
  head' : Tm Γ (Stream' A ⇛ A)
  head' = lamι[ "s" ∈ Stream' A ] ι⁻¹[ eq-mod-closed allnow-timeless A ] allnow-tm (g-head $ unallnow-tm (varι "s"))

  tail' : Tm Γ (Stream' A ⇛ Stream' A)
  tail' = lamι[ "s" ∈ Stream' A ] ι⁻¹[ allnow-later'-ty (GStream A) ] allnow-tm (g-tail $ unallnow-tm (varι "s"))

  cons' : Tm Γ (A ⇛ Stream' A ⇛ Stream' A)
  cons' = lamι[ "x" ∈ A ]
            lamι[ "xs" ∈ Stream' A ]
              allnow-tm (g-cons $ unallnow-tm (ι[ eq-mod-closed allnow-timeless A ] varι "x")
                                $ unallnow-tm (ι[ allnow-later'-ty (GStream A) ] varι "xs"))


--------------------------------------------------
-- Definition of standard Agda streams (note that the standard library uses
-- sized types and we want to avoid any extension of standard Agda) & translation
-- of standard Sikkel streams to Agda streams.

record Stream {ℓ} (A : Set ℓ) : Set ℓ where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

take : ∀ {ℓ} {A : Set ℓ} (n : ℕ) → Stream A → Vec A n
take zero    s = []
take (suc n) s = head s ∷ take n (tail s)

take-first : ∀ {ℓ} {A : Set ℓ} {m n : ℕ} (m≤n : m ≤ n) (s : Stream A) →
             first-≤ m≤n (take n s) ≡ take m s
take-first z≤n       s = refl
take-first (s≤s m≤n) s = cong (head s ∷_) (take-first m≤n (tail s))

instance
  translate-stream : {A : ClosedType ★} {{_ : IsClosedNatural A}} {{_ : Translatable A}} → Translatable (Stream' A)
  translated-type {{translate-stream {A = A}}} = Stream (translate-type A)
  head (translate-term {{translate-stream}} s) = translate-term (head' $ s)
  tail (translate-term {{translate-stream}} s) = translate-term (tail' $ s)
  translate-back {{translate-stream {A = A}}} s = allnow-tm (MkTm (λ n _ → Data.Vec.map (λ a → now-timeless-ctx-intro {A = A} (translate-back a) ⟨ tt , tt ⟩')
                                                                                        (take (suc n) s))
                                                                  (λ { m≤n refl → nat (s≤s m≤n) s }))
    where
      open ≡-Reasoning
      nat : ∀ {m n} (m≤n : m ≤ n) (s' : Stream (translate-type A)) →
        Data.Vec.map (A ⟪ tt , refl ⟫_) (first-≤ m≤n (Data.Vec.map (λ a → now-timeless-ctx-intro {A = A} (translate-back a) ⟨ tt , tt ⟩') (take n s')))
          ≡ Data.Vec.map (λ a → now-timeless-ctx-intro {A = A} (translate-back a) ⟨ tt , tt ⟩') (take m s')
      nat {m}{n} m≤n s' = begin
          Data.Vec.map (A ⟪ tt , refl ⟫_) (first-≤ m≤n (Data.Vec.map (λ a → now-timeless-ctx-intro {A = A} (translate-back a) ⟨ tt , tt ⟩') (take n s')))
        ≡⟨ trans (map-cong (λ _ → ty-id A) _) (map-id _) ⟩
          first-≤ m≤n (Data.Vec.map (λ a → now-timeless-ctx-intro {A = A} (translate-back a) ⟨ tt , tt ⟩') (take n s'))
        ≡˘⟨ map-first-≤ ⟩
          Data.Vec.map (λ a → now-timeless-ctx-intro {A = A} (translate-back a) ⟨ tt , tt ⟩') (first-≤ m≤n (take n s'))
        ≡⟨ cong (Data.Vec.map _) (take-first m≤n s') ⟩
          Data.Vec.map (λ a → now-timeless-ctx-intro {A = A} (translate-back a) ⟨ tt , tt ⟩') (take m s') ∎
