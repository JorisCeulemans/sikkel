--------------------------------------------------
-- Definition of standard streams in mode ★
--------------------------------------------------

module Applications.GuardedRecursion.Model.Streams.Standard where

open import Data.Nat
open import Data.Unit hiding (_≤_)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.Vec.Properties
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.Modality
open import Model.Type.Function
open import Applications.GuardedRecursion.Model.Streams.Guarded
open import Applications.GuardedRecursion.Model.Modalities
open import Extraction

private
  variable
    Γ : Ctx ★


--------------------------------------------------
-- Definition of Stream'

Stream' : ClosedType ★ → ClosedType ★
Stream' A = allnow-ty (GStream A)


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


--------------------------------------------------
-- Instance of Extractable for standard streams.

vecs-to-stream : ∀ {ℓ} {A : Set ℓ} → (∀ n → Vec A (suc n)) → Stream A
head (vecs-to-stream f) = Vec.head (f 0)
tail (vecs-to-stream f) = vecs-to-stream (λ n → Vec.tail (f (suc n)))

instance
  extract-stream : {A : ClosedType ★} {{_ : IsClosedNatural A}} {{_ : Extractable A}} → Extractable (Stream' A)
  translated-type {{extract-stream {A = A}}} = Stream (translate-type A)
  extract-term {{extract-stream {A = A}}} s = vecs-to-stream (λ n → Vec.map (extract-term {A} ∘ to-◇A-term) (unallnow-tm s ⟨ n , tt ⟩'))
    where
      to-★-nowtmlss◇-term : A {now (timeless-ctx ◇)} ⟨ tt , tt ⟩ → Tm (now (timeless-ctx ◇)) A
      to-★-nowtmlss◇-term a ⟨ tt , tt ⟩' = a
      Tm.naturality (to-★-nowtmlss◇-term a) tt refl = ty-id A

      to-◇A-term : A {now (timeless-ctx ◇)} ⟨ tt , tt ⟩ → Tm ◇ A
      to-◇A-term = ι⁻¹[ closed-natural {U = A} _ ]_ ∘ _[ to (now-timeless-ctx ◇) ]' ∘ to-★-nowtmlss◇-term
  embed-term {{extract-stream {A = A}}} s = allnow-tm (MkTm (λ n _ → Vec.map (λ a → now-timeless-ctx-intro {A = A} (embed-term a) ⟨ tt , tt ⟩')
                                                                             (take (suc n) s))
                                                            (λ { m≤n refl → nat (s≤s m≤n) s }))
    where
      open ≡-Reasoning
      nat : ∀ {m n} (m≤n : m ≤ n) (s' : Stream (translate-type A)) →
        Vec.map (A ⟪ tt , refl ⟫_) (first-≤ m≤n (Vec.map (λ a → now-timeless-ctx-intro {A = A} (embed-term a) ⟨ tt , tt ⟩') (take n s')))
          ≡ Vec.map (λ a → now-timeless-ctx-intro {A = A} (embed-term a) ⟨ tt , tt ⟩') (take m s')
      nat {m}{n} m≤n s' = begin
          Vec.map (A ⟪ tt , refl ⟫_) (first-≤ m≤n (Vec.map (λ a → now-timeless-ctx-intro {A = A} (embed-term a) ⟨ tt , tt ⟩') (take n s')))
        ≡⟨ trans (map-cong (λ _ → ty-id A) _) (map-id _) ⟩
          first-≤ m≤n (Vec.map (λ a → now-timeless-ctx-intro {A = A} (embed-term a) ⟨ tt , tt ⟩') (take n s'))
        ≡˘⟨ map-first-≤ ⟩
          Vec.map (λ a → now-timeless-ctx-intro {A = A} (embed-term a) ⟨ tt , tt ⟩') (first-≤ m≤n (take n s'))
        ≡⟨ cong (Vec.map _) (take-first m≤n s') ⟩
          Vec.map (λ a → now-timeless-ctx-intro {A = A} (embed-term a) ⟨ tt , tt ⟩') (take m s') ∎
