--------------------------------------------------
-- Definition of semantic standard streams in base category ★
--------------------------------------------------

module Applications.GuardedRecursion.Model.Streams.Standard where

open import Data.Nat
open import Data.Unit
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.Vec.Properties
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Preliminaries
open import Model.BaseCategory
open import Model.CwF-Structure
open import Model.DRA
open import Model.Type.Function
open import Applications.GuardedRecursion.Model.Streams.Guarded
open import Applications.GuardedRecursion.Model.Modalities
open import Extraction

private
  variable
    Γ : Ctx ★


--------------------------------------------------
-- Definition of Stream'

Stream' : ClosedTy ★ → ClosedTy ★
Stream' A = forever-ty (GStream A)

stream-closed : {A : ClosedTy ★} → IsClosedNatural A → IsClosedNatural (Stream' A)
stream-closed clA = dra-closed forever (gstream-closed clA)


--------------------------------------------------
-- Instance of Extractable for standard streams

vecs-to-stream : {A : Set} → ((n : ℕ) → Vec A (suc n)) → Stream A
head (vecs-to-stream vs) = Vec.head (vs 0)
tail (vecs-to-stream vs) = vecs-to-stream (λ n → Vec.tail (vs (suc n)))

extract-stream : {A : ClosedTy ★} → IsClosedNatural A → Extractable A → Extractable (Stream' A)
translated-type (extract-stream clA exA) = Stream (translated-type exA)
extract-term (extract-stream {A} clA exA) s = vecs-to-stream (λ n → Vec.map (extract-term exA ∘ to-◇A-term) (unforever-tm s ⟨ n , tt ⟩'))
  where
    to-★-nowtmlss◇-term : A {now (constantly-ctx ◇)} ⟨ tt , tt ⟩ → Tm (now (constantly-ctx ◇)) A
    to-★-nowtmlss◇-term a ⟨ tt , tt ⟩' = a
    Tm.naturality (to-★-nowtmlss◇-term a) tt refl = ty-id A

    to-◇A-term : A {now (constantly-ctx ◇)} ⟨ tt , tt ⟩ → Tm ◇ A
    to-◇A-term = ι⁻¹[ closed-natural clA _ ]_ ∘ _[ key-subst (from forever-constantly) ]' ∘ to-★-nowtmlss◇-term
embed-term (extract-stream {A = A} clA exA) s = forever-tm (MkTm (λ n _ → Vec.map (λ a → now-constantly-ctx-intro clA (embed-term exA a) ⟨ tt , tt ⟩')
                                                                            (take (suc n) s))
                                                           (λ { m≤n refl → nat (s≤s m≤n) s }))
  where
    open ≡-Reasoning
    nat : ∀ {m n} (m≤n : m ≤ n) (s' : Stream (translated-type exA)) →
      Vec.map (A ⟪ tt , refl ⟫_) (first-≤ m≤n (Vec.map (λ a → now-constantly-ctx-intro clA (embed-term exA a) ⟨ tt , tt ⟩') (take n s')))
        ≡ Vec.map (λ a → now-constantly-ctx-intro clA (embed-term exA a) ⟨ tt , tt ⟩') (take m s')
    nat {m}{n} m≤n s' = begin
        Vec.map (A ⟪ tt , refl ⟫_) (first-≤ m≤n (Vec.map (λ a → now-constantly-ctx-intro clA (embed-term exA a) ⟨ tt , tt ⟩') (take n s')))
      ≡⟨ trans (map-cong (λ _ → ty-id A) _) (map-id _) ⟩
        first-≤ m≤n (Vec.map (λ a → now-constantly-ctx-intro clA (embed-term exA a) ⟨ tt , tt ⟩') (take n s'))
      ≡⟨ map-first-≤ ⟨
        Vec.map (λ a → now-constantly-ctx-intro clA (embed-term exA a) ⟨ tt , tt ⟩') (first-≤ m≤n (take n s'))
      ≡⟨ cong (Vec.map _) (take-first m≤n s') ⟩
        Vec.map (λ a → now-constantly-ctx-intro clA (embed-term exA a) ⟨ tt , tt ⟩') (take m s') ∎
