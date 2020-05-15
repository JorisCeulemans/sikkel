module Types.Functions where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Function hiding (_⟨_⟩_; _↣_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension


--------------------------------------------------
-- (Non-dependent) function types
--------------------------------------------------

record PresheafFunc {ℓ} {Γ : Ctx ℓ} (T S : Ty Γ) (n : ℕ) (γ : Γ ⟨ n ⟩) : Set ℓ where
  constructor MkFunc
  field
    _$⟨_,_⟩_ : ∀ {m} (m≤n : m ≤ n) {γ' : Γ ⟨ m ⟩} (eq : Γ ⟪ m≤n ⟫ γ ≡ γ') →
               T ⟨ m , γ' ⟩ → S ⟨ m , γ' ⟩
    naturality : ∀ {k m} {k≤m : k ≤ m} {m≤n : m ≤ n} {γm : Γ ⟨ m ⟩} {γk : Γ ⟨ k ⟩} →
                 (eq-nm : Γ ⟪ m≤n ⟫ γ ≡ γm) (eq-mk : Γ ⟪ k≤m ⟫ γm ≡ γk) (t : T ⟨ m , γm ⟩)→
                 _$⟨_,_⟩_ (≤-trans k≤m m≤n) (strong-rel-comp Γ eq-nm eq-mk) (T ⟪ k≤m , eq-mk ⟫ t) ≡
                   S ⟪ k≤m , eq-mk ⟫ (_$⟨_,_⟩_ m≤n eq-nm t)
  infix 13 _$⟨_,_⟩_
open PresheafFunc public

pshfun-dimap : {Γ : Ctx ℓ} {T T' S S' : Ty Γ} → (T' ↣ T) → (S ↣ S') →
               (n : ℕ) (γ : Γ ⟨ n ⟩) →
               PresheafFunc T S n γ → PresheafFunc T' S' n γ
_$⟨_,_⟩_ (pshfun-dimap η φ n γ f) m≤n eγ t' = func φ (f $⟨ m≤n , eγ ⟩ func η t')
naturality (pshfun-dimap {T = T}{T'}{S}{S'} η φ n γ f) eq-nm eq-mk t' =
  begin
    func φ (f $⟨ ≤-trans _ _ , _ ⟩ func η (T' ⟪ _ , eq-mk ⟫ t'))
  ≡˘⟨ cong (func φ ∘ f $⟨ ≤-trans _ _ , _ ⟩_) (naturality η t') ⟩
    func φ (f $⟨ ≤-trans _ _ , _ ⟩ (T ⟪ _ , eq-mk ⟫ func η t'))
  ≡⟨ cong (func φ) (naturality f eq-nm eq-mk (func η t')) ⟩
    func φ (S ⟪ _ , eq-mk ⟫ (f $⟨ _ , eq-nm ⟩ func η t'))
  ≡˘⟨ naturality φ _ ⟩
    S' ⟪ _ , eq-mk ⟫ func φ (f $⟨ _ , eq-nm ⟩ func η t') ∎
  where open ≡-Reasoning

-- Here we make again use of uip by pattern matching on both equality proofs.
$-cong : {Γ : Ctx ℓ} {T S : Ty Γ} {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} (f : PresheafFunc T S n γn)
         {m≤n m≤n' : m ≤ n} (e-ineq : m≤n ≡ m≤n')
         (eγ : Γ ⟪ m≤n ⟫ γn ≡ γm) (eγ' : Γ ⟪ m≤n' ⟫ γn ≡ γm)
         {t : T ⟨ m , γm ⟩} →
         f $⟨ m≤n , eγ ⟩ t ≡ f $⟨ m≤n' , eγ' ⟩ t
$-cong f refl refl refl = refl

to-pshfun-eq : {Γ : Ctx ℓ} {T S : Ty Γ} {n : ℕ} {γ : Γ ⟨ n ⟩} {f g : PresheafFunc T S n γ} →
               (∀ {m} (m≤n : m ≤ n) {γ'} (eq : Γ ⟪ m≤n ⟫ γ ≡ γ') t →
                   f $⟨ m≤n , eq ⟩ t ≡ g $⟨ m≤n , eq ⟩ t) →
               f ≡ g
to-pshfun-eq e = cong₂-d MkFunc
  (funextI (funext (λ m≤n → funextI (funext λ eq → funext λ t → e m≤n eq t))))
  (funextI (funextI (funextI (funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _)))))))

lower-presheaffunc : ∀ {m n} {Γ : Ctx ℓ} {T S : Ty Γ} (m≤n : m ≤ n)
                     {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} (eq : Γ ⟪ m≤n ⟫ γn ≡ γm) →
                     PresheafFunc T S n γn → PresheafFunc T S m γm
lower-presheaffunc {m = m}{n}{Γ}{T}{S} m≤n {γn}{γm} eq-nm f = MkFunc g g-nat
  where
    g : ∀ {k} (k≤m : k ≤ m) {γk} (eq-mk : Γ ⟪ k≤m ⟫ γm ≡ γk) →
        T ⟨ k , γk ⟩ → S ⟨ k , γk ⟩
    g k≤m eq-mk = f $⟨ ≤-trans k≤m m≤n , strong-rel-comp Γ eq-nm eq-mk ⟩_
    open ≡-Reasoning
    g-nat : ∀ {k l} {k≤l : k ≤ l} {l≤m : l ≤ m} {γl : Γ ⟨ l ⟩} {γk : Γ ⟨ k ⟩}
            (eq-ml : Γ ⟪ l≤m ⟫ γm ≡ γl) (eq-lk : Γ ⟪ k≤l ⟫ γl ≡ γk) → _
    g-nat {k≤l = k≤l}{l≤m} eq-ml eq-lk t =
      f $⟨ ≤-trans (≤-trans k≤l l≤m) m≤n , strong-rel-comp Γ eq-nm (strong-rel-comp Γ eq-ml eq-lk) ⟩ (T ⟪ k≤l , eq-lk ⟫ t)
        ≡⟨ $-cong f (≤-irrelevant _ _) _ _ ⟩
      f $⟨ ≤-trans k≤l (≤-trans l≤m m≤n) , strong-rel-comp Γ (strong-rel-comp Γ eq-nm eq-ml) eq-lk ⟩ (T ⟪ k≤l , eq-lk ⟫ t)
        ≡⟨ naturality f (strong-rel-comp Γ eq-nm eq-ml) eq-lk t ⟩
      S ⟪ k≤l , eq-lk ⟫ (f $⟨ ≤-trans l≤m m≤n , strong-rel-comp Γ eq-nm eq-ml ⟩ t) ∎

_⇛_ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ → Ty Γ
type (_⇛_ {Γ = Γ} T S) n γ = PresheafFunc T S n γ
morph (T ⇛ S) = lower-presheaffunc
morph-id (_⇛_ {Γ = Γ} T S) f = to-pshfun-eq (λ m≤n eγ t → $-cong f (≤-irrelevant _ _) _ eγ)
morph-comp (_⇛_ {Γ = Γ} T S) l≤m m≤n eq-nm eq-ml f = to-pshfun-eq (λ k≤l eq-lk t → $-cong f (≤-irrelevant _ _) _ _)

⇛-dimap : {Γ : Ctx ℓ} {T T' S S' : Ty Γ} → (T' ↣ T) → (S ↣ S') → (T ⇛ S ↣ T' ⇛ S')
func (⇛-dimap η φ) = pshfun-dimap η φ _ _
naturality (⇛-dimap η φ) f = to-pshfun-eq λ _ _ _ → refl

⇛-cong : {Γ : Ctx ℓ} {T T' S S' : Ty Γ} → T ≅ᵗʸ T' → S ≅ᵗʸ S' → T ⇛ S ≅ᵗʸ T' ⇛ S'
from (⇛-cong T=T' S=S') = ⇛-dimap (to T=T') (from S=S')
to (⇛-cong T=T' S=S') = ⇛-dimap (from T=T') (to S=S')
eq (isoˡ (⇛-cong T=T' S=S')) f = to-pshfun-eq (λ m≤n eγ t →
  begin
    func (to S=S') (func (from S=S') (f $⟨ m≤n , eγ ⟩ func (to T=T') (func (from T=T') t)))
  ≡⟨ eq (isoˡ S=S') _ ⟩
    f $⟨ m≤n , eγ ⟩ func (to T=T') (func (from T=T') t)
  ≡⟨ cong (f $⟨ m≤n , eγ ⟩_) (eq (isoˡ T=T') t) ⟩
    f $⟨ m≤n , eγ ⟩ t ∎)
  where open ≡-Reasoning
eq (isoʳ (⇛-cong T=T' S=S')) f = to-pshfun-eq (λ m≤n eγ t' →
  begin
    func (from S=S') (func (to S=S') (f $⟨ m≤n , eγ ⟩ func (from T=T') (func (to T=T') t')))
  ≡⟨ eq (isoʳ S=S') _ ⟩
    f $⟨ m≤n , eγ ⟩ func (from T=T') (func (to T=T') t')
  ≡⟨ cong (f $⟨ m≤n , eγ ⟩_) (eq (isoʳ T=T') t') ⟩
    f $⟨ m≤n , eγ ⟩ t' ∎)
  where open ≡-Reasoning

lam : {Γ : Ctx ℓ} (T : Ty Γ) {S : Ty Γ} → Tm (Γ ,, T) (S [ π ]) → Tm Γ (T ⇛ S)
term (lam T {S} b) n γ = MkFunc (λ m≤n {γ'} eγ t → b ⟨ _ , [ γ' , t ] ⟩')
                                (λ {k}{m}{k≤m}{_}{γm}{γk} eq-nm eq-mk t →
  b ⟨ k , [ γk , T ⟪ k≤m , eq-mk ⟫ t ] ⟩'
    ≡⟨ sym (naturality b k≤m (to-Σ-eq eq-mk (morph-subst T refl eq-mk t))) ⟩
  S ⟪ k≤m , from-Σ-eq1 (to-Σ-eq eq-mk _) ⟫ b ⟨ m , [ γm , t ] ⟩'
    ≡⟨ cong (λ x → S ⟪ k≤m , x ⟫ _) (from-to-Σ-eq1 (morph-subst T refl eq-mk t)) ⟩
  S ⟪ k≤m , eq-mk ⟫ b ⟨ m , [ γm , t ] ⟩' ∎)
  where open ≡-Reasoning
naturality (lam T b) m≤n eq-nm = to-pshfun-eq λ k≤m eq-mk t → refl

_€⟨_,_⟩_ : {Γ : Ctx ℓ} {T S : Ty Γ} → Tm Γ (T ⇛ S) → (n : ℕ) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩ → S ⟨ n , γ ⟩
_€⟨_,_⟩_ {Γ = Γ} f n γ t = f ⟨ n , γ ⟩' $⟨ ≤-refl , rel-id Γ γ ⟩ t

€-natural : {Γ : Ctx ℓ} {T S : Ty Γ} (f : Tm Γ (T ⇛ S)) (m≤n : m ≤ n)
            {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} (eγ : Γ ⟪ m≤n ⟫ γn ≡ γm)
            (t : T ⟨ n , γn ⟩) →
            S ⟪ m≤n , eγ ⟫ (f €⟨ n , γn ⟩ t) ≡ f €⟨ m , γm ⟩ (T ⟪ m≤n , eγ ⟫ t)
€-natural {Γ = Γ}{T}{S} f m≤n {γn}{γm} eγ t =
  S ⟪ m≤n , eγ ⟫ (f ⟨ _ , γn ⟩' $⟨ ≤-refl , rel-id Γ γn ⟩ t)
    ≡⟨ sym (naturality (f ⟨ _ , γn ⟩') (rel-id Γ γn) eγ t) ⟩
  f ⟨ _ , γn ⟩' $⟨ ≤-trans m≤n ≤-refl , strong-rel-comp Γ (rel-id Γ γn) eγ ⟩ (T ⟪ m≤n , eγ ⟫ t)
    ≡⟨ $-cong (f ⟨ _ , γn ⟩') (≤-irrelevant _ _) _ _ ⟩
  f ⟨ _ , γn ⟩' $⟨ ≤-trans ≤-refl m≤n , strong-rel-comp Γ eγ (rel-id Γ γm) ⟩ (T ⟪ m≤n , eγ ⟫ t)
    ≡⟨ cong (λ x → x $⟨ _ , _ ⟩ _) (naturality f m≤n eγ) ⟩
  f ⟨ _ , γm ⟩' $⟨ ≤-refl , rel-id Γ γm ⟩ (T ⟪ m≤n , eγ ⟫ t) ∎
  where open ≡-Reasoning

app : {Γ : Ctx ℓ} {T S : Ty Γ} → Tm Γ (T ⇛ S) → Tm Γ T → Tm Γ S
term (app f t) n γ = f €⟨ n , γ ⟩ (t ⟨ n , γ ⟩')
naturality (app {Γ = Γ}{T}{S} f t) m≤n {γn}{γm} eγ =
  S ⟪ m≤n , eγ ⟫ (f €⟨ _ , γn ⟩ (t ⟨ _ , γn ⟩'))
    ≡⟨ €-natural f m≤n eγ (t ⟨ _ , γn ⟩') ⟩
  f €⟨ _ , γm ⟩ (T ⟪ m≤n , eγ ⟫ (t ⟨ _ , γn ⟩'))
    ≡⟨ cong (f €⟨ _ , γm ⟩_) (naturality t m≤n eγ) ⟩
  f €⟨ _ , γm ⟩ (t ⟨ _ , γm ⟩') ∎
  where open ≡-Reasoning

module _ {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) (T S : Ty Γ) {n : ℕ} {δ : Δ ⟨ n ⟩} where
  pshfun-subst-from : PresheafFunc T S n (func σ δ) → PresheafFunc (T [ σ ]) (S [ σ ]) n δ
  _$⟨_,_⟩_ (pshfun-subst-from f) m≤n eδ t = f $⟨ m≤n , trans (naturality σ δ) (cong (func σ) eδ) ⟩ t
  naturality (pshfun-subst-from f) eq-nm eq-mk t = trans ($-cong f refl _ _) (naturality f _ _ t)

  pshfun-subst-to : PresheafFunc (T [ σ ]) (S [ σ ]) n δ → PresheafFunc T S n (func σ δ)
  _$⟨_,_⟩_ (pshfun-subst-to f) m≤n {γ'} eδ t = ctx-element-subst S proof (
                                                f $⟨ m≤n , refl ⟩
                                                ctx-element-subst T (sym proof) t)
    where
      proof : func σ (Δ ⟪ m≤n ⟫ δ) ≡ γ'
      proof = trans (sym (naturality σ δ)) eδ
  naturality (pshfun-subst-to f) {k≤m = k≤m}{m≤n} eq-nm eq-mk t =
    begin
      S ⟪ ≤-refl , α ⟫ f $⟨ ≤-trans k≤m m≤n , refl ⟩ (T ⟪ ≤-refl , _ ⟫ T ⟪ k≤m , eq-mk ⟫ t)
    ≡˘⟨ cong (S ⟪ ≤-refl , α ⟫ ∘ f $⟨ ≤-trans k≤m m≤n , refl ⟩_) (morph-comp T ≤-refl k≤m _ _ t) ⟩
      S ⟪ ≤-refl , α ⟫ f $⟨ ≤-trans k≤m m≤n , refl ⟩ (T ⟪ ≤-trans ≤-refl k≤m , _ ⟫ t)
    ≡⟨ cong (S ⟪ ≤-refl , α ⟫ ∘ f $⟨ ≤-trans k≤m m≤n , refl ⟩_) (morph-cong T (≤-irrelevant _ _) _ _) ⟩
      S ⟪ ≤-refl , α ⟫ f $⟨ ≤-trans k≤m m≤n , refl ⟩ (T ⟪ ≤-trans k≤m ≤-refl , _ ⟫ t)
    ≡⟨ cong (S ⟪ ≤-refl , α ⟫ ∘ f $⟨ ≤-trans k≤m m≤n , refl ⟩_) (morph-comp T k≤m ≤-refl _ _ t) ⟩
      S ⟪ ≤-refl , α ⟫ f $⟨ ≤-trans k≤m m≤n , refl ⟩ (T ⟪ k≤m , _ ⟫ (T ⟪ ≤-refl , β ⟫ t))
    ≡⟨ cong (S ⟪ ≤-refl , α ⟫) ($-cong f refl refl _) ⟩
      S ⟪ ≤-refl , α ⟫ f $⟨ ≤-trans k≤m m≤n , _ ⟩ (T ⟪ k≤m , _ ⟫ (T ⟪ ≤-refl , β ⟫ t))
    ≡⟨ cong (S ⟪ ≤-refl , α ⟫) (naturality f refl (sym (rel-comp Δ k≤m m≤n δ)) _) ⟩
      S ⟪ ≤-refl , α ⟫ S ⟪ k≤m , _ ⟫ f $⟨ m≤n , refl ⟩ (T ⟪ ≤-refl , β ⟫ t)
    ≡˘⟨ morph-comp S ≤-refl k≤m _ α _ ⟩
      S ⟪ ≤-trans ≤-refl k≤m , _ ⟫ f $⟨ m≤n , refl ⟩ (T ⟪ ≤-refl , β ⟫ t)
    ≡⟨ morph-cong S (≤-irrelevant _ _) _ _ ⟩
      S ⟪ ≤-trans k≤m ≤-refl , _ ⟫ f $⟨ m≤n , refl ⟩ (T ⟪ ≤-refl , β ⟫ t)
    ≡⟨ morph-comp S k≤m ≤-refl _ eq-mk _ ⟩
      S ⟪ k≤m , eq-mk ⟫ S ⟪ ≤-refl , _ ⟫ f $⟨ m≤n , refl ⟩ (T ⟪ ≤-refl , β ⟫ t) ∎
    where
      open ≡-Reasoning
      α = _
      β = _

⇛-natural : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) (T S : Ty Γ) → (T ⇛ S) [ σ ] ≅ᵗʸ (T [ σ ]) ⇛ (S [ σ ])
from (⇛-natural σ T S) = record { func = pshfun-subst-from σ T S
                                 ; naturality = λ f → to-pshfun-eq (λ k≤m _ _ → $-cong f refl _ _) }
to (⇛-natural {Δ = Δ} σ T S) = record { func = pshfun-subst-to σ T S
                                       ; naturality = λ {_ _ m≤n} f → to-pshfun-eq λ k≤m eγ t →
  let α = _
      β = _
      ζ = _
      α' = _
      β' = _
      ζ' = _
      ρ = trans (rel-id Δ _) (sym β')
  in begin
    S ⟪ ≤-refl , α ⟫ f $⟨ ≤-trans k≤m m≤n , β ⟩ (T ⟪ ≤-refl , ζ ⟫ t)
  ≡⟨ cong (S ⟪ ≤-refl , α ⟫ ∘ f $⟨ ≤-trans k≤m m≤n , β ⟩_) (morph-cong T (≤-irrelevant _ _) _ _) ⟩
    S ⟪ ≤-refl , α ⟫ f $⟨ ≤-trans k≤m m≤n , β ⟩ (T ⟪ ≤-trans ≤-refl ≤-refl , _ ⟫ t)
  ≡⟨ cong (S ⟪ ≤-refl , α ⟫ ∘ f $⟨ ≤-trans k≤m m≤n , β ⟩_) (morph-comp T _ _ ζ' _ t) ⟩
    S ⟪ ≤-refl , α ⟫ f $⟨ ≤-trans k≤m m≤n , β ⟩ (T ⟪ ≤-refl , _ ⟫ (T ⟪ ≤-refl , ζ' ⟫ t))
  ≡⟨ cong (S ⟪ ≤-refl , α ⟫) ($-cong f (≤-irrelevant _ _) refl _) ⟩
    S ⟪ ≤-refl , α ⟫ f $⟨ ≤-trans ≤-refl (≤-trans k≤m m≤n) , _ ⟩ (T ⟪ ≤-refl , _ ⟫ (T ⟪ ≤-refl , ζ' ⟫ t))
  ≡⟨ cong (S ⟪ ≤-refl , α ⟫) (naturality f _ ρ _) ⟩
    S ⟪ ≤-refl , α ⟫ S ⟪ ≤-refl , _ ⟫ f $⟨ ≤-trans k≤m m≤n , β' ⟩ (T ⟪ ≤-refl , ζ' ⟫ t)
  ≡˘⟨ morph-comp S _ _ _ _ _ ⟩
    S ⟪ ≤-trans ≤-refl ≤-refl , _ ⟫ f $⟨ ≤-trans k≤m m≤n , β' ⟩ (T ⟪ ≤-refl , ζ' ⟫ t)
  ≡⟨ morph-cong S (≤-irrelevant _ _) _ _ ⟩
    S ⟪ ≤-refl , α' ⟫ f $⟨ ≤-trans k≤m m≤n , β' ⟩ (T ⟪ ≤-refl , ζ' ⟫ t) ∎ }
  where open ≡-Reasoning
eq (isoˡ (⇛-natural σ T S)) f = to-pshfun-eq (λ m≤n eγ t →
  begin
    S ⟪ ≤-refl , _ ⟫ f $⟨ m≤n , _ ⟩ (T ⟪ ≤-refl , _ ⟫ t)
  ≡⟨ cong (S ⟪ ≤-refl , _ ⟫) ($-cong f (≤-irrelevant _ _) _ _) ⟩
    S ⟪ ≤-refl , _ ⟫ f $⟨ ≤-trans ≤-refl m≤n , _ ⟩ (T ⟪ ≤-refl , _ ⟫ t)
  ≡⟨ cong (S ⟪ ≤-refl , _ ⟫) (naturality f eγ _ t) ⟩
    S ⟪ ≤-refl , _ ⟫ S ⟪ ≤-refl , _ ⟫ f $⟨ m≤n , eγ ⟩ t
  ≡˘⟨ morph-comp S _ _ _ _ _ ⟩
    S ⟪ ≤-trans ≤-refl ≤-refl , _ ⟫ f $⟨ m≤n , eγ ⟩ t
  ≡⟨ morph-cong S (≤-irrelevant _ _) _ _ ⟩
    S ⟪ ≤-refl , _ ⟫ f $⟨ m≤n , eγ ⟩ t
  ≡⟨ morph-id S _ ⟩
    f $⟨ m≤n , eγ ⟩ t ∎)
  where open ≡-Reasoning
eq (isoʳ (⇛-natural {Δ = Δ} σ T S)) f = to-pshfun-eq (λ m≤n eγ t →
  begin
    S ⟪ ≤-refl , _ ⟫ f $⟨ m≤n , refl ⟩ (T ⟪ ≤-refl , _ ⟫ t)
  ≡⟨ cong (S ⟪ ≤-refl , {!!} ⟫) {!$-cong f (≤-irrelevant _ _) refl {!!}!} ⟩
    S ⟪ ≤-refl , _ ⟫ f $⟨ ≤-trans ≤-refl m≤n , {!!} ⟩ (T ⟪ ≤-refl , _ ⟫ t)
  ≡⟨ cong (S ⟪ ≤-refl , {!!} ⟫ ∘ f $⟨ ≤-trans ≤-refl m≤n , {!!} ⟩_) {!morph-cong T refl {!!} {!!}!} ⟩
    S ⟪ ≤-refl , _ ⟫ f $⟨ ≤-trans ≤-refl m≤n , {!!} ⟩ (T ⟪ ≤-refl , _ ⟫ t)
  ≡⟨ cong (S ⟪ ≤-refl , _ ⟫) (naturality f eγ {!!} t) ⟩
    S ⟪ ≤-refl , _ ⟫ S ⟪ ≤-refl , {!!} ⟫ f $⟨ m≤n , eγ ⟩ t
  ≡˘⟨ morph-comp S _ _ {!!} {!!} {!!} ⟩
    S ⟪ ≤-trans ≤-refl ≤-refl , {!!} ⟫ f $⟨ m≤n , eγ ⟩ t
  ≡⟨ morph-cong S (≤-irrelevant _ _) {!!} _ ⟩
    S ⟪ ≤-refl , _ ⟫ f $⟨ m≤n , eγ ⟩ t
  ≡⟨ morph-id S _ ⟩
    f $⟨ m≤n , eγ ⟩ t ∎)
  where open ≡-Reasoning

{-
to-⇛[_]_ : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) {T S : Ty Γ} → Tm Δ ((T [ σ ]) ⇛ (S [ σ ])) → Tm Δ ((T ⇛ S) [ σ ])
term (to-⇛[_]_ σ {T}{S} f) n δ = MkFunc (λ m≤n t → subst (λ x → S ⟨ _ , x ⟩) (sym (naturality σ δ))
                                                       (f ⟨ _ , δ ⟩' $⟨ m≤n ⟩
                                                       subst (λ x → T ⟨ _ , x ⟩) (naturality σ δ) t))
                                         {!!}
naturality (to-⇛[ σ ] f) = {!!}
-}
{-
-- Another approach to the introduction of function types (based on https://arxiv.org/pdf/1805.08684.pdf).
{-
_⇛_ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ → Ty Γ
type (T ⇛ S) = λ n γ → Tm (𝕪 n ,, (T [ to-𝕪⇒* γ ])) (S [ to-𝕪⇒* γ ⊚ π ])
morph (_⇛_ {Γ = Γ} T S) = λ m≤n γ s → helper (s [ (to-𝕪⇒𝕪 m≤n) ⊹ ]')
  where
    helper : ∀ {m n} {m≤n : m ≤ n} {γ : Γ ⟨ n ⟩} →
             Tm (𝕪 m ,, (T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ])) (S [ to-𝕪⇒* γ ⊚ π ] [ (to-𝕪⇒𝕪 m≤n) ⊹ ]) →
             Tm (𝕪 m ,, (T [ to-𝕪⇒* (Γ ⟪ m≤n ⟫ γ) ])) (S [ to-𝕪⇒* (Γ ⟪ m≤n ⟫ γ) ⊚ π ])
    helper {m} {n} {m≤n} {γ} = subst (λ x → Tm (𝕪 m ,, T [ x ]) (S [ x ⊚ π ])) (𝕪-comp m≤n γ) ∘
                               subst (λ x → Tm (𝕪 m ,, x) (S [ to-𝕪⇒* γ ⊚ to-𝕪⇒𝕪 m≤n ⊚ π {T = x}])) (ty-subst-comp T (to-𝕪⇒* γ) (to-𝕪⇒𝕪 m≤n)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ x ])) (sym (⊚-assoc (to-𝕪⇒* γ) (to-𝕪⇒𝕪 m≤n) π)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ to-𝕪⇒* γ ⊚ x ])) (⊹-π-comm (to-𝕪⇒𝕪 m≤n)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ x ])) (⊚-assoc (to-𝕪⇒* γ) π ((to-𝕪⇒𝕪 m≤n) ⊹)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) x) (ty-subst-comp S (to-𝕪⇒* γ ⊚ π) ((to-𝕪⇒𝕪 m≤n) ⊹))
morph-id (T ⇛ S) = {!!}
morph-comp (T ⇛ S) = {!!}
-}
{-
Π : {Γ : Ctx ℓ} (T : Ty Γ) (S : Ty (Γ ,, T)) → Ty Γ
type (Π T S) = λ n γ → Tm (𝕪 n ,, (T [ to-𝕪⇒* γ ])) (S [ to-𝕪⇒* γ ⊹ ])
morph (Π {Γ = Γ} T S) {m = m} m≤n γ s = subst (λ x → Tm (𝕪 m ,, T [ x ]) (S [ x ⊹ ])) (𝕪-comp m≤n γ)
                                        (subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ⊚ to-𝕪⇒𝕪 m≤n ]) (S [ x ])) {!!} {!s [ (to-𝕪⇒𝕪 m≤n) ⊹ ]'!})
{-  where
    helper : ∀ {m n} {m≤n : m ≤ n} {γ : Γ ⟨ n ⟩} →
             Tm (𝕪 m ,, (T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ])) (S [ to-𝕪⇒* γ ⊹ ] [ to-𝕪⇒𝕪 m≤n ⊹ ]) →
             Tm (𝕪 m ,, (T [ to-𝕪⇒* (Γ ⟪ m≤n ⟫ γ) ])) (S [ to-𝕪⇒* (Γ ⟪ m≤n ⟫ γ) ⊹ ])
    helper {m} {n} {m≤n} {γ} = {!subst (λ x → Tm (𝕪 m ,, T [ x ]) (S [ x ⊚ π ])) (𝕪-comp m≤n γ) ∘
                               subst (λ x → Tm (𝕪 m ,, x) (S [ to-𝕪⇒* γ ⊚ to-𝕪⇒𝕪 m≤n ⊚ π {T = x}])) (ty-subst-comp T (to-𝕪⇒* γ) (to-𝕪⇒𝕪 m≤n)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ x ])) (sym (⊚-assoc (to-𝕪⇒* γ) (to-𝕪⇒𝕪 m≤n) π)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ to-𝕪⇒* γ ⊚ x ])) (⊹-π-comm (to-𝕪⇒𝕪 m≤n)) ∘
                               subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) (S [ x ])) (⊚-assoc (to-𝕪⇒* γ) π ((to-𝕪⇒𝕪 m≤n) ⊹))!} ∘
                               {!subst (λ x → Tm (𝕪 m ,, T [ to-𝕪⇒* γ ] [ to-𝕪⇒𝕪 m≤n ]) x) (ty-subst-comp S (to-𝕪⇒* γ ⊹) (to-𝕪⇒𝕪 m≤n ⊹))!}-}
morph-id (Π T S) = {!!}
morph-comp (Π T S) = {!!}
-}
{-
module _ {Γ : Ctx ℓ} {T S : Ty Γ} where
  lam : Tm (Γ ,, T) (S [ π ]) → Tm Γ (T ⇛ S)
  term (lam b) = λ n γ → subst (λ x → Tm (𝕪 n ,, T [ to-𝕪⇒* γ ]) (S [ x ])) (⊹-π-comm (to-𝕪⇒* γ))
                                (subst (λ x → Tm (𝕪 n ,, T [ to-𝕪⇒* γ ]) x) (ty-subst-comp S π (to-𝕪⇒* γ ⊹))
                                       (b [ to-𝕪⇒* γ ⊹ ]'))
  naturality (lam b) = {!!}

  ap : Tm Γ (T ⇛ S) → Tm (Γ ,, T) (S [ π ])
  term (ap f) = λ n γ → {!term f!}
  naturality (ap f) = {!!}

  app : Tm Γ (T ⇛ S) → Tm Γ T → Tm Γ S
  app f t = {!ap f [ ? ]'!}
-}
-}
