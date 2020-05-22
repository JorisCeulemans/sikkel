--------------------------------------------------
-- (Non-dependent) function types
--------------------------------------------------

open import Categories

module Types.Functions {C : Category} where

-- open import Data.Nat hiding (_⊔_)
-- open import Data.Nat.Properties
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Function hiding (_⟨_⟩_; _↣_)
open import Level
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types {C = C}
open import CwF-Structure.Terms {C = C}
open import CwF-Structure.ContextExtension {C = C}
open import CwF-Structure.SubstitutionSequence {C = C}

open Category C


--------------------------------------------------
-- Description of a function type at a specific stage (object of the base category)

record PresheafFunc {ℓ} {Γ : Ctx C ℓ} (T S : Ty Γ) (z : Ob) (γ : Γ ⟨ z ⟩) : Set ℓ where
  constructor MkFunc
  field
    _$⟨_,_⟩_ : ∀ {y} (ρ : Hom y z) {γ' : Γ ⟨ y ⟩} (eq : Γ ⟪ ρ ⟫ γ ≡ γ') →
               T ⟨ y , γ' ⟩ → S ⟨ y , γ' ⟩
    naturality : ∀ {x y} {ρ-xy : Hom x y} {ρ-yz : Hom y z} {γx : Γ ⟨ x ⟩} {γy : Γ ⟨ y ⟩} →
                 (eq-zy : Γ ⟪ ρ-yz ⟫ γ ≡ γy) (eq-yx : Γ ⟪ ρ-xy ⟫ γy ≡ γx) (t : T ⟨ y , γy ⟩)→
                 _$⟨_,_⟩_ (ρ-yz ∙ ρ-xy) (strong-rel-comp Γ eq-zy eq-yx) (T ⟪ ρ-xy , eq-yx ⟫ t) ≡
                   S ⟪ ρ-xy , eq-yx ⟫ (_$⟨_,_⟩_ ρ-yz eq-zy t)
  infix 13 _$⟨_,_⟩_
open PresheafFunc public

private
  variable
    x y z : Ob

-- Here we make again use of uip by pattern matching on both equality proofs.
$-cong : {Γ : Ctx C ℓ} {T S : Ty Γ} {γx : Γ ⟨ x ⟩} {γy : Γ ⟨ y ⟩} (f : PresheafFunc T S y γy)
         {ρ ρ' : Hom x y} (eρ : ρ ≡ ρ')
         (eγ : Γ ⟪ ρ ⟫ γy ≡ γx) (eγ' : Γ ⟪ ρ' ⟫ γy ≡ γx)
         {t : T ⟨ x , γx ⟩} →
         f $⟨ ρ , eγ ⟩ t ≡ f $⟨ ρ' , eγ' ⟩ t
$-cong f refl refl refl = refl

to-pshfun-eq : {Γ : Ctx C ℓ} {T S : Ty Γ} {γ : Γ ⟨ y ⟩} {f g : PresheafFunc T S y γ} →
               (∀ {x} (ρ : Hom x y) {γ'} (eq : Γ ⟪ ρ ⟫ γ ≡ γ') t →
                   f $⟨ ρ , eq ⟩ t ≡ g $⟨ ρ , eq ⟩ t) →
               f ≡ g
to-pshfun-eq e = cong₂-d MkFunc
  (funextI (funext (λ ρ → funextI (funext λ eq → funext λ t → e ρ eq t))))
  (funextI (funextI (funextI (funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _)))))))

lower-presheaffunc : {Γ : Ctx C ℓ} {T S : Ty Γ} (ρ-yz : Hom y z)
                     {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} (eq : Γ ⟪ ρ-yz ⟫ γz ≡ γy) →
                     PresheafFunc T S z γz → PresheafFunc T S y γy
lower-presheaffunc {y = y}{z = z}{Γ = Γ}{T}{S} ρ-yz {γz}{γy} eq-zy f = MkFunc g g-nat
  where
    g : ∀ {x} (ρ-xy : Hom x y) {γx} (eq-yx : Γ ⟪ ρ-xy ⟫ γy ≡ γx) →
        T ⟨ x , γx ⟩ → S ⟨ x , γx ⟩
    g ρ-xy eq-yx = f $⟨ ρ-yz ∙ ρ-xy , strong-rel-comp Γ eq-zy eq-yx ⟩_
    open ≡-Reasoning
    g-nat : ∀ {w x} {ρ-wx : Hom w x} {ρ-xy : Hom x y} {γx : Γ ⟨ x ⟩} {γw : Γ ⟨ w ⟩}
            (eq-yx : Γ ⟪ ρ-xy ⟫ γy ≡ γx) (eq-xw : Γ ⟪ ρ-wx ⟫ γx ≡ γw) → _
    g-nat {ρ-wx = ρ-wx}{ρ-xy} eq-yx eq-xw t =
      f $⟨ ρ-yz ∙ (ρ-xy ∙ ρ-wx) , strong-rel-comp Γ eq-zy (strong-rel-comp Γ eq-yx eq-xw) ⟩ (T ⟪ ρ-wx , eq-xw ⟫ t)
        ≡˘⟨ $-cong f ∙assoc _ _ ⟩
      f $⟨ (ρ-yz ∙ ρ-xy) ∙ ρ-wx , strong-rel-comp Γ (strong-rel-comp Γ eq-zy eq-yx) eq-xw ⟩ (T ⟪ ρ-wx , eq-xw ⟫ t)
        ≡⟨ naturality f (strong-rel-comp Γ eq-zy eq-yx) eq-xw t ⟩
      (S ⟪ ρ-wx , eq-xw ⟫ (f $⟨ ρ-yz ∙ ρ-xy , strong-rel-comp Γ eq-zy eq-yx ⟩ t)) ∎


--------------------------------------------------
-- Definition of the function type + term constructors

_⇛_ : {Γ : Ctx C ℓ} → Ty Γ → Ty Γ → Ty Γ
type (_⇛_ {Γ = Γ} T S) n γ = PresheafFunc T S n γ
morph (T ⇛ S) = lower-presheaffunc
morph-id (_⇛_ {Γ = Γ} T S) f = to-pshfun-eq (λ m≤n eγ t → $-cong f hom-idˡ _ eγ)
morph-comp (_⇛_ {Γ = Γ} T S) l≤m m≤n eq-nm eq-ml f = to-pshfun-eq (λ k≤l eq-lk t → $-cong f ∙assoc _ _)

lam : {Γ : Ctx C ℓ} (T : Ty Γ) {S : Ty Γ} → Tm (Γ ,, T) (S [ π ]) → Tm Γ (T ⇛ S)
term (lam T {S} b) z γz = MkFunc (λ ρ-yz {γy} eγ t → b ⟨ _ , [ γy , t ] ⟩')
                                 (λ {x = x}{y}{ρ-xy}{_}{γx}{γy} eq-zy eq-yx t →
  b ⟨ x , [ γx , T ⟪ ρ-xy , eq-yx ⟫ t ] ⟩'
    ≡⟨ sym (naturality b ρ-xy (to-Σ-eq eq-yx (morph-subst T refl eq-yx t))) ⟩
  S ⟪ ρ-xy , from-Σ-eq1 (to-Σ-eq eq-yx _) ⟫ b ⟨ y , [ γy , t ] ⟩'
    ≡⟨ cong (λ x → S ⟪ ρ-xy , x ⟫ _) (from-to-Σ-eq1 (morph-subst T refl eq-yx t)) ⟩
  S ⟪ ρ-xy , eq-yx ⟫ b ⟨ y , [ γy , t ] ⟩' ∎)
  where open ≡-Reasoning
naturality (lam T b) _ _ = to-pshfun-eq (λ _ _ _ → refl)

_€⟨_,_⟩_ : {Γ : Ctx C ℓ} {T S : Ty Γ} → Tm Γ (T ⇛ S) → (x : Ob) (γ : Γ ⟨ x ⟩) → T ⟨ x , γ ⟩ → S ⟨ x , γ ⟩
_€⟨_,_⟩_ {Γ = Γ} f x γ t = f ⟨ x , γ ⟩' $⟨ hom-id , rel-id Γ γ ⟩ t

€-natural : {Γ : Ctx C ℓ} {T S : Ty Γ} (f : Tm Γ (T ⇛ S)) (ρ : Hom x y)
            {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} (eγ : Γ ⟪ ρ ⟫ γy ≡ γx)
            (t : T ⟨ y , γy ⟩) →
            S ⟪ ρ , eγ ⟫ (f €⟨ y , γy ⟩ t) ≡ f €⟨ x , γx ⟩ (T ⟪ ρ , eγ ⟫ t)
€-natural {Γ = Γ}{T}{S} f ρ {γy}{γx} eγ t =
  S ⟪ ρ , eγ ⟫ (f ⟨ _ , γy ⟩' $⟨ hom-id , rel-id Γ γy ⟩ t)
    ≡⟨ sym (naturality (f ⟨ _ , γy ⟩') (rel-id Γ γy) eγ t) ⟩
  f ⟨ _ , γy ⟩' $⟨ hom-id ∙ ρ , strong-rel-comp Γ (rel-id Γ γy) eγ ⟩ (T ⟪ ρ , eγ ⟫ t)
    ≡⟨ $-cong (f ⟨ _ , γy ⟩') (trans hom-idˡ (sym hom-idʳ)) _ _ ⟩
  f ⟨ _ , γy ⟩' $⟨ ρ ∙ hom-id , strong-rel-comp Γ eγ (rel-id Γ γx) ⟩ (T ⟪ ρ , eγ ⟫ t)
    ≡⟨ cong (λ x → x $⟨ _ , _ ⟩ _) (naturality f ρ eγ) ⟩
  f ⟨ _ , γx ⟩' $⟨ hom-id , rel-id Γ γx ⟩ (T ⟪ ρ , eγ ⟫ t) ∎
  where open ≡-Reasoning

app : {Γ : Ctx C ℓ} {T S : Ty Γ} → Tm Γ (T ⇛ S) → Tm Γ T → Tm Γ S
term (app f t) y γ = f €⟨ y , γ ⟩ (t ⟨ y , γ ⟩')
naturality (app {Γ = Γ}{T}{S} f t) ρ {γy}{γx} eγ =
  S ⟪ ρ , eγ ⟫ (f €⟨ _ , γy ⟩ (t ⟨ _ , γy ⟩'))
    ≡⟨ €-natural f ρ eγ (t ⟨ _ , γy ⟩') ⟩
  f €⟨ _ , γx ⟩ (T ⟪ ρ , eγ ⟫ (t ⟨ _ , γy ⟩'))
    ≡⟨ cong (f €⟨ _ , γx ⟩_) (naturality t ρ eγ) ⟩
  f €⟨ _ , γx ⟩ (t ⟨ _ , γx ⟩') ∎
  where open ≡-Reasoning


--------------------------------------------------
-- Congruence proofs

pshfun-dimap : {Γ : Ctx C ℓ} {T T' S S' : Ty Γ} → (T' ↣ T) → (S ↣ S') →
               (z : Ob) (γ : Γ ⟨ z ⟩) →
               PresheafFunc T S z γ → PresheafFunc T' S' z γ
_$⟨_,_⟩_ (pshfun-dimap η φ _ γ f) ρ eγ t' = func φ (f $⟨ ρ , eγ ⟩ func η t')
naturality (pshfun-dimap {T = T}{T'}{S}{S'} η φ z γ f) eq-zy eq-yx t' =
  begin
    func φ (f $⟨ _ , _ ⟩ func η (T' ⟪ _ , eq-yx ⟫ t'))
  ≡˘⟨ cong (func φ ∘ f $⟨ _ , _ ⟩_) (naturality η t') ⟩
    func φ (f $⟨ _ , _ ⟩ (T ⟪ _ , eq-yx ⟫ func η t'))
  ≡⟨ cong (func φ) (naturality f eq-zy eq-yx (func η t')) ⟩
    func φ (S ⟪ _ , eq-yx ⟫ (f $⟨ _ , eq-zy ⟩ func η t'))
  ≡˘⟨ naturality φ _ ⟩
    S' ⟪ _ , eq-yx ⟫ func φ (f $⟨ _ , eq-zy ⟩ func η t') ∎
  where open ≡-Reasoning

⇛-dimap : {Γ : Ctx C ℓ} {T T' S S' : Ty Γ} → (T' ↣ T) → (S ↣ S') → (T ⇛ S ↣ T' ⇛ S')
func (⇛-dimap η φ) = pshfun-dimap η φ _ _
naturality (⇛-dimap η φ) f = to-pshfun-eq λ _ _ _ → refl

⇛-cong : {Γ : Ctx C ℓ} {T T' S S' : Ty Γ} → T ≅ᵗʸ T' → S ≅ᵗʸ S' → T ⇛ S ≅ᵗʸ T' ⇛ S'
from (⇛-cong T=T' S=S') = ⇛-dimap (to T=T') (from S=S')
to (⇛-cong T=T' S=S') = ⇛-dimap (from T=T') (to S=S')
eq (isoˡ (⇛-cong T=T' S=S')) f = to-pshfun-eq (λ ρ eγ t →
  begin
    func (to S=S') (func (from S=S') (f $⟨ ρ , eγ ⟩ func (to T=T') (func (from T=T') t)))
  ≡⟨ eq (isoˡ S=S') _ ⟩
    f $⟨ ρ , eγ ⟩ func (to T=T') (func (from T=T') t)
  ≡⟨ cong (f $⟨ ρ , eγ ⟩_) (eq (isoˡ T=T') t) ⟩
    f $⟨ ρ , eγ ⟩ t ∎)
  where open ≡-Reasoning
eq (isoʳ (⇛-cong T=T' S=S')) f = to-pshfun-eq (λ ρ eγ t' →
  begin
    func (from S=S') (func (to S=S') (f $⟨ ρ , eγ ⟩ func (from T=T') (func (to T=T') t')))
  ≡⟨ eq (isoʳ S=S') _ ⟩
    f $⟨ ρ , eγ ⟩ func (from T=T') (func (to T=T') t')
  ≡⟨ cong (f $⟨ ρ , eγ ⟩_) (eq (isoʳ T=T') t') ⟩
    f $⟨ ρ , eγ ⟩ t' ∎)
  where open ≡-Reasoning

lam-cong : {Γ : Ctx C ℓ} (T : Ty Γ) {S : Ty Γ} {b b' : Tm (Γ ,, T) (S [ π ])} →
           b ≅ᵗᵐ b' → lam T {S = S} b ≅ᵗᵐ lam T b'
eq (lam-cong T b=b') γ = to-pshfun-eq (λ _ {γ'}  _ t → eq b=b' [ γ' , t ])

€-cong : {Γ : Ctx C ℓ} {T S : Ty Γ} {f f' : Tm Γ (T ⇛ S)} {γ : Γ ⟨ z ⟩} {t t' : T ⟨ z , γ ⟩} →
         f ≅ᵗᵐ f' → t ≡ t' → f €⟨ z , γ ⟩ t ≡ f' €⟨ z , γ ⟩ t'
€-cong {z = z}{f = f}{f'}{γ}{t}{t'} f=f' t=t' =
  begin
    f ⟨ z , γ ⟩' $⟨ hom-id , _ ⟩ t
  ≡⟨ cong (f ⟨ z , γ ⟩' $⟨ hom-id , _ ⟩_) t=t' ⟩
    f ⟨ z , γ ⟩' $⟨ hom-id , _ ⟩ t'
  ≡⟨ cong (_$⟨ hom-id , _ ⟩ t') (eq f=f' γ) ⟩
    f' ⟨ z , γ ⟩' $⟨ hom-id , _ ⟩ t' ∎
  where open ≡-Reasoning

app-cong : {Γ : Ctx C ℓ} {T S : Ty Γ} {f f' : Tm Γ (T ⇛ S)} {t t' : Tm Γ T} →
           f ≅ᵗᵐ f' → t ≅ᵗᵐ t' → app f t ≅ᵗᵐ app f' t'
eq (app-cong {f = f}{f'}{t}{t'} f=f' t=t') γ =
  begin
    f ⟨ _ , γ ⟩' $⟨ hom-id , _ ⟩ t ⟨ _ , γ ⟩'
  ≡⟨ cong (_$⟨ hom-id , _ ⟩ t ⟨ _ , γ ⟩') (eq f=f' γ) ⟩
    f' ⟨ _ , γ ⟩' $⟨ hom-id , _ ⟩ t ⟨ _ , γ ⟩'
  ≡⟨ cong (f' ⟨ _ , γ ⟩' $⟨ hom-id , _ ⟩_) (eq t=t' γ) ⟩
    f' ⟨ _ , γ ⟩' $⟨ hom-id , _ ⟩ t' ⟨ _ , γ ⟩' ∎
  where open ≡-Reasoning

module _ {Γ : Ctx C ℓ} {T T' S S' : Ty Γ} (T=T' : T ≅ᵗʸ T') (S=S' : S ≅ᵗʸ S') where
  lam-ι : (b : Tm (Γ ,, T') (S' [ π ])) →
          ι[ ⇛-cong T=T' S=S' ] (lam T' {S = S'} b) ≅ᵗᵐ
            lam T (ι[ ty-subst-cong-ty π S=S' ] (
                   ι⁻¹[ ty-subst-cong-subst (ctx-ext-subst-proj₁ {T = T'} (π {T = T}) (ι⁻¹[ ty-subst-cong-ty (π {T = T}) T=T' ] (ξ {T = T}))) S' ] (
                   ι⁻¹[ ty-subst-comp S' π (ty-eq-to-ext-subst Γ T=T') ] (
                   b [ ty-eq-to-ext-subst Γ T=T' ]'))))
  eq (lam-ι b) γ = to-pshfun-eq (λ _ _ _ → sym(
    begin
      func (to S=S') (S' ⟪ hom-id , _ ⟫ b ⟨ _ , _ ⟩')
    ≡⟨ cong (func (to S=S')) (morph-cong S' refl _ _) ⟩
      func (to S=S') (S' ⟪ hom-id , _ ⟫ b ⟨ _ , _ ⟩')
    ≡⟨ cong (func (to S=S')) (morph-id S' _) ⟩
      func (to S=S') (b ⟨ _ , _ ⟩') ∎))
    where open ≡-Reasoning

  app-ι : (f : Tm Γ (T' ⇛ S')) (t : Tm Γ T') → app (ι[ ⇛-cong T=T' S=S' ] f) (ι[ T=T' ] t) ≅ᵗᵐ ι[ S=S' ] (app f t)
  eq (app-ι f t) γ = cong (func (to S=S') ∘ f ⟨ _ , γ ⟩' $⟨ hom-id , _ ⟩_) (eq (isoʳ T=T') (t ⟨ _ , γ ⟩'))


--------------------------------------------------
-- Naturality proofs

module _ {Δ Γ : Ctx C ℓ} (σ : Δ ⇒ Γ) (T S : Ty Γ) {δ : Δ ⟨ z ⟩} where
  pshfun-subst-from : PresheafFunc T S z (func σ δ) → PresheafFunc (T [ σ ]) (S [ σ ]) z δ
  _$⟨_,_⟩_ (pshfun-subst-from f) ρ-yz eδ t = f $⟨ ρ-yz , trans (naturality σ δ) (cong (func σ) eδ) ⟩ t
  naturality (pshfun-subst-from f) _ _ t = trans ($-cong f refl _ _) (naturality f _ _ t)

  pshfun-subst-to : PresheafFunc (T [ σ ]) (S [ σ ]) z δ → PresheafFunc T S z (func σ δ)
  _$⟨_,_⟩_ (pshfun-subst-to f) ρ-yz {γ'} eδ t = ctx-element-subst S proof (
                                                 f $⟨ ρ-yz , refl ⟩
                                                 ctx-element-subst T (sym proof) t)
    where
      proof : func σ (Δ ⟪ ρ-yz ⟫ δ) ≡ γ'
      proof = trans (sym (naturality σ δ)) eδ
  naturality (pshfun-subst-to f) {ρ-xy = ρ-xy}{ρ-yz} _ eq-yx t =
    begin
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , refl ⟩ (T ⟪ hom-id , _ ⟫ T ⟪ ρ-xy , eq-yx ⟫ t)
    ≡˘⟨ cong (S ⟪ hom-id , α ⟫ ∘ f $⟨ ρ-yz ∙ ρ-xy , refl ⟩_) (morph-comp T hom-id ρ-xy _ _ t) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , refl ⟩ (T ⟪ ρ-xy ∙ hom-id , _ ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , α ⟫ ∘ f $⟨ ρ-yz ∙ ρ-xy , refl ⟩_) (morph-cong T (trans hom-idʳ (sym hom-idˡ)) _ _) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , refl ⟩ (T ⟪ hom-id ∙ ρ-xy , _ ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , α ⟫ ∘ f $⟨ ρ-yz ∙ ρ-xy , refl ⟩_) (morph-comp T ρ-xy hom-id _ _ t) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , refl ⟩ (T ⟪ ρ-xy , _ ⟫ (T ⟪ hom-id , β ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫) ($-cong f refl refl _) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , _ ⟩ (T ⟪ ρ-xy , _ ⟫ (T ⟪ hom-id , β ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫) (naturality f refl (sym (rel-comp Δ ρ-xy ρ-yz δ)) _) ⟩
      S ⟪ hom-id , α ⟫ S ⟪ ρ-xy , _ ⟫ f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , β ⟫ t)
    ≡˘⟨ morph-comp S hom-id ρ-xy _ α _ ⟩
      S ⟪ ρ-xy ∙ hom-id , _ ⟫ f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , β ⟫ t)
    ≡⟨ morph-cong S (trans hom-idʳ (sym hom-idˡ)) _ _ ⟩
      S ⟪ hom-id ∙ ρ-xy , _ ⟫ f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , β ⟫ t)
    ≡⟨ morph-comp S ρ-xy hom-id _ eq-yx _ ⟩
      S ⟪ ρ-xy , eq-yx ⟫ S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , β ⟫ t) ∎
    where
      open ≡-Reasoning
      α = _
      β = _

module _ {Δ Γ : Ctx C ℓ} {T S : Ty Γ} (σ : Δ ⇒ Γ) where
  ⇛-natural : (T ⇛ S) [ σ ] ≅ᵗʸ (T [ σ ]) ⇛ (S [ σ ])
  from ⇛-natural = record { func = pshfun-subst-from σ T S
                           ; naturality = λ f → to-pshfun-eq (λ _ _ _ → $-cong f refl _ _) }
  to ⇛-natural = record { func = pshfun-subst-to σ T S
                         ; naturality = λ {_ _ ρ-yz} f → to-pshfun-eq λ ρ-xy eγ t →
    let α = _
        β = _
        ζ = _
        α' = _
        β' = _
        ζ' = _
    in begin
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , β ⟩ (T ⟪ hom-id , ζ ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , α ⟫ ∘ f $⟨ ρ-yz ∙ ρ-xy , β ⟩_) (morph-cong T (sym hom-idʳ) _ _) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , β ⟩ (T ⟪ hom-id ∙ hom-id , _ ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , α ⟫ ∘ f $⟨ ρ-yz ∙ ρ-xy , β ⟩_) (morph-comp T _ _ ζ' _ t) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , β ⟩ (T ⟪ hom-id , _ ⟫ (T ⟪ hom-id , ζ' ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫) ($-cong f (sym hom-idʳ) refl _) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ (ρ-yz ∙ ρ-xy) ∙ hom-id , _ ⟩ (T ⟪ hom-id , _ ⟫ (T ⟪ hom-id , ζ' ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫) (naturality f _ (trans (rel-id Δ _) (sym β')) _) ⟩
      S ⟪ hom-id , α ⟫ S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz ∙ ρ-xy , β' ⟩ (T ⟪ hom-id , ζ' ⟫ t)
    ≡˘⟨ morph-comp S _ _ _ _ _ ⟩
      S ⟪ hom-id ∙ hom-id , _ ⟫ f $⟨ ρ-yz ∙ ρ-xy , β' ⟩ (T ⟪ hom-id , ζ' ⟫ t)
    ≡⟨ morph-cong S hom-idʳ _ _ ⟩
      S ⟪ hom-id , α' ⟫ f $⟨ ρ-yz ∙ ρ-xy , β' ⟩ (T ⟪ hom-id , ζ' ⟫ t) ∎ }
    where open ≡-Reasoning
  eq (isoˡ ⇛-natural) f = to-pshfun-eq (λ ρ-yz eγ t →
    begin
      S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , _ ⟩ (T ⟪ hom-id , _ ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , _ ⟫) ($-cong f (sym hom-idʳ) _ _) ⟩
      S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz ∙ hom-id , _ ⟩ (T ⟪ hom-id , _ ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , _ ⟫) (naturality f eγ _ t) ⟩
      S ⟪ hom-id , _ ⟫ S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , eγ ⟩ t
    ≡˘⟨ morph-comp S _ _ _ _ _ ⟩
      S ⟪ hom-id ∙ hom-id , _ ⟫ f $⟨ ρ-yz , eγ ⟩ t
    ≡⟨ morph-cong S hom-idʳ _ _ ⟩
      S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , eγ ⟩ t
    ≡⟨ morph-id S _ ⟩
      f $⟨ ρ-yz , eγ ⟩ t ∎)
    where open ≡-Reasoning
  eq (isoʳ ⇛-natural) f = to-pshfun-eq (λ ρ-yz eδ t →
    let α = trans (rel-id Δ _) (sym eδ)
        β = _
    in begin
      S ⟪ hom-id , β ⟫ f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , _ ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , β ⟫) ($-cong f (sym hom-idʳ) refl _) ⟩
      S ⟪ hom-id , β ⟫ f $⟨ ρ-yz ∙ hom-id , _ ⟩ (T ⟪ hom-id , _ ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , β ⟫ ∘ f $⟨ ρ-yz ∙ hom-id , _ ⟩_) (morph-cong T refl _ _) ⟩
      S ⟪ hom-id , β ⟫ f $⟨ ρ-yz ∙ hom-id , _ ⟩ (T [ σ ] ⟪ hom-id , α ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , _ ⟫) (naturality f eδ _ t) ⟩
      S ⟪ hom-id , β ⟫ S [ σ ] ⟪ hom-id , α ⟫ f $⟨ ρ-yz , eδ ⟩ t
    ≡˘⟨ morph-comp S _ _ _ _ _ ⟩
      S ⟪ hom-id ∙ hom-id , _ ⟫ f $⟨ ρ-yz , eδ ⟩ t
    ≡⟨ morph-cong S hom-idʳ _ _ ⟩
      S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , eδ ⟩ t
    ≡⟨ morph-id S _ ⟩
      f $⟨ ρ-yz , eδ ⟩ t ∎)
    where open ≡-Reasoning

  lam-natural : (b : Tm (Γ ,, T) (S [ π ])) →
                (lam T {S = S} b) [ σ ]' ≅ᵗᵐ
                  ι[ ⇛-natural ] (
                  lam (T [ σ ]) (ι⁻¹[ ty-subst-seq-cong (π {T = T} ∷ σ ⊹ ◼) (σ ∷ π {T = T [ σ ]} ◼) S (⊹-π-comm σ) ] (b [ σ ⊹ ]')))
  eq (lam-natural b) δ = to-pshfun-eq (λ ρ {γ'} eγ t → sym (
    let α = begin
              subst (λ - → T ⟨ _ , - ⟩) _ (T ⟪ hom-id , _ ⟫ T ⟪ hom-id , _ ⟫ t)
            ≡⟨ morph-subst T refl _ _ ⟩
              T ⟪ hom-id , _ ⟫ T ⟪ hom-id , _ ⟫ t
            ≡˘⟨ morph-comp T hom-id hom-id _ _ t ⟩
              T ⟪ hom-id ∙ hom-id , _ ⟫ t
            ≡⟨ morph-cong T hom-idʳ _ _ ⟩
              T ⟪ hom-id , _ ⟫ t
            ≡⟨ morph-id T t ⟩
              t ∎
    in begin
      S ⟪ hom-id , _ ⟫ S ⟪ hom-id , _ ⟫ b ⟨ _ , [ func σ (Δ ⟪ ρ ⟫ δ) , T ⟪ hom-id , _ ⟫ t ] ⟩'
    ≡˘⟨ morph-comp S hom-id hom-id _ _ _ ⟩
      S ⟪ hom-id ∙ hom-id , _ ⟫ b ⟨ _ , [ func σ (Δ ⟪ ρ ⟫ δ) , T ⟪ hom-id , _ ⟫ t ] ⟩'
    ≡⟨ morph-cong S hom-idʳ _ _ ⟩
      S ⟪ hom-id , _ ⟫ b ⟨ _ , [ func σ (Δ ⟪ ρ ⟫ δ) , T ⟪ hom-id , _ ⟫ t ] ⟩'
    ≡⟨ naturality b hom-id (to-Σ-eq (trans (rel-id Γ _) (trans (sym (naturality σ δ)) eγ)) α) ⟩
      b ⟨ _ , [ γ' , t ] ⟩' ∎))
    where open ≡-Reasoning

  app-natural : (f : Tm Γ (T ⇛ S)) (t : Tm Γ T) →
                (app f t) [ σ ]' ≅ᵗᵐ app (ι⁻¹[ ⇛-natural ] (f [ σ ]')) (t [ σ ]')
  eq (app-natural f t) δ = $-cong (f ⟨ _ , func σ δ ⟩') refl _ _

{-
-- Another approach to the introduction of function types (based on https://arxiv.org/pdf/1805.08684.pdf).
{-
_⇛_ : {Γ : Ctx  ℓ} → Ty Γ → Ty Γ → Ty Γ
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
