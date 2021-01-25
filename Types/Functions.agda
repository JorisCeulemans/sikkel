{-# OPTIONS --without-K #-}

--------------------------------------------------
-- (Non-dependent) function types
--------------------------------------------------

open import Categories

module Types.Functions {C : Category} where

open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.String
open import Function using (_∘_; Congruent)
open import Level
open import Relation.Binary hiding (_⇒_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality
  hiding ([_]; naturality) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension
open import Reflection.SubstitutionSequence

open Category C

private
  variable
    ℓc ℓt ℓs r rc rt rs : Level
    x y z : Ob
    Γ Δ : Ctx C ℓ r
    T T' S S' : Ty Γ ℓ r

infixr 12 _⇛_
infixr 4 nlam[_∈_]_

{-
open import Axiom.UniquenessOfIdentityProofs
private
  uip : ∀ {a} {A : Set a} → UIP A
  uip refl refl = refl
-}


--------------------------------------------------
-- Description of a function type at a specific stage (object of the base category)

record PresheafFunc {Γ : Ctx C ℓc rc} (T : Ty Γ ℓt rt) (S : Ty Γ ℓs rs) (z : Ob) (γ : Γ ⟨ z ⟩) : Set (ℓc ⊔ rc ⊔ ℓt ⊔ rt ⊔ ℓs ⊔ rs) where
  constructor MkFunc
  field
    _$⟨_,_⟩_ : ∀ {y} (ρ : Hom y z) {γ' : Γ ⟨ y ⟩} (eγ : Γ ⟪ ρ ⟫ γ ≈[ Γ ]≈ γ') →
               T ⟨ y , γ' ⟩ → S ⟨ y , γ' ⟩
    $-cong : ∀ {y} (ρ : Hom y z) {γ' : Γ ⟨ y ⟩} (eγ : Γ ⟪ ρ ⟫ γ ≈[ Γ ]≈ γ') →
             Congruent (ty≈ T y γ') (ty≈ S y γ') (_$⟨_,_⟩_ ρ eγ)
    $-hom-cong : ∀ {y} {ρ ρ' : Hom y z} (e-hom : ρ ≡ ρ')
                 {γy : Γ ⟨ y ⟩} {eγ : Γ ⟪ ρ ⟫ γ ≈[ Γ ]≈ γy} {eγ' : Γ ⟪ ρ' ⟫ γ ≈[ Γ ]≈ γy}
                 {t : T ⟨ y , γy ⟩} →
                 _$⟨_,_⟩_ ρ eγ t ≈⟦ S ⟧≈ _$⟨_,_⟩_ ρ' eγ' t
    naturality : ∀ {x y} {ρ-xy : Hom x y} {ρ-yz : Hom y z} {γx : Γ ⟨ x ⟩} {γy : Γ ⟨ y ⟩} →
                 (eq-zy : Γ ⟪ ρ-yz ⟫ γ ≈[ Γ ]≈ γy) (eq-yx : Γ ⟪ ρ-xy ⟫ γy ≈[ Γ ]≈ γx) (t : T ⟨ y , γy ⟩)→
                 _$⟨_,_⟩_ (ρ-yz ∙ ρ-xy) (strong-rel-comp Γ eq-zy eq-yx) (T ⟪ ρ-xy , eq-yx ⟫ t) ≈⟦ S ⟧≈
                   S ⟪ ρ-xy , eq-yx ⟫ (_$⟨_,_⟩_ ρ-yz eq-zy t)
  infix 13 _$⟨_,_⟩_
open PresheafFunc public

{-
-- Here we make again use of uip by pattern matching on both equality proofs.
$-cong : {T : Ty Γ ℓt} {S : Ty Γ ℓs}
         {γx : Γ ⟨ x ⟩} {γy : Γ ⟨ y ⟩} (f : PresheafFunc T S y γy)
         {ρ ρ' : Hom x y} (eρ : ρ ≡ ρ')
         (eγ : Γ ⟪ ρ ⟫ γy ≡ γx) (eγ' : Γ ⟪ ρ' ⟫ γy ≡ γx)
         {t : T ⟨ x , γx ⟩} →
         f $⟨ ρ , eγ ⟩ t ≡ f $⟨ ρ' , eγ' ⟩ t
$-cong f refl refl refl = refl

-- This is one of the few places where we use function extensionality.
to-pshfun-eq : {T : Ty Γ ℓt} {S : Ty Γ ℓs}
               {γ : Γ ⟨ y ⟩} {f g : PresheafFunc T S y γ} →
               (∀ {x} (ρ : Hom x y) {γ'} (eq : Γ ⟪ ρ ⟫ γ ≡ γ') t →
                   f $⟨ ρ , eq ⟩ t ≡ g $⟨ ρ , eq ⟩ t) →
               f ≡ g
to-pshfun-eq e = cong₂-d MkFunc
  (funextI (funext (λ ρ → funextI (funext λ eq → funext λ t → e ρ eq t))))
  (funextI (funextI (funextI (funextI (funextI (funextI (funext λ _ → funext λ _ → funext λ _ → uip _ _)))))))
-}

func≈ : {Γ : Ctx C ℓc rc} (T : Ty Γ ℓt rt) (S : Ty Γ ℓs rs) (y : Ob) (γy : Γ ⟨ y ⟩) →
        Rel (PresheafFunc T S y γy) (ℓc ⊔ rc ⊔ ℓt ⊔ rs)
func≈ {Γ = Γ} _ S y γy f g = ∀ {x} (ρ : Hom x y) {γx} (eγ : Γ ⟪ ρ ⟫ γy ≈[ Γ ]≈ γx) t →
                             f $⟨ ρ , eγ ⟩ t ≈⟦ S ⟧≈ g $⟨ ρ , eγ ⟩ t

func≈-equiv : {Γ : Ctx C ℓc rc} (T : Ty Γ ℓt rt) (S : Ty Γ ℓs rs) (y : Ob) (γy : Γ ⟨ y ⟩) →
              IsEquivalence (func≈ T S y γy)
IsEquivalence.refl (func≈-equiv T S y γy) _ _ _ = ty≈-refl S
IsEquivalence.sym (func≈-equiv T S y γy) f=g ρ eγ t = ty≈-sym S (f=g ρ eγ t)
IsEquivalence.trans (func≈-equiv T S y γy) f=g g=h ρ eγ t = ty≈-trans S (f=g ρ eγ t) (g=h ρ eγ t)

-- This will be used to define the action of a function type on morphisms.
lower-presheaffunc : {T : Ty Γ ℓt rt} {S : Ty Γ ℓs rs} (ρ-yz : Hom y z)
                     {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} (eγ : Γ ⟪ ρ-yz ⟫ γz ≈[ Γ ]≈ γy) →
                     PresheafFunc T S z γz → PresheafFunc T S y γy
lower-presheaffunc {Γ = Γ}{y = y}{z = z}{T = T}{S = S} ρ-yz {γz}{γy} eγ-zy f = MkFunc g g-cong g-hom-cong g-nat
  where
    g : ∀ {x} (ρ-xy : Hom x y) {γx} (eγ-yx : Γ ⟪ ρ-xy ⟫ γy ≈[ Γ ]≈ γx) →
        T ⟨ x , γx ⟩ → S ⟨ x , γx ⟩
    g ρ-xy eγ-yx = f $⟨ ρ-yz ∙ ρ-xy , strong-rel-comp Γ eγ-zy eγ-yx ⟩_
    g-cong : ∀ {x} (ρ : Hom x y) {γx : Γ ⟨ x ⟩} (eγ-yx : Γ ⟪ ρ ⟫ γy ≈[ Γ ]≈ γx) →
             Congruent (ty≈ T x γx) (ty≈ S x γx) (g ρ eγ-yx)
    g-cong ρ eγ-yx et = $-cong f (ρ-yz ∙ ρ) _ et
    g-hom-cong : ∀ {x} {ρ ρ' : Hom x y} (e-hom : ρ ≡ ρ')
                 {γx : Γ ⟨ x ⟩} {eγ-yx : Γ ⟪ ρ ⟫ γy ≈[ Γ ]≈ γx} {eγ-yx' : Γ ⟪ ρ' ⟫ γy ≈[ Γ ]≈ γx}
                 {t : T ⟨ x , γx ⟩} →
                 g ρ eγ-yx t ≈⟦ S ⟧≈ g ρ' eγ-yx' t
    g-hom-cong eρ = $-hom-cong f (cong (ρ-yz ∙_) eρ)
    g-nat : ∀ {w x} {ρ-wx : Hom w x} {ρ-xy : Hom x y} {γx : Γ ⟨ x ⟩} {γw : Γ ⟨ w ⟩}
            (eq-yx : Γ ⟪ ρ-xy ⟫ γy ≈[ Γ ]≈ γx) (eq-xw : Γ ⟪ ρ-wx ⟫ γx ≈[ Γ ]≈ γw) → _
    g-nat {ρ-wx = ρ-wx}{ρ-xy} eγ-yx eγ-xw t =
      begin
        f $⟨ ρ-yz ∙ (ρ-xy ∙ ρ-wx) , strong-rel-comp Γ eγ-zy (strong-rel-comp Γ eγ-yx eγ-xw) ⟩ (T ⟪ ρ-wx , eγ-xw ⟫ t)
      ≈˘⟨ $-hom-cong f ∙assoc ⟩
        f $⟨ (ρ-yz ∙ ρ-xy) ∙ ρ-wx , strong-rel-comp Γ (strong-rel-comp Γ eγ-zy eγ-yx) eγ-xw ⟩ (T ⟪ ρ-wx , eγ-xw ⟫ t)
      ≈⟨ naturality f (strong-rel-comp Γ eγ-zy eγ-yx) eγ-xw t ⟩
        (S ⟪ ρ-wx , eγ-xw ⟫ (f $⟨ ρ-yz ∙ ρ-xy , strong-rel-comp Γ eγ-zy eγ-yx ⟩ t)) ∎
      where open SetoidReasoning (type S _ _)


--------------------------------------------------
-- Definition of the function type + term constructors

_⇛_ : {Γ : Ctx C ℓc rc} → Ty Γ ℓt rt → Ty Γ ℓs rs → Ty Γ (ℓc ⊔ rc ⊔ ℓt ⊔ rt ⊔ ℓs ⊔ rs) (ℓc ⊔ rc ⊔ ℓt ⊔ rs)
Setoid.Carrier (type (_⇛_ {Γ = Γ} T S) z γ) = PresheafFunc T S z γ
Setoid._≈_ (type (_⇛_ {Γ = Γ} T S) z γ) = func≈ T S z γ
Setoid.isEquivalence (type (_⇛_ {Γ = Γ} T S) z γ) = func≈-equiv T S z γ
morph (T ⇛ S) = lower-presheaffunc
morph-cong (T ⇛ S) ρ-zy eγ-zy f=g ρ-yx eγ-yx t = f=g (ρ-zy ∙ ρ-yx) _ t
morph-hom-cong (T ⇛ S) eρ-zy {t = f} ρ-yx eγ-yx t = $-hom-cong f (cong (_∙ ρ-yx) eρ-zy)
morph-id (_⇛_ {Γ = Γ} T S) f _ _ _ = $-hom-cong f hom-idˡ 
morph-comp (_⇛_ {Γ = Γ} T S) _ _ _ _ f _ _ _ = $-hom-cong f ∙assoc

lam : (T : Ty Γ ℓt rt) → Tm (Γ ,, T) (S [ π ]) → Tm Γ (T ⇛ S)
_$⟨_,_⟩_ (term (lam {S = S} T b) z γz) ρ-yz {γy} eγ t = b ⟨ _ , [ γy , t ] ⟩'
$-cong (term (lam {Γ = Γ}{S = S} T b) z γz) {y} ρ-yz {γy} eγ {t1}{t2} et =
  begin
    b ⟨ y , [ γy , t1 ] ⟩'
  ≈˘⟨ morph-id S _ ⟩
    S ⟪ hom-id , _ ⟫ (b ⟨ y , [ γy , t1 ] ⟩')
  ≈⟨ morph-hom-cong S ≡-refl ⟩
    S ⟪ hom-id , _ ⟫ (b ⟨ y , [ γy , t1 ] ⟩')
    -- TODO: tidy up!
  ≈⟨ naturality b hom-id [ rel-id Γ γy , ty≈-trans T (ty≈-trans T (morph-hom-cong-2-1 T hom-idˡ)
                                                                  (morph-id T t1))
                                                     et ] ⟩
    b ⟨ y , [ γy , t2 ] ⟩' ∎
  where open SetoidReasoning (type S y γy)
$-hom-cong (term (lam {S = S} T b) z γz) _ = ty≈-refl S
naturality (term (lam {S = S} T b) z γz) {x = x}{y}{ρ-xy}{_}{γx}{γy} eγ-zy eγ-yx t =
  begin
    b ⟨ x , [ γx , T ⟪ ρ-xy , eγ-yx ⟫ t ] ⟩'
  ≈˘⟨ naturality b ρ-xy [ eγ-yx , morph-hom-cong-2-1 T hom-idʳ ] ⟩
    S ⟪ ρ-xy , _ ⟫ b ⟨ y , [ γy , t ] ⟩'
  ≈⟨ morph-hom-cong S ≡-refl ⟩
    S ⟪ ρ-xy , eγ-yx ⟫ b ⟨ y , [ γy , t ] ⟩' ∎
  where open SetoidReasoning (type S x γx)
naturality (lam {S = S} T b) _ _ _ _ _ = ty≈-refl S

-- An operator used to define function application.
_€⟨_,_⟩_ : Tm Γ (T ⇛ S) → (x : Ob) (γ : Γ ⟨ x ⟩) → T ⟨ x , γ ⟩ → S ⟨ x , γ ⟩
_€⟨_,_⟩_ {Γ = Γ} f x γ t = f ⟨ x , γ ⟩' $⟨ hom-id , rel-id Γ γ ⟩ t

-- TODO: generalization of Γ T and S seems to fail here, see why that is.
€-natural : ∀ {ℓc rc} {Γ : Ctx C ℓc rc}
            {ℓt ℓs rt rs} {T : Ty Γ ℓt rt} {S : Ty Γ ℓs rs}
            (f : Tm Γ (T ⇛ S)) (ρ : Hom x y)
            {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} (eγ : Γ ⟪ ρ ⟫ γy ≈[ Γ ]≈ γx)
            (t : T ⟨ y , γy ⟩) →
            S ⟪ ρ , eγ ⟫ (f €⟨ y , γy ⟩ t) ≈⟦ S ⟧≈ f €⟨ x , γx ⟩ (T ⟪ ρ , eγ ⟫ t)
€-natural {Γ = Γ}{T = T}{S = S} f ρ {γy}{γx} eγ t =
  begin
    S ⟪ ρ , eγ ⟫ (f ⟨ _ , γy ⟩' $⟨ hom-id , rel-id Γ γy ⟩ t)
  ≈˘⟨ naturality (f ⟨ _ , γy ⟩') (rel-id Γ γy) eγ t ⟩
    f ⟨ _ , γy ⟩' $⟨ hom-id ∙ ρ , strong-rel-comp Γ (rel-id Γ γy) eγ ⟩ (T ⟪ ρ , eγ ⟫ t)
  ≈⟨ $-hom-cong (f ⟨ _ , γy ⟩') (≡-trans hom-idˡ (≡-sym hom-idʳ)) ⟩
    f ⟨ _ , γy ⟩' $⟨ ρ ∙ hom-id , strong-rel-comp Γ eγ (rel-id Γ γx) ⟩ (T ⟪ ρ , eγ ⟫ t)
  ≈⟨ naturality f ρ eγ hom-id _ (T ⟪ ρ , eγ ⟫ t) ⟩
    f ⟨ _ , γx ⟩' $⟨ hom-id , rel-id Γ γx ⟩ (T ⟪ ρ , eγ ⟫ t) ∎
  where open SetoidReasoning (type S _ γx)

app : Tm Γ (T ⇛ S) → Tm Γ T → Tm Γ S
term (app f t) y γ = f €⟨ y , γ ⟩ (t ⟨ y , γ ⟩')
naturality (app {Γ = Γ}{T = T}{S = S} f t) ρ {γy}{γx} eγ =
  begin
    S ⟪ ρ , eγ ⟫ (f €⟨ _ , γy ⟩ (t ⟨ _ , γy ⟩'))
  ≈⟨ €-natural f ρ eγ (t ⟨ _ , γy ⟩') ⟩
    f €⟨ _ , γx ⟩ (T ⟪ ρ , eγ ⟫ (t ⟨ _ , γy ⟩'))
  ≈⟨ $-cong (f ⟨ _ , γx ⟩') hom-id _ (naturality t ρ eγ) ⟩
    f €⟨ _ , γx ⟩ (t ⟨ _ , γx ⟩') ∎
  where open SetoidReasoning (type S _ γx)

infixl 12 _$_
_$_ = app


--------------------------------------------------
-- Congruence proofs

pshfun-dimap : ∀ {ℓt ℓt' rt' ℓs ℓs' rs'}
               {T : Ty Γ ℓt rt} {T' : Ty Γ ℓt' rt'} {S : Ty Γ ℓs rs} {S' : Ty Γ ℓs' rs'} →
               (T' ↣ T) → (S ↣ S') →
               (z : Ob) (γ : Γ ⟨ z ⟩) →
               PresheafFunc T S z γ → PresheafFunc T' S' z γ
_$⟨_,_⟩_ (pshfun-dimap η φ _ γ f) ρ eγ t' = func φ (f $⟨ ρ , eγ ⟩ func η t')
$-cong (pshfun-dimap η φ _ γ f) ρ eγ et = func-cong φ ($-cong f ρ eγ (func-cong η et))
$-hom-cong (pshfun-dimap η φ _ γ f) eρ = func-cong φ ($-hom-cong f eρ)
naturality (pshfun-dimap {T = T}{T'}{S}{S'} η φ z γ f) eq-zy eq-yx t' =
  begin
    func φ (f $⟨ _ , _ ⟩ func η (T' ⟪ _ , eq-yx ⟫ t'))
  ≈˘⟨ func-cong φ ($-cong f _ _ (naturality η t')) ⟩
    func φ (f $⟨ _ , _ ⟩ (T ⟪ _ , eq-yx ⟫ func η t'))
  ≈⟨ func-cong φ (naturality f eq-zy eq-yx (func η t')) ⟩
    func φ (S ⟪ _ , eq-yx ⟫ (f $⟨ _ , eq-zy ⟩ func η t'))
  ≈˘⟨ naturality φ _ ⟩
    S' ⟪ _ , eq-yx ⟫ func φ (f $⟨ _ , eq-zy ⟩ func η t') ∎
  where open SetoidReasoning (type S' _ _)

⇛-dimap : (T' ↣ T) → (S ↣ S') → (T ⇛ S ↣ T' ⇛ S')
func (⇛-dimap η φ) = pshfun-dimap η φ _ _
func-cong (⇛-dimap η φ) ef ρ eγ t = func-cong φ (ef ρ eγ (func η t))
naturality (⇛-dimap {S' = S'} η φ) f ρ eγ t = ty≈-refl S'

⇛-cong : T ≅ᵗʸ T' → S ≅ᵗʸ S' → T ⇛ S ≅ᵗʸ T' ⇛ S'
from (⇛-cong T=T' S=S') = ⇛-dimap (to T=T') (from S=S')
to (⇛-cong T=T' S=S') = ⇛-dimap (from T=T') (to S=S')
eq (isoˡ (⇛-cong {S = S} T=T' S=S')) f ρ eγ t = 
  begin
    func (to S=S') (func (from S=S') (f $⟨ ρ , eγ ⟩ func (to T=T') (func (from T=T') t)))
  ≈⟨ eq (isoˡ S=S') _ ⟩
    f $⟨ ρ , eγ ⟩ func (to T=T') (func (from T=T') t)
  ≈⟨ $-cong f ρ eγ (eq (isoˡ T=T') t) ⟩
    f $⟨ ρ , eγ ⟩ t ∎
  where open SetoidReasoning (type S _ _)
eq (isoʳ (⇛-cong {S' = S'} T=T' S=S')) f ρ eγ t' = 
  begin
    func (from S=S') (func (to S=S') (f $⟨ ρ , eγ ⟩ func (from T=T') (func (to T=T') t')))
  ≈⟨ eq (isoʳ S=S') _ ⟩
    f $⟨ ρ , eγ ⟩ func (from T=T') (func (to T=T') t')
  ≈⟨ $-cong f ρ eγ (eq (isoʳ T=T') t') ⟩
    f $⟨ ρ , eγ ⟩ t' ∎
  where open SetoidReasoning (type S' _ _)

lam-cong : (T : Ty Γ ℓ r) {b b' : Tm (Γ ,, T) (S [ π ])} →
           b ≅ᵗᵐ b' → lam T b ≅ᵗᵐ lam T b'
eq (lam-cong T b=b') _ _ {γ'} _ t = eq b=b' [ γ' , t ]

€-cong : {f f' : Tm Γ (T ⇛ S)} {γ : Γ ⟨ z ⟩} {t t' : T ⟨ z , γ ⟩} →
         f ≅ᵗᵐ f' → t ≈⟦ T ⟧≈ t' → f €⟨ z , γ ⟩ t ≈⟦ S ⟧≈ f' €⟨ z , γ ⟩ t'
€-cong {S = S}{z = z}{f = f}{f'}{γ}{t}{t'} f=f' t=t' =
  begin
    f ⟨ z , γ ⟩' $⟨ hom-id , _ ⟩ t
  ≈⟨ $-cong (f ⟨ z , γ ⟩') hom-id _ t=t' ⟩
    f ⟨ z , γ ⟩' $⟨ hom-id , _ ⟩ t'
  ≈⟨ eq f=f' γ hom-id _ t' ⟩
    f' ⟨ z , γ ⟩' $⟨ hom-id , _ ⟩ t' ∎
  where open SetoidReasoning (type S z γ)

app-cong : {f f' : Tm Γ (T ⇛ S)} {t t' : Tm Γ T} →
           f ≅ᵗᵐ f' → t ≅ᵗᵐ t' → app f t ≅ᵗᵐ app f' t'
eq (app-cong {f = f}{f'}{t}{t'} f=f' t=t') γ = €-cong f=f' (eq t=t' γ)

module _ {ℓt ℓt' rt' ℓs ℓs' rs'}
  {T : Ty Γ ℓt rt} {T' : Ty Γ ℓt' rt'} {S : Ty Γ ℓs rs} {S' : Ty Γ ℓs' rs'}
  (T=T' : T ≅ᵗʸ T') (S=S' : S ≅ᵗʸ S')
  where

  lam-ι : (b : Tm (Γ ,, T') (S' [ π ])) →
          ι[ ⇛-cong T=T' S=S' ] (lam T' b) ≅ᵗᵐ
            lam T (ι[ ty-subst-cong-ty π S=S' ] (
                   ι⁻¹[ ty-subst-cong-subst (ctx-ext-subst-proj₁ π (ι⁻¹[ ty-subst-cong-ty π T=T' ] ξ)) S' ] (
                   ι⁻¹[ ty-subst-comp S' π (ty-eq-to-ext-subst Γ T=T') ] (
                   b [ ty-eq-to-ext-subst Γ T=T' ]'))))
  eq (lam-ι b) γ _ _ _ = ty≈-sym S (
    begin
      func (to S=S') (S' ⟪ hom-id , _ ⟫ b ⟨ _ , _ ⟩')
    ≈⟨ func-cong (to S=S') (morph-hom-cong S' ≡-refl) ⟩
      func (to S=S') (S' ⟪ hom-id , _ ⟫ b ⟨ _ , _ ⟩')
    ≈⟨ func-cong (to S=S') (morph-id S' _) ⟩
      func (to S=S') (b ⟨ _ , _ ⟩') ∎)
    where open SetoidReasoning (type S _ _)

  app-ι : (f : Tm Γ (T' ⇛ S')) (t : Tm Γ T') → app (ι[ ⇛-cong T=T' S=S' ] f) (ι[ T=T' ] t) ≅ᵗᵐ ι[ S=S' ] (app f t)
  eq (app-ι f t) γ = func-cong (to S=S') ($-cong (f ⟨ _ , γ ⟩') hom-id _ (eq (isoʳ T=T') (t ⟨ _ , γ ⟩')))


--------------------------------------------------
-- Naturality proofs

module _ (σ : Δ ⇒ Γ) (T : Ty Γ ℓt rt) (S : Ty Γ ℓs rs) {δ : Δ ⟨ z ⟩} where
  pshfun-subst-from : PresheafFunc T S z (func σ δ) → PresheafFunc (T [ σ ]) (S [ σ ]) z δ
  _$⟨_,_⟩_ (pshfun-subst-from f) ρ-yz eδ t = f $⟨ ρ-yz , ctx≈-trans Γ (naturality σ δ) (func-cong σ eδ) ⟩ t
  $-cong (pshfun-subst-from f) ρ eγ et = $-cong f ρ _ et
  $-hom-cong (pshfun-subst-from f) eρ = $-hom-cong f eρ
  naturality (pshfun-subst-from f) _ _ t = ty≈-trans S ($-hom-cong f ≡-refl) (naturality f _ _ t)

  pshfun-subst-to : PresheafFunc (T [ σ ]) (S [ σ ]) z δ → PresheafFunc T S z (func σ δ)
  _$⟨_,_⟩_ (pshfun-subst-to f) ρ-yz {γ'} eδ t = ctx-element-subst S proof (
                                                 f $⟨ ρ-yz , ctx≈-refl Δ ⟩
                                                 ctx-element-subst T (ctx≈-sym Γ proof) t)
    where
      proof : func σ (Δ ⟪ ρ-yz ⟫ δ) ≈[ Γ ]≈ γ'
      proof = ctx≈-trans Γ (ctx≈-sym Γ (naturality σ δ)) eδ
  $-cong (pshfun-subst-to f) ρ eγ et = morph-cong S hom-id _ ($-cong f ρ _ (morph-cong T hom-id _ et))
  $-hom-cong (pshfun-subst-to f) ≡-refl = ty≈-trans S (ty≈-trans S (morph-hom-cong S ≡-refl)
                                                                   (morph-cong S hom-id _ ($-hom-cong f ≡-refl)))
                                                      (morph-cong S hom-id _ ($-cong f _ _ (morph-hom-cong T ≡-refl)))
  naturality (pshfun-subst-to f) {ρ-xy = ρ-xy}{ρ-yz} _ eq-yx t =
    begin
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , ctx≈-refl Δ ⟩ (T ⟪ hom-id , _ ⟫ T ⟪ ρ-xy , eq-yx ⟫ t)
    ≈⟨ morph-cong S hom-id α ($-cong f (ρ-yz ∙ ρ-xy) (ctx≈-refl Δ) (morph-hom-cong-2-2 T (≡-trans hom-idʳ (≡-sym hom-idˡ)))) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , ctx≈-refl Δ ⟩ (T ⟪ ρ-xy , _ ⟫ (T ⟪ hom-id , β ⟫ t))
    ≈⟨ morph-cong S hom-id α ($-hom-cong f ≡-refl) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , _ ⟩ (T ⟪ ρ-xy , _ ⟫ (T ⟪ hom-id , β ⟫ t))
    ≈⟨ morph-cong S hom-id α (naturality f (ctx≈-refl Δ) (ctx≈-sym Δ (rel-comp Δ ρ-xy ρ-yz δ)) _) ⟩
      S ⟪ hom-id , α ⟫ S ⟪ ρ-xy , _ ⟫ f $⟨ ρ-yz , ctx≈-refl Δ ⟩ (T ⟪ hom-id , β ⟫ t)
    ≈⟨ morph-hom-cong-2-2 S (≡-trans hom-idʳ (≡-sym hom-idˡ)) ⟩
      S ⟪ ρ-xy , eq-yx ⟫ S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , ctx≈-refl Δ ⟩ (T ⟪ hom-id , β ⟫ t) ∎
    where
      open SetoidReasoning (type S _ _)
      α = _
      β = _

module _ {T : Ty Γ ℓt rt} {S : Ty Γ ℓs rs} (σ : Δ ⇒ Γ) where
  ⇛-natural : (T ⇛ S) [ σ ] ≅ᵗʸ (T [ σ ]) ⇛ (S [ σ ])
  func (from ⇛-natural) = pshfun-subst-from σ T S
  func-cong (from ⇛-natural) ef ρ eγ t = ef ρ _ t
  naturality (from ⇛-natural) f _ _ _ = $-hom-cong f ≡-refl
  func (to ⇛-natural) = pshfun-subst-to σ T S
  func-cong (to ⇛-natural) ef ρ eγ t = morph-cong S hom-id _ (ef ρ _ _)
  naturality (to ⇛-natural) {_} {_} {ρ-yz} f ρ-xy eγ t =
    let α = _
        β = _
        ζ = _
        α' = _
        β' = _
        ζ' = _
    in begin
        S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , β ⟩ (T ⟪ hom-id , ζ ⟫ t)
      ≈˘⟨ morph-cong S hom-id α ($-cong f (ρ-yz ∙ ρ-xy) β (morph-hom-cong-2-1 T hom-idˡ)) ⟩
        S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , β ⟩ (T ⟪ hom-id , _ ⟫ (T ⟪ hom-id , ζ' ⟫ t))
      ≈⟨ morph-cong S hom-id α ($-hom-cong f (≡-sym hom-idʳ)) ⟩
        S ⟪ hom-id , α ⟫ f $⟨ (ρ-yz ∙ ρ-xy) ∙ hom-id , _ ⟩ (T ⟪ hom-id , _ ⟫ (T ⟪ hom-id , ζ' ⟫ t))
      ≈⟨ morph-cong S hom-id α (naturality f _ (ctx≈-trans Δ (rel-id Δ _) (ctx≈-sym Δ β')) _) ⟩
        S ⟪ hom-id , α ⟫ S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz ∙ ρ-xy , β' ⟩ (T ⟪ hom-id , ζ' ⟫ t)
      ≈⟨ morph-hom-cong-2-1 S hom-idˡ ⟩
        S ⟪ hom-id , α' ⟫ f $⟨ ρ-yz ∙ ρ-xy , β' ⟩ (T ⟪ hom-id , ζ' ⟫ t) ∎
    where open SetoidReasoning (type S _ _)
  eq (isoˡ ⇛-natural) f ρ-yz eγ t = 
    begin
      S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , _ ⟩ (T ⟪ hom-id , _ ⟫ t)
    ≈⟨ morph-cong S hom-id _ ($-hom-cong f (≡-sym hom-idʳ)) ⟩
      S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz ∙ hom-id , _ ⟩ (T ⟪ hom-id , _ ⟫ t)
    ≈⟨ morph-cong S hom-id _(naturality f eγ _ t) ⟩
      S ⟪ hom-id , _ ⟫ S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , eγ ⟩ t
    ≈⟨ morph-hom-cong-2-1 S hom-idˡ ⟩
      S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , eγ ⟩ t
    ≈⟨ morph-id S _ ⟩
      f $⟨ ρ-yz , eγ ⟩ t ∎
    where open SetoidReasoning (type S _ _)
  eq (isoʳ ⇛-natural) f ρ-yz eδ t =
    let α = ctx≈-trans Δ (rel-id Δ _) (ctx≈-sym Δ eδ)
        β = _
    in  begin
      S ⟪ hom-id , β ⟫ f $⟨ ρ-yz , ctx≈-refl Δ ⟩ (T ⟪ hom-id , _ ⟫ t)
    ≈⟨ morph-cong S hom-id β ($-hom-cong f (≡-sym hom-idʳ)) ⟩
      S ⟪ hom-id , β ⟫ f $⟨ ρ-yz ∙ hom-id , _ ⟩ (T ⟪ hom-id , _ ⟫ t)
    ≈⟨ morph-cong S hom-id β ($-cong f (ρ-yz ∙ hom-id) _(morph-hom-cong T ≡-refl)) ⟩
      S ⟪ hom-id , β ⟫ f $⟨ ρ-yz ∙ hom-id , _ ⟩ (T [ σ ] ⟪ hom-id , α ⟫ t)
    ≈⟨ morph-cong S hom-id _ (naturality f eδ _ t) ⟩
      S ⟪ hom-id , β ⟫ S [ σ ] ⟪ hom-id , α ⟫ f $⟨ ρ-yz , eδ ⟩ t
    ≈⟨ morph-hom-cong-2-1 S hom-idˡ ⟩
      S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , eδ ⟩ t
    ≈⟨ morph-id S _ ⟩
      f $⟨ ρ-yz , eδ ⟩ t ∎
    where open SetoidReasoning (type S _ _)

  lam-natural : (b : Tm (Γ ,, T) (S [ π ])) →
                (lam T b) [ σ ]' ≅ᵗᵐ
                  ι[ ⇛-natural ] (
                  lam (T [ σ ]) (ι⁻¹[ ty-subst-seq-cong (π ∷ σ ⊹ ◼) (σ ∷ π ◼) S (⊹-π-comm σ) ] (b [ σ ⊹ ]')))
  eq (lam-natural b) δ ρ {γ'} eγ t = ty≈-sym S (
    let α = ty≈-trans T (ty≈-trans T (morph-hom-cong-2-1 T hom-idˡ {eh = ctx≈-trans Γ (rel-id Γ _) (ctx≈-trans Γ (ctx≈-sym Γ (naturality σ δ)) eγ)})
                                     (morph-hom-cong-2-1 T hom-idˡ))
                        (morph-id T t)
    in begin
      S ⟪ hom-id , _ ⟫ S ⟪ hom-id , _ ⟫ b ⟨ _ , [ func σ (Δ ⟪ ρ ⟫ δ) , T ⟪ hom-id , _ ⟫ t ] ⟩'
    ≈⟨ morph-hom-cong-2-1 S hom-idˡ ⟩
      S ⟪ hom-id , _ ⟫ b ⟨ _ , [ func σ (Δ ⟪ ρ ⟫ δ) , T ⟪ hom-id , _ ⟫ t ] ⟩'
    ≈⟨ naturality b hom-id [ ctx≈-trans Γ (rel-id Γ _) (ctx≈-trans Γ (ctx≈-sym Γ (naturality σ δ)) eγ) , α ] ⟩
      b ⟨ _ , [ γ' , t ] ⟩' ∎)
    where
      open SetoidReasoning (type S _ _)

  app-natural : (f : Tm Γ (T ⇛ S)) (t : Tm Γ T) →
                (app f t) [ σ ]' ≅ᵗᵐ app (ι⁻¹[ ⇛-natural ] (f [ σ ]')) (t [ σ ]')
  eq (app-natural f t) δ = $-hom-cong (f ⟨ _ , func σ δ ⟩') ≡-refl


--------------------------------------------------
-- Relation between functions T ⇛ S and natural tranformations T ↣ S

⇛-to-↣ : Tm Γ (T ⇛ S) → (T ↣ S)
func (⇛-to-↣ f) = f €⟨ _ , _ ⟩_
func-cong (⇛-to-↣ f) = $-cong (f ⟨ _ , _ ⟩') hom-id _
naturality (⇛-to-↣ f) t = €-natural f _ _ t

↣-to-⇛ : (T ↣ S) → Tm Γ (T ⇛ S)
(term (↣-to-⇛ η) _ _) $⟨ _ , _ ⟩ t = func η t
$-cong (term (↣-to-⇛ η) _ _) _ _ = func-cong η
$-hom-cong (term (↣-to-⇛ {S = S} η) _ _) _ = ty≈-refl S
naturality (term (↣-to-⇛ {S = S} η) _ _) _ _ t = ty≈-sym S (naturality η t)
naturality (↣-to-⇛ {S = S} η) _ _ _ _ _ = ty≈-refl S

↣-⇛-iso : (η : T ↣ S) → ⇛-to-↣ (↣-to-⇛ η) ≅ⁿ η
eq (↣-⇛-iso {S = S} η) _ = ty≈-refl S

⇛-↣-iso : (f : Tm Γ (T ⇛ S)) → ↣-to-⇛ (⇛-to-↣ f) ≅ᵗᵐ f
eq (⇛-↣-iso {Γ = Γ}{S = S} f) {x} γ {y} ρ {γ'} eγ t =
  begin
    f ⟨ y , γ' ⟩' $⟨ hom-id , rel-id Γ γ' ⟩ t
  ≈˘⟨ naturality f ρ eγ hom-id (rel-id Γ γ') t ⟩
    f ⟨ x , γ ⟩' $⟨ ρ ∙ hom-id , strong-rel-comp Γ eγ (rel-id Γ γ') ⟩ t
  ≈⟨ $-hom-cong (f ⟨ x , γ ⟩') hom-idʳ ⟩
    f ⟨ x , γ ⟩' $⟨ ρ , eγ ⟩ t ∎
  where open SetoidReasoning (type S y γ')


--------------------------------------------------
-- Alternative version of lambda abstraction that allows to name the bound variable

nlam[_∈_]_ : (v : String) (T : Ty Γ ℓt rt) → Tm (Γ ,, v ∈ T) (S [ π ]) → Tm Γ (T ⇛ S)
nlam[_∈_]_ v = lam
