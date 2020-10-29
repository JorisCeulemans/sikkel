--------------------------------------------------
-- (Non-dependent) function types
--------------------------------------------------

open import Categories

module Types.Functions {C : Category} where

open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Function
open import Level
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality) renaming (refl to ≡-refl)

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
{-
infixr 12 _⇛_

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
$-cong (term (lam {S = S} T b) z γz) ρ-yz eγ et = {!naturality b!}
$-hom-cong (term (lam {S = S} T b) z γz) _ = ty≈-refl S
naturality (term (lam {S = S} T b) z γz) {x = x}{y}{ρ-xy}{_}{γx}{γy} eγ-zy eγ-yx t =
  begin
    b ⟨ x , [ γx , T ⟪ ρ-xy , eγ-yx ⟫ t ] ⟩'
  ≈˘⟨ naturality b ρ-xy [ eγ-yx , ty≈-trans T (ty≈-sym T (morph-comp T hom-id ρ-xy _ _ t)) {!!} ] ⟩
    S ⟪ ρ-xy , _ ⟫ b ⟨ y , [ γy , t ] ⟩'
  ≈⟨ morph-hom-cong S ≡-refl ⟩
    S ⟪ ρ-xy , eγ-yx ⟫ b ⟨ y , [ γy , t ] ⟩' ∎
  where open SetoidReasoning (type S x γx)
naturality (lam {S = S} T b) _ _ _ _ _ = ty≈-refl S
{-
-- An operator used to define function application.
_€⟨_,_⟩_ : Tm Γ (T ⇛ S) → (x : Ob) (γ : Γ ⟨ x ⟩) → T ⟨ x , γ ⟩ → S ⟨ x , γ ⟩
_€⟨_,_⟩_ {Γ = Γ} f x γ t = f ⟨ x , γ ⟩' $⟨ hom-id , rel-id Γ γ ⟩ t

€-natural : (f : Tm Γ (T ⇛ S)) (ρ : Hom x y)
            {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} (eγ : Γ ⟪ ρ ⟫ γy ≡ γx)
            (t : T ⟨ y , γy ⟩) →
            S ⟪ ρ , eγ ⟫ (f €⟨ y , γy ⟩ t) ≡ f €⟨ x , γx ⟩ (T ⟪ ρ , eγ ⟫ t)
€-natural {Γ = Γ}{T = T}{S = S} f ρ {γy}{γx} eγ t =
  begin
    S ⟪ ρ , eγ ⟫ (f ⟨ _ , γy ⟩' $⟨ hom-id , rel-id Γ γy ⟩ t)
  ≡⟨ sym (naturality (f ⟨ _ , γy ⟩') (rel-id Γ γy) eγ t) ⟩
    f ⟨ _ , γy ⟩' $⟨ hom-id ∙ ρ , strong-rel-comp Γ (rel-id Γ γy) eγ ⟩ (T ⟪ ρ , eγ ⟫ t)
  ≡⟨ $-cong (f ⟨ _ , γy ⟩') (trans hom-idˡ (sym hom-idʳ)) _ _ ⟩
    f ⟨ _ , γy ⟩' $⟨ ρ ∙ hom-id , strong-rel-comp Γ eγ (rel-id Γ γx) ⟩ (T ⟪ ρ , eγ ⟫ t)
  ≡⟨ cong (λ x → x $⟨ _ , _ ⟩ _) (naturality f ρ eγ) ⟩
    f ⟨ _ , γx ⟩' $⟨ hom-id , rel-id Γ γx ⟩ (T ⟪ ρ , eγ ⟫ t) ∎
  where open ≡-Reasoning

app : Tm Γ (T ⇛ S) → Tm Γ T → Tm Γ S
term (app f t) y γ = f €⟨ y , γ ⟩ (t ⟨ y , γ ⟩')
naturality (app {Γ = Γ}{T = T}{S = S} f t) ρ {γy}{γx} eγ =
  begin
    S ⟪ ρ , eγ ⟫ (f €⟨ _ , γy ⟩ (t ⟨ _ , γy ⟩'))
  ≡⟨ €-natural f ρ eγ (t ⟨ _ , γy ⟩') ⟩
    f €⟨ _ , γx ⟩ (T ⟪ ρ , eγ ⟫ (t ⟨ _ , γy ⟩'))
  ≡⟨ cong (f €⟨ _ , γx ⟩_) (naturality t ρ eγ) ⟩
    f €⟨ _ , γx ⟩ (t ⟨ _ , γx ⟩') ∎
  where open ≡-Reasoning


--------------------------------------------------
-- Congruence proofs

pshfun-dimap : ∀ {ℓt ℓt' ℓs ℓs'}
               {T : Ty Γ ℓt} {T' : Ty Γ ℓt'} {S : Ty Γ ℓs} {S' : Ty Γ ℓs'} →
               (T' ↣ T) → (S ↣ S') →
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

⇛-dimap : (T' ↣ T) → (S ↣ S') → (T ⇛ S ↣ T' ⇛ S')
func (⇛-dimap η φ) = pshfun-dimap η φ _ _
naturality (⇛-dimap η φ) f = to-pshfun-eq λ _ _ _ → refl

⇛-cong : T ≅ᵗʸ T' → S ≅ᵗʸ S' → T ⇛ S ≅ᵗʸ T' ⇛ S'
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

lam-cong : (T : Ty Γ ℓ) {b b' : Tm (Γ ,, T) (S [ π ])} →
           b ≅ᵗᵐ b' → lam T b ≅ᵗᵐ lam T b'
eq (lam-cong T b=b') γ = to-pshfun-eq (λ _ {γ'} _ t → eq b=b' [ γ' , t ])

€-cong : {f f' : Tm Γ (T ⇛ S)} {γ : Γ ⟨ z ⟩} {t t' : T ⟨ z , γ ⟩} →
         f ≅ᵗᵐ f' → t ≡ t' → f €⟨ z , γ ⟩ t ≡ f' €⟨ z , γ ⟩ t'
€-cong {z = z}{f = f}{f'}{γ}{t}{t'} f=f' t=t' =
  begin
    f ⟨ z , γ ⟩' $⟨ hom-id , _ ⟩ t
  ≡⟨ cong (f ⟨ z , γ ⟩' $⟨ hom-id , _ ⟩_) t=t' ⟩
    f ⟨ z , γ ⟩' $⟨ hom-id , _ ⟩ t'
  ≡⟨ cong (_$⟨ hom-id , _ ⟩ t') (eq f=f' γ) ⟩
    f' ⟨ z , γ ⟩' $⟨ hom-id , _ ⟩ t' ∎
  where open ≡-Reasoning

app-cong : {f f' : Tm Γ (T ⇛ S)} {t t' : Tm Γ T} →
           f ≅ᵗᵐ f' → t ≅ᵗᵐ t' → app f t ≅ᵗᵐ app f' t'
eq (app-cong {f = f}{f'}{t}{t'} f=f' t=t') γ = €-cong f=f' (eq t=t' γ)

module _ {ℓt ℓt' ℓs ℓs'}
  {T : Ty Γ ℓt} {T' : Ty Γ ℓt'} {S : Ty Γ ℓs} {S' : Ty Γ ℓs'}
  (T=T' : T ≅ᵗʸ T') (S=S' : S ≅ᵗʸ S')
  where
  
  lam-ι : (b : Tm (Γ ,, T') (S' [ π ])) →
          ι[ ⇛-cong T=T' S=S' ] (lam T' b) ≅ᵗᵐ
            lam T (ι[ ty-subst-cong-ty π S=S' ] (
                   ι⁻¹[ ty-subst-cong-subst (ctx-ext-subst-proj₁ π (ι⁻¹[ ty-subst-cong-ty π T=T' ] ξ)) S' ] (
                   ι⁻¹[ ty-subst-comp S' π (ty-eq-to-ext-subst Γ T=T') ] (
                   b [ ty-eq-to-ext-subst Γ T=T' ]'))))
  eq (lam-ι b) γ = to-pshfun-eq (λ _ _ _ → sym(
    begin
      func (to S=S') (S' ⟪ hom-id , _ ⟫ b ⟨ _ , _ ⟩')
    ≡⟨ cong (func (to S=S')) (morph-cong S' refl) ⟩
      func (to S=S') (S' ⟪ hom-id , _ ⟫ b ⟨ _ , _ ⟩')
    ≡⟨ cong (func (to S=S')) (morph-id S' _) ⟩
      func (to S=S') (b ⟨ _ , _ ⟩') ∎))
    where open ≡-Reasoning

  app-ι : (f : Tm Γ (T' ⇛ S')) (t : Tm Γ T') → app (ι[ ⇛-cong T=T' S=S' ] f) (ι[ T=T' ] t) ≅ᵗᵐ ι[ S=S' ] (app f t)
  eq (app-ι f t) γ = cong (func (to S=S') ∘ f ⟨ _ , γ ⟩' $⟨ hom-id , _ ⟩_) (eq (isoʳ T=T') (t ⟨ _ , γ ⟩'))


--------------------------------------------------
-- Naturality proofs

module _ (σ : Δ ⇒ Γ) (T : Ty Γ ℓt) (S : Ty Γ ℓs) {δ : Δ ⟨ z ⟩} where
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
    ≡⟨ cong (S ⟪ hom-id , α ⟫ ∘ f $⟨ ρ-yz ∙ ρ-xy , refl ⟩_) (morph-cong T (trans hom-idʳ (sym hom-idˡ))) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , refl ⟩ (T ⟪ hom-id ∙ ρ-xy , _ ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , α ⟫ ∘ f $⟨ ρ-yz ∙ ρ-xy , refl ⟩_) (morph-comp T ρ-xy hom-id _ _ t) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , refl ⟩ (T ⟪ ρ-xy , _ ⟫ (T ⟪ hom-id , β ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫) ($-cong f refl refl _) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , _ ⟩ (T ⟪ ρ-xy , _ ⟫ (T ⟪ hom-id , β ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫) (naturality f refl (sym (rel-comp Δ ρ-xy ρ-yz δ)) _) ⟩
      S ⟪ hom-id , α ⟫ S ⟪ ρ-xy , _ ⟫ f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , β ⟫ t)
    ≡˘⟨ morph-comp S hom-id ρ-xy _ α _ ⟩
      S ⟪ ρ-xy ∙ hom-id , _ ⟫ f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , β ⟫ t)
    ≡⟨ morph-cong S (trans hom-idʳ (sym hom-idˡ)) ⟩
      S ⟪ hom-id ∙ ρ-xy , _ ⟫ f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , β ⟫ t)
    ≡⟨ morph-comp S ρ-xy hom-id _ eq-yx _ ⟩
      S ⟪ ρ-xy , eq-yx ⟫ S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , β ⟫ t) ∎
    where
      open ≡-Reasoning
      α = _
      β = _

module _ {T : Ty Γ ℓt} {S : Ty Γ ℓs} (σ : Δ ⇒ Γ) where
  ⇛-natural : (T ⇛ S) [ σ ] ≅ᵗʸ (T [ σ ]) ⇛ (S [ σ ])
  func (from ⇛-natural) = pshfun-subst-from σ T S
  naturality (from ⇛-natural) f = to-pshfun-eq (λ _ _ _ → $-cong f refl _ _)
  func (to ⇛-natural) = pshfun-subst-to σ T S
  naturality (to ⇛-natural) {_} {_} {ρ-yz} f = to-pshfun-eq λ ρ-xy eγ t →
    let α = _
        β = _
        ζ = _
        α' = _
        β' = _
        ζ' = _
    in begin
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , β ⟩ (T ⟪ hom-id , ζ ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , α ⟫ ∘ f $⟨ ρ-yz ∙ ρ-xy , β ⟩_) (morph-cong T (sym hom-idʳ)) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , β ⟩ (T ⟪ hom-id ∙ hom-id , _ ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , α ⟫ ∘ f $⟨ ρ-yz ∙ ρ-xy , β ⟩_) (morph-comp T _ _ ζ' _ t) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , β ⟩ (T ⟪ hom-id , _ ⟫ (T ⟪ hom-id , ζ' ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫) ($-cong f (sym hom-idʳ) refl _) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ (ρ-yz ∙ ρ-xy) ∙ hom-id , _ ⟩ (T ⟪ hom-id , _ ⟫ (T ⟪ hom-id , ζ' ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫) (naturality f _ (trans (rel-id Δ _) (sym β')) _) ⟩
      S ⟪ hom-id , α ⟫ S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz ∙ ρ-xy , β' ⟩ (T ⟪ hom-id , ζ' ⟫ t)
    ≡˘⟨ morph-comp S _ _ _ _ _ ⟩
      S ⟪ hom-id ∙ hom-id , _ ⟫ f $⟨ ρ-yz ∙ ρ-xy , β' ⟩ (T ⟪ hom-id , ζ' ⟫ t)
    ≡⟨ morph-cong S hom-idʳ ⟩
      S ⟪ hom-id , α' ⟫ f $⟨ ρ-yz ∙ ρ-xy , β' ⟩ (T ⟪ hom-id , ζ' ⟫ t) ∎
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
    ≡⟨ morph-cong S hom-idʳ ⟩
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
    ≡⟨ cong (S ⟪ hom-id , β ⟫ ∘ f $⟨ ρ-yz ∙ hom-id , _ ⟩_) (morph-cong T refl) ⟩
      S ⟪ hom-id , β ⟫ f $⟨ ρ-yz ∙ hom-id , _ ⟩ (T [ σ ] ⟪ hom-id , α ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , _ ⟫) (naturality f eδ _ t) ⟩
      S ⟪ hom-id , β ⟫ S [ σ ] ⟪ hom-id , α ⟫ f $⟨ ρ-yz , eδ ⟩ t
    ≡˘⟨ morph-comp S _ _ _ _ _ ⟩
      S ⟪ hom-id ∙ hom-id , _ ⟫ f $⟨ ρ-yz , eδ ⟩ t
    ≡⟨ morph-cong S hom-idʳ ⟩
      S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , eδ ⟩ t
    ≡⟨ morph-id S _ ⟩
      f $⟨ ρ-yz , eδ ⟩ t ∎)
    where open ≡-Reasoning

  lam-natural : (b : Tm (Γ ,, T) (S [ π ])) →
                (lam T b) [ σ ]' ≅ᵗᵐ
                  ι[ ⇛-natural ] (
                  lam (T [ σ ]) (ι⁻¹[ ty-subst-seq-cong (π ∷ σ ⊹ ◼) (σ ∷ π ◼) S (⊹-π-comm σ) ] (b [ σ ⊹ ]')))
  eq (lam-natural b) δ = to-pshfun-eq (λ ρ {γ'} eγ t → sym (
    let α = begin
              transport (λ - → T ⟨ _ , - ⟩) _ (T ⟪ hom-id , _ ⟫ T ⟪ hom-id , _ ⟫ t)
            ≡⟨ morph-transport T refl _ _ ⟩
              T ⟪ hom-id , _ ⟫ T ⟪ hom-id , _ ⟫ t
            ≡˘⟨ morph-comp T hom-id hom-id _ _ t ⟩
              T ⟪ hom-id ∙ hom-id , _ ⟫ t
            ≡⟨ morph-cong T hom-idʳ ⟩
              T ⟪ hom-id , _ ⟫ t
            ≡⟨ morph-id T t ⟩
              t ∎
    in begin
      S ⟪ hom-id , _ ⟫ S ⟪ hom-id , _ ⟫ b ⟨ _ , [ func σ (Δ ⟪ ρ ⟫ δ) , T ⟪ hom-id , _ ⟫ t ] ⟩'
    ≡˘⟨ morph-comp S hom-id hom-id _ _ _ ⟩
      S ⟪ hom-id ∙ hom-id , _ ⟫ b ⟨ _ , [ func σ (Δ ⟪ ρ ⟫ δ) , T ⟪ hom-id , _ ⟫ t ] ⟩'
    ≡⟨ morph-cong S hom-idʳ ⟩
      S ⟪ hom-id , _ ⟫ b ⟨ _ , [ func σ (Δ ⟪ ρ ⟫ δ) , T ⟪ hom-id , _ ⟫ t ] ⟩'
    ≡⟨ naturality b hom-id (to-Σ-eq (trans (rel-id Γ _) (trans (sym (naturality σ δ)) eγ)) α) ⟩
      b ⟨ _ , [ γ' , t ] ⟩' ∎))
    where open ≡-Reasoning

  app-natural : (f : Tm Γ (T ⇛ S)) (t : Tm Γ T) →
                (app f t) [ σ ]' ≅ᵗᵐ app (ι⁻¹[ ⇛-natural ] (f [ σ ]')) (t [ σ ]')
  eq (app-natural f t) δ = $-cong (f ⟨ _ , func σ δ ⟩') refl _ _


--------------------------------------------------
-- Relation between functions T ⇛ S and natural tranformations T ↣ S

⇛-to-↣ : Tm Γ (T ⇛ S) → (T ↣ S)
func (⇛-to-↣ f) = f €⟨ _ , _ ⟩_
naturality (⇛-to-↣ f) t = €-natural f _ _ t

↣-to-⇛ : (T ↣ S) → Tm Γ (T ⇛ S)
(term (↣-to-⇛ η) _ _) $⟨ _ , _ ⟩ t = func η t
naturality (term (↣-to-⇛ η) _ _) _ _ t = sym (naturality η t)
naturality (↣-to-⇛ η) _ _ = to-pshfun-eq (λ _ _ _ → refl)

↣-⇛-iso : (η : T ↣ S) → ⇛-to-↣ (↣-to-⇛ η) ≅ⁿ η
eq (↣-⇛-iso η) _ = refl

⇛-↣-iso : (f : Tm Γ (T ⇛ S)) → ↣-to-⇛ (⇛-to-↣ f) ≅ᵗᵐ f
eq (⇛-↣-iso {Γ = Γ} f) {x} γ = to-pshfun-eq (λ {y} ρ {γ'} eγ t →
  begin
    f ⟨ y , γ' ⟩' $⟨ hom-id , rel-id Γ γ' ⟩ t
  ≡˘⟨ cong (_$⟨ hom-id , rel-id Γ γ' ⟩ t) (naturality f ρ eγ) ⟩
    f ⟨ x , γ ⟩' $⟨ ρ ∙ hom-id , strong-rel-comp Γ eγ (rel-id Γ γ') ⟩ t
  ≡⟨ $-cong (f ⟨ x , γ ⟩') hom-idʳ (strong-rel-comp Γ eγ (rel-id Γ γ')) eγ ⟩
    f ⟨ x , γ ⟩' $⟨ ρ , eγ ⟩ t ∎)
  where open ≡-Reasoning
-}
