--------------------------------------------------
-- (Non-dependent) function types
--------------------------------------------------

open import Model.BaseCategory

module Model.Type.Function {C : BaseCategory} where

open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.String
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.Helpers
open import Model.CwF-Structure
open import Model.CwF-Structure.Reflection.SubstitutionSequence
open BaseCategory C

private
  variable
    x y z : Ob
    Γ Δ : Ctx C
    T T' S S' : Ty Γ

infixr 12 _⇛_
infixr 4 lam[_∈_]_


--------------------------------------------------
-- Description of a function type at a specific stage (object of the base category)

record PshFun {Γ : Ctx C} (T : Ty Γ) (S : Ty Γ) (z : Ob) (γ : Γ ⟨ z ⟩) : Set where
  constructor MkFun
  field
    _$⟨_,_⟩_ : ∀ {y} (ρ : Hom y z) {γ' : Γ ⟨ y ⟩} (eγ : Γ ⟪ ρ ⟫ γ ≡ γ') →
               T ⟨ y , γ' ⟩ → S ⟨ y , γ' ⟩
    naturality : ∀ {x y} {ρ-xy : Hom x y} {ρ-yz : Hom y z} {γx : Γ ⟨ x ⟩} {γy : Γ ⟨ y ⟩} →
                 {eγ-zy : Γ ⟪ ρ-yz ⟫ γ ≡ γy} {eγ-yx : Γ ⟪ ρ-xy ⟫ γy ≡ γx} {t : T ⟨ y , γy ⟩} →
                 _$⟨_,_⟩_ (ρ-yz ∙ ρ-xy) (strong-ctx-comp Γ eγ-zy eγ-yx) (T ⟪ ρ-xy , eγ-yx ⟫ t) ≡
                   S ⟪ ρ-xy , eγ-yx ⟫ (_$⟨_,_⟩_ ρ-yz eγ-zy t)
  infix 13 _$⟨_,_⟩_
open PshFun public

-- Here we make again use of uip by pattern matching on both equality proofs.
$-cong : {T : Ty Γ} {S : Ty Γ}
         {γx : Γ ⟨ x ⟩} {γy : Γ ⟨ y ⟩} (f : PshFun T S y γy)
         {ρ ρ' : Hom x y} (eρ : ρ ≡ ρ')
         {eγ : Γ ⟪ ρ ⟫ γy ≡ γx} {eγ' : Γ ⟪ ρ' ⟫ γy ≡ γx}
         {t : T ⟨ x , γx ⟩} →
         f $⟨ ρ , eγ ⟩ t ≡ f $⟨ ρ' , eγ' ⟩ t
$-cong f refl {eγ = refl} {eγ' = refl} = refl

-- This is one of the few places where we use function extensionality.
to-pshfun-eq : {T : Ty Γ} {S : Ty Γ}
               {γ : Γ ⟨ y ⟩} {f g : PshFun T S y γ} →
               (∀ {x} (ρ : Hom x y) {γ'} (eγ : Γ ⟪ ρ ⟫ γ ≡ γ') t →
                   f $⟨ ρ , eγ ⟩ t ≡ g $⟨ ρ , eγ ⟩ t) →
               f ≡ g
to-pshfun-eq e = cong₂-d MkFun
  (funextI (funext (λ ρ → funextI (funext λ eq → funext λ t → e ρ eq t))))
  (funextI (funextI (funextI (funextI (funextI (funextI (funextI (funextI (funextI (uip _ _))))))))))

-- This will be used to define the action of a function type on morphisms.
lower-presheaffunc : {T : Ty Γ} {S : Ty Γ} (ρ-yz : Hom y z)
                     {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} (eγ : Γ ⟪ ρ-yz ⟫ γz ≡ γy) →
                     PshFun T S z γz → PshFun T S y γy
lower-presheaffunc {Γ = Γ}{y = y}{z = z}{T = T}{S = S} ρ-yz {γz}{γy} eγ-zy f = MkFun g g-nat
  where
    g : ∀ {x} (ρ-xy : Hom x y) {γx} (eγ-yx : Γ ⟪ ρ-xy ⟫ γy ≡ γx) →
        T ⟨ x , γx ⟩ → S ⟨ x , γx ⟩
    g ρ-xy eγ-yx = f $⟨ ρ-yz ∙ ρ-xy , strong-ctx-comp Γ eγ-zy eγ-yx ⟩_
    open ≡-Reasoning
    g-nat : ∀ {w x} {ρ-wx : Hom w x} {ρ-xy : Hom x y} {γx : Γ ⟨ x ⟩} {γw : Γ ⟨ w ⟩}
            {eγ-yx : Γ ⟪ ρ-xy ⟫ γy ≡ γx} {eγ-xw : Γ ⟪ ρ-wx ⟫ γx ≡ γw} {t : T ⟨ x , γx ⟩} → _
    g-nat {ρ-wx = ρ-wx}{ρ-xy}{eγ-yx = eγ-yx}{eγ-xw}{t = t} =
      begin
        f $⟨ ρ-yz ∙ (ρ-xy ∙ ρ-wx) , strong-ctx-comp Γ eγ-zy (strong-ctx-comp Γ eγ-yx eγ-xw) ⟩ (T ⟪ ρ-wx , eγ-xw ⟫ t)
      ≡˘⟨ $-cong f ∙assoc ⟩
        f $⟨ (ρ-yz ∙ ρ-xy) ∙ ρ-wx , strong-ctx-comp Γ (strong-ctx-comp Γ eγ-zy eγ-yx) eγ-xw ⟩ (T ⟪ ρ-wx , eγ-xw ⟫ t)
      ≡⟨ naturality f ⟩
        (S ⟪ ρ-wx , eγ-xw ⟫ (f $⟨ ρ-yz ∙ ρ-xy , strong-ctx-comp Γ eγ-zy eγ-yx ⟩ t)) ∎


--------------------------------------------------
-- Definition of the function type + term constructors

_⇛_ : {Γ : Ctx C} → Ty Γ → Ty Γ → Ty Γ
_⇛_ {Γ = Γ} T S ⟨ z , γ ⟩ = PshFun T S z γ
_⟪_,_⟫_ (T ⇛ S) = lower-presheaffunc
ty-cong (T ⇛ S) refl {t = f} = to-pshfun-eq λ _ _ _ → $-cong f refl
ty-id (_⇛_ {Γ = Γ} T S) {t = f} = to-pshfun-eq (λ _ eγ _ → $-cong f hom-idˡ)
ty-comp (_⇛_ {Γ = Γ} T S) {t = f} = to-pshfun-eq (λ _ _ _ → $-cong f ∙assoc)

-- Lambda abstraction that adds a nameless variable to the context (only accessible by de Bruijn index).
lam : (T : Ty Γ) → Tm (Γ ,, T) (S [ π ]) → Tm Γ (T ⇛ S)
lam {S = S} T b ⟨ z , γz ⟩' = MkFun (λ ρ-yz {γy} eγ t → b ⟨ _ , [ γy , t ] ⟩')
                                    (λ {x = x}{y}{ρ-xy}{_}{γx}{γy}{eγ-zy}{eγ-yx}{t} →
  begin
    b ⟨ x , [ γx , T ⟪ ρ-xy , eγ-yx ⟫ t ] ⟩'
  ≡˘⟨ naturality b ρ-xy (to-Σ-ty-eq T eγ-yx (ty-cong-2-1 T hom-idʳ)) ⟩
    S ⟪ ρ-xy , _ ⟫ b ⟨ y , [ γy , t ] ⟩'
  ≡⟨ ty-cong S refl ⟩
    S ⟪ ρ-xy , eγ-yx ⟫ b ⟨ y , [ γy , t ] ⟩' ∎)
  where open ≡-Reasoning
naturality (lam T b) _ _ = to-pshfun-eq (λ _ _ _ → refl)

-- Version of lambda abstraction that allows to name the bound variable.
lam[_∈_]_ : (v : String) (T : Ty Γ) → Tm (Γ ,, v ∈ T) (S [ π ]) → Tm Γ (T ⇛ S)
lam[_∈_]_ v = lam

-- An operator used to define function application.
_€⟨_,_⟩_ : Tm Γ (T ⇛ S) → (x : Ob) (γ : Γ ⟨ x ⟩) → T ⟨ x , γ ⟩ → S ⟨ x , γ ⟩
_€⟨_,_⟩_ {Γ = Γ} f x γ t = f ⟨ x , γ ⟩' $⟨ hom-id , ctx-id Γ ⟩ t

€-natural : (f : Tm Γ (T ⇛ S)) {ρ : Hom x y}
            {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} {eγ : Γ ⟪ ρ ⟫ γy ≡ γx}
            {t : T ⟨ y , γy ⟩} →
            S ⟪ ρ , eγ ⟫ (f €⟨ y , γy ⟩ t) ≡ f €⟨ x , γx ⟩ (T ⟪ ρ , eγ ⟫ t)
€-natural {Γ = Γ}{T = T}{S = S} f {ρ}{γy}{γx}{eγ}{t} =
  begin
    S ⟪ ρ , eγ ⟫ (f ⟨ _ , γy ⟩' $⟨ hom-id , ctx-id Γ ⟩ t)
  ≡˘⟨ naturality (f ⟨ _ , γy ⟩') ⟩
    f ⟨ _ , γy ⟩' $⟨ hom-id ∙ ρ , strong-ctx-comp Γ (ctx-id Γ) eγ ⟩ (T ⟪ ρ , eγ ⟫ t)
  ≡⟨ $-cong (f ⟨ _ , γy ⟩') (trans hom-idˡ (sym hom-idʳ)) ⟩
    f ⟨ _ , γy ⟩' $⟨ ρ ∙ hom-id , strong-ctx-comp Γ eγ (ctx-id Γ) ⟩ (T ⟪ ρ , eγ ⟫ t)
  ≡⟨ cong (λ x → x $⟨ _ , _ ⟩ _) (naturality f ρ eγ) ⟩
    f ⟨ _ , γx ⟩' $⟨ hom-id , ctx-id Γ ⟩ (T ⟪ ρ , eγ ⟫ t) ∎
  where open ≡-Reasoning

app : Tm Γ (T ⇛ S) → Tm Γ T → Tm Γ S
app f t ⟨ y , γ ⟩' = f €⟨ y , γ ⟩ (t ⟨ y , γ ⟩')
naturality (app {Γ = Γ}{T = T}{S = S} f t) {γy = γy}{γx} ρ eγ =
  begin
    S ⟪ ρ , eγ ⟫ (f €⟨ _ , γy ⟩ (t ⟨ _ , γy ⟩'))
  ≡⟨ €-natural f ⟩
    f €⟨ _ , γx ⟩ (T ⟪ ρ , eγ ⟫ (t ⟨ _ , γy ⟩'))
  ≡⟨ cong (f €⟨ _ , γx ⟩_) (naturality t ρ eγ) ⟩
    f €⟨ _ , γx ⟩ (t ⟨ _ , γx ⟩') ∎
  where open ≡-Reasoning

infixl 10 _$_
_$_ = app

ap : Tm Γ (T ⇛ S) → Tm (Γ ,, T) (S [ π ])
ap f ⟨ x , [ γ , t ] ⟩' = f €⟨ x , γ ⟩ t
naturality (ap {T = T} f) ρ refl = trans (€-natural f) (cong (f €⟨ _ , _ ⟩_) (ty-cong T refl))


--------------------------------------------------
-- Congruence proofs

pshfun-dimap : {T : Ty Γ} {T' : Ty Γ} {S : Ty Γ} {S' : Ty Γ} →
               (T' ↣ T) → (S ↣ S') →
               {z : Ob} {γ : Γ ⟨ z ⟩} →
               PshFun T S z γ → PshFun T' S' z γ
_$⟨_,_⟩_ (pshfun-dimap η φ f) ρ eγ t' = func φ (f $⟨ ρ , eγ ⟩ func η t')
naturality (pshfun-dimap {T = T}{T'}{S}{S'} η φ {z} {γ} f) {eγ-zy = eγ-zy} {eγ-yx} {t'} =
  begin
    func φ (f $⟨ _ , _ ⟩ func η (T' ⟪ _ , eγ-yx ⟫ t'))
  ≡˘⟨ cong (func φ ∘ f $⟨ _ , _ ⟩_) (naturality η) ⟩
    func φ (f $⟨ _ , _ ⟩ (T ⟪ _ , eγ-yx ⟫ func η t'))
  ≡⟨ cong (func φ) (naturality f) ⟩
    func φ (S ⟪ _ , eγ-yx ⟫ (f $⟨ _ , eγ-zy ⟩ func η t'))
  ≡˘⟨ naturality φ ⟩
    S' ⟪ _ , eγ-yx ⟫ func φ (f $⟨ _ , eγ-zy ⟩ func η t') ∎
  where open ≡-Reasoning

⇛-dimap : (T' ↣ T) → (S ↣ S') → (T ⇛ S ↣ T' ⇛ S')
func (⇛-dimap η φ) = pshfun-dimap η φ
naturality (⇛-dimap η φ) = to-pshfun-eq λ _ _ _ → refl

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

lam-cong : (T : Ty Γ) {b b' : Tm (Γ ,, T) (S [ π ])} →
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
eq (app-cong f=f' t=t') γ = €-cong f=f' (eq t=t' γ)

module _
  {T : Ty Γ} {T' : Ty Γ} {S : Ty Γ} {S' : Ty Γ}
  (T=T' : T ≅ᵗʸ T') (S=S' : S ≅ᵗʸ S')
  where

  lam-ι : (b : Tm (Γ ,, T') (S' [ π ])) →
          ι[ ⇛-cong T=T' S=S' ] (lam T' b) ≅ᵗᵐ
            lam T (ι[ ty-subst-cong-ty π S=S' ] (
                   ι⁻¹[ ty-subst-cong-subst (ctx-ext-subst-proj₁ π (ι⁻¹[ ty-subst-cong-ty π T=T' ] ξ)) S' ] (
                   ι⁻¹[ ty-subst-comp S' π (ty-eq-to-ext-subst Γ T=T') ] (
                   b [ ty-eq-to-ext-subst Γ T=T' ]'))))
  eq (lam-ι b) γ = to-pshfun-eq (λ _ _ _ → sym (cong (func (to S=S')) (strong-ty-id S')))

  app-ι : (f : Tm Γ (T' ⇛ S')) (t : Tm Γ T') → app (ι[ ⇛-cong T=T' S=S' ] f) (ι[ T=T' ] t) ≅ᵗᵐ ι[ S=S' ] (app f t)
  eq (app-ι f t) γ = cong (func (to S=S') ∘ f ⟨ _ , γ ⟩' $⟨ hom-id , _ ⟩_) (eq (isoʳ T=T') (t ⟨ _ , γ ⟩'))


--------------------------------------------------
-- Naturality proofs

module _ (σ : Δ ⇒ Γ) (T : Ty Γ) (S : Ty Γ) {δ : Δ ⟨ z ⟩} where
  pshfun-subst-from : PshFun T S z (func σ δ) → PshFun (T [ σ ]) (S [ σ ]) z δ
  _$⟨_,_⟩_ (pshfun-subst-from f) ρ-yz eδ t = f $⟨ ρ-yz , trans (naturality σ) (cong (func σ) eδ) ⟩ t
  naturality (pshfun-subst-from f) = trans ($-cong f refl) (naturality f)

  pshfun-subst-to : PshFun (T [ σ ]) (S [ σ ]) z δ → PshFun T S z (func σ δ)
  _$⟨_,_⟩_ (pshfun-subst-to f) ρ-yz {γ'} eδ t = ty-ctx-subst S proof (
                                                 f $⟨ ρ-yz , refl ⟩
                                                 ty-ctx-subst T (sym proof) t)
    where
      proof : func σ (Δ ⟪ ρ-yz ⟫ δ) ≡ γ'
      proof = trans (sym (naturality σ)) eδ
  naturality (pshfun-subst-to f) {ρ-xy = ρ-xy}{ρ-yz} {eγ-yx = eγ-yx} {t = t} =
    begin
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , refl ⟩ (T ⟪ hom-id , _ ⟫ T ⟪ ρ-xy , eγ-yx ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , α ⟫_ ∘ f $⟨ ρ-yz ∙ ρ-xy , refl ⟩_) (ty-cong-2-2 T (trans hom-idʳ (sym hom-idˡ))) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , refl ⟩ (T ⟪ ρ-xy , _ ⟫ (T ⟪ hom-id , β ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) ($-cong f refl) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , _ ⟩ (T ⟪ ρ-xy , _ ⟫ (T ⟪ hom-id , β ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) (naturality f {eγ-yx = sym (ctx-comp Δ)}) ⟩
      S ⟪ hom-id , α ⟫ S ⟪ ρ-xy , _ ⟫ f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , β ⟫ t)
    ≡⟨ ty-cong-2-2 S (trans hom-idʳ (sym hom-idˡ)) ⟩
      S ⟪ ρ-xy , eγ-yx ⟫ S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , β ⟫ t) ∎
    where
      open ≡-Reasoning
      α = _
      β = _

module _ {T : Ty Γ} {S : Ty Γ} (σ : Δ ⇒ Γ) where
  ⇛-natural : (T ⇛ S) [ σ ] ≅ᵗʸ (T [ σ ]) ⇛ (S [ σ ])
  func (from ⇛-natural) = pshfun-subst-from σ T S
  naturality (from ⇛-natural) {t = f} = to-pshfun-eq (λ _ _ _ → $-cong f refl)
  func (to ⇛-natural) = pshfun-subst-to σ T S
  naturality (to ⇛-natural) {_} {_} {ρ-yz} {t = f} = to-pshfun-eq λ ρ-xy eγ t →
    let α = _
        β = _
        ζ = _
        α' = _
        β' = _
        ζ' = _
    in begin
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , β ⟩ (T ⟪ hom-id , ζ ⟫ t)
    ≡˘⟨ cong (S ⟪ hom-id , α ⟫_ ∘ f $⟨ ρ-yz ∙ ρ-xy , β ⟩_) (ty-cong-2-1 T hom-idˡ) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ ρ-xy , β ⟩ (T ⟪ hom-id , _ ⟫ (T ⟪ hom-id , ζ' ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) ($-cong f (sym hom-idʳ)) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ (ρ-yz ∙ ρ-xy) ∙ hom-id , _ ⟩ (T ⟪ hom-id , _ ⟫ (T ⟪ hom-id , ζ' ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) (naturality f {eγ-yx = trans (ctx-id Δ) (sym β')}) ⟩
      S ⟪ hom-id , α ⟫ S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz ∙ ρ-xy , β' ⟩ (T ⟪ hom-id , ζ' ⟫ t)
    ≡⟨ ty-cong-2-1 S hom-idʳ ⟩
      S ⟪ hom-id , α' ⟫ f $⟨ ρ-yz ∙ ρ-xy , β' ⟩ (T ⟪ hom-id , ζ' ⟫ t) ∎
    where open ≡-Reasoning
  eq (isoˡ ⇛-natural) f = to-pshfun-eq (λ ρ-yz eγ t →
    let α = _ -- giving a name α to the proof makes sure that there are no unsolved metas
    in begin
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz , _ ⟩ (T ⟪ hom-id , _ ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) ($-cong f (sym hom-idʳ)) ⟩
      S ⟪ hom-id , α ⟫ f $⟨ ρ-yz ∙ hom-id , _ ⟩ (T ⟪ hom-id , _ ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) (naturality f) ⟩
      S ⟪ hom-id , α ⟫ S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , eγ ⟩ t
    ≡⟨ ty-cong-2-1 S hom-idʳ ⟩
      S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , eγ ⟩ t
    ≡⟨ ty-id S ⟩
      f $⟨ ρ-yz , eγ ⟩ t ∎)
    where open ≡-Reasoning
  eq (isoʳ ⇛-natural) f = to-pshfun-eq (λ ρ-yz eδ t →
    let α = trans (ctx-id Δ) (sym eδ)
        β = _
    in begin
      S ⟪ hom-id , β ⟫ f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , _ ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , β ⟫_) ($-cong f (sym hom-idʳ)) ⟩
      S ⟪ hom-id , β ⟫ f $⟨ ρ-yz ∙ hom-id , _ ⟩ (T ⟪ hom-id , _ ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , β ⟫_ ∘ f $⟨ ρ-yz ∙ hom-id , _ ⟩_) (ty-cong T refl) ⟩
      S ⟪ hom-id , β ⟫ f $⟨ ρ-yz ∙ hom-id , _ ⟩ (T [ σ ] ⟪ hom-id , α ⟫ t)
    ≡⟨ cong (S ⟪ hom-id , β ⟫_) (naturality f) ⟩
      S ⟪ hom-id , β ⟫ S [ σ ] ⟪ hom-id , α ⟫ f $⟨ ρ-yz , eδ ⟩ t
    ≡⟨ ty-cong-2-1 S hom-idʳ ⟩
      S ⟪ hom-id , _ ⟫ f $⟨ ρ-yz , eδ ⟩ t
    ≡⟨ ty-id S ⟩
      f $⟨ ρ-yz , eδ ⟩ t ∎)
    where open ≡-Reasoning

  lam-natural : (b : Tm (Γ ,, T) (S [ π ])) →
                (lam T b) [ σ ]' ≅ᵗᵐ
                  ι[ ⇛-natural ] (
                  lam (T [ σ ]) (ι⁻¹[ ty-subst-seq-cong (π ∷ σ ⊹ ◼) (σ ∷ π ◼) S (⊹-π-comm σ) ] (b [ σ ⊹ ]')))
  eq (lam-natural b) δ = to-pshfun-eq (λ ρ {γ'} eγ t → sym (
    let α : Γ ⟪ hom-id ⟫ func σ (Δ ⟪ ρ ⟫ δ) ≡ γ'
        α = trans (ctx-id Γ) (trans (sym (naturality σ)) eγ)
        β = begin
              T ⟪ hom-id , _ ⟫ T ⟪ hom-id , _ ⟫ T ⟪ hom-id , _ ⟫ t
            ≡⟨ ty-cong-2-1 T hom-idʳ ⟩
              T ⟪ hom-id , α ⟫ T ⟪ hom-id , _ ⟫ t
            ≡⟨ ty-cong-2-1 T hom-idʳ ⟩
              T ⟪ hom-id , _ ⟫ t
            ≡⟨ ty-id T ⟩
              t ∎
    in begin
      S ⟪ hom-id , _ ⟫ S ⟪ hom-id , _ ⟫ b ⟨ _ , [ func σ (Δ ⟪ ρ ⟫ δ) , T ⟪ hom-id , _ ⟫ t ] ⟩'
    ≡⟨ ty-cong-2-1 S hom-idʳ ⟩
      S ⟪ hom-id , _ ⟫ b ⟨ _ , [ func σ (Δ ⟪ ρ ⟫ δ) , T ⟪ hom-id , _ ⟫ t ] ⟩'
    ≡⟨ naturality b hom-id (to-Σ-ty-eq T α β) ⟩
      b ⟨ _ , [ γ' , t ] ⟩' ∎))
    where open ≡-Reasoning

  app-natural : (f : Tm Γ (T ⇛ S)) (t : Tm Γ T) →
                (app f t) [ σ ]' ≅ᵗᵐ app (ι⁻¹[ ⇛-natural ] (f [ σ ]')) (t [ σ ]')
  eq (app-natural f t) δ = $-cong (f ⟨ _ , func σ δ ⟩') refl


--------------------------------------------------
-- Relation between functions T ⇛ S and natural tranformations T ↣ S

⇛-to-↣ : Tm Γ (T ⇛ S) → (T ↣ S)
func (⇛-to-↣ f) = f €⟨ _ , _ ⟩_
naturality (⇛-to-↣ f) = €-natural f

↣-to-⇛ : (T ↣ S) → Tm Γ (T ⇛ S)
(↣-to-⇛ η ⟨ _ , _ ⟩') $⟨ _ , _ ⟩ t = func η t
naturality (↣-to-⇛ η ⟨ _ , _ ⟩') = sym (naturality η)
naturality (↣-to-⇛ η) _ _ = to-pshfun-eq (λ _ _ _ → refl)

↣-⇛-iso : (η : T ↣ S) → ⇛-to-↣ (↣-to-⇛ η) ≅ⁿ η
eq (↣-⇛-iso η) _ = refl

⇛-↣-iso : (f : Tm Γ (T ⇛ S)) → ↣-to-⇛ (⇛-to-↣ f) ≅ᵗᵐ f
eq (⇛-↣-iso {Γ = Γ} f) {x} γ = to-pshfun-eq (λ {y} ρ {γ'} eγ t →
  begin
    f ⟨ y , γ' ⟩' $⟨ hom-id , ctx-id Γ ⟩ t
  ≡˘⟨ cong (_$⟨ hom-id , ctx-id Γ ⟩ t) (naturality f ρ eγ) ⟩
    f ⟨ x , γ ⟩' $⟨ ρ ∙ hom-id , strong-ctx-comp Γ eγ (ctx-id Γ) ⟩ t
  ≡⟨ $-cong (f ⟨ x , γ ⟩') hom-idʳ ⟩
    f ⟨ x , γ ⟩' $⟨ ρ , eγ ⟩ t ∎)
  where open ≡-Reasoning


--------------------------------------------------
-- Instance of ClosedType

instance
  fun-closed : {A B : ClosedTy C} {{_ : IsClosedNatural A}} {{_ : IsClosedNatural B}} →
               IsClosedNatural (A ⇛ B)
  closed-natural {{fun-closed}} σ = transᵗʸ (⇛-natural σ) (⇛-cong (closed-natural σ) (closed-natural σ))
