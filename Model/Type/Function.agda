--------------------------------------------------
-- (Non-dependent) function types
--------------------------------------------------

open import Model.BaseCategory

module Model.Type.Function {C : BaseCategory} where

open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_) renaming (_,_ to [_,_])
open import Data.String
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Preliminaries
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
      ≡⟨ $-cong f ∙assoc ⟨
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
  ≡⟨ naturality b ρ-xy (to-Σ-ty-eq T eγ-yx (ty-cong-2-1 T hom-idʳ)) ⟨
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
  ≡⟨ naturality (f ⟨ _ , γy ⟩') ⟨
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
  ≡⟨ cong (func φ ∘ f $⟨ _ , _ ⟩_) (naturality η) ⟨
    func φ (f $⟨ _ , _ ⟩ (T ⟪ _ , eγ-yx ⟫ func η t'))
  ≡⟨ cong (func φ) (naturality f) ⟩
    func φ (S ⟪ _ , eγ-yx ⟫ (f $⟨ _ , eγ-zy ⟩ func η t'))
  ≡⟨ naturality φ ⟨
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

⇛-cong-sym : {T=T' : T ≅ᵗʸ T'} {S=S' : S ≅ᵗʸ S'} →
             ⇛-cong (symᵗʸ T=T') (symᵗʸ S=S') ≅ᵉ symᵗʸ (⇛-cong T=T' S=S')
eq (from-eq ⇛-cong-sym) f = to-pshfun-eq (λ _ _ _ → refl)

⇛-cong-trans : {T T' T'' S S' S'' : Ty Γ}
               {T=T' : T ≅ᵗʸ T'} {T'=T'' : T' ≅ᵗʸ T''} {S=S' : S ≅ᵗʸ S'} {S'=S'' : S' ≅ᵗʸ S''} →
               ⇛-cong (transᵗʸ T=T' T'=T'') (transᵗʸ S=S' S'=S'') ≅ᵉ transᵗʸ (⇛-cong T=T' S=S') (⇛-cong T'=T'' S'=S'')
eq (from-eq ⇛-cong-trans) _ = to-pshfun-eq (λ _ _ _ → refl)

⇛-cong-cong : {T1 T2 S1 S2 : Ty Γ} {eT eT' : T1 ≅ᵗʸ T2} {eS eS' : S1 ≅ᵗʸ S2} →
              eT ≅ᵉ eT' → eS ≅ᵉ eS' → ⇛-cong eT eS ≅ᵉ ⇛-cong eT' eS'
eq (from-eq (⇛-cong-cong {eS' = eS'} 𝑒T 𝑒S)) f =
  to-pshfun-eq (λ ρ eγ _ → trans (eq (from-eq 𝑒S) _) (cong (λ x → func (from eS') (f $⟨ ρ , eγ ⟩ x)) (eq (to-eq 𝑒T) _)))

lam-cong : (T : Ty Γ) {b b' : Tm (Γ ,, T) (S [ π ])} →
           b ≅ᵗᵐ b' → lam T b ≅ᵗᵐ lam T b'
eq (lam-cong T b=b') γ = to-pshfun-eq (λ _ {γ'} _ t → eq b=b' [ γ' , t ])

ap-cong : {f f' : Tm Γ (T ⇛ S)} → f ≅ᵗᵐ f' → ap f ≅ᵗᵐ ap f'
eq (ap-cong f=f') γ = cong (_$⟨ hom-id , _ ⟩ _) (eq f=f' (proj₁ γ))

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
  {T=T' : T ≅ᵗʸ T'} {S=S' : S ≅ᵗʸ S'}
  where

  lam-ι : (b : Tm (Γ ,, T') (S' [ π ])) →
          ι[ ⇛-cong T=T' S=S' ] (lam T' b) ≅ᵗᵐ
            lam T (ι[ ty-subst-cong-ty π S=S' ] (
                   ι⁻¹[ ty-subst-cong-subst (ctx-ext-subst-β₁ π (ι⁻¹[ ty-subst-cong-ty π T=T' ] ξ)) S' ] (
                   ι⁻¹[ ty-subst-comp S' π (ty-eq-to-ext-subst Γ T=T') ] (
                   b [ ty-eq-to-ext-subst Γ T=T' ]'))))
  eq (lam-ι b) γ = to-pshfun-eq (λ _ _ _ → sym (cong (func (to S=S')) (strong-ty-id S')))

  lam-ι⁻¹ : (b : Tm (Γ ,, T) (S [ π ])) →
            ι⁻¹[ ⇛-cong T=T' S=S' ] (lam T b) ≅ᵗᵐ
              lam T' (ι⁻¹[ ty-subst-cong-ty π S=S' ] (
                      ι⁻¹[ ty-subst-cong-subst (ctx-ext-subst-β₁ π (ι[ ty-subst-cong-ty π T=T' ] ξ)) S ] (
                      ι⁻¹[ ty-subst-comp S π _ ] (
                      b [ _ ]'))))
  eq (lam-ι⁻¹ b) γ = to-pshfun-eq (λ _ _ _ → cong (func (from S=S')) (sym (strong-ty-id S)))

  app-ι : (f : Tm Γ (T' ⇛ S')) (t : Tm Γ T') → app (ι[ ⇛-cong T=T' S=S' ] f) (ι[ T=T' ] t) ≅ᵗᵐ ι[ S=S' ] (app f t)
  eq (app-ι f t) γ = cong (func (to S=S') ∘ f ⟨ _ , γ ⟩' $⟨ hom-id , _ ⟩_) (eq (isoʳ T=T') (t ⟨ _ , γ ⟩'))

  app-ι⁻¹ : (f : Tm Γ (T ⇛ S)) (t : Tm Γ T) → app (ι⁻¹[ ⇛-cong T=T' S=S' ] f) (ι⁻¹[ T=T' ] t) ≅ᵗᵐ ι⁻¹[ S=S' ] (app f t)
  eq (app-ι⁻¹ f t) γ = cong (func (from S=S') ∘ f ⟨ _ , γ ⟩' $⟨ hom-id , _ ⟩_) (eq (isoˡ T=T') (t ⟨ _ , γ ⟩'))

ap-ι : {T S S' : Ty Γ} {S=S' : S ≅ᵗʸ S'} (f : Tm Γ (T ⇛ S')) →
       ι[ ty-subst-cong-ty π S=S' ] (ap f) ≅ᵗᵐ ap (ι[ ⇛-cong reflᵗʸ S=S' ] f)
eq (ap-ι f) γ = refl


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
    ≡⟨ cong (S ⟪ hom-id , α ⟫_ ∘ f $⟨ ρ-yz ∙ ρ-xy , β ⟩_) (ty-cong-2-1 T hom-idˡ) ⟨
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
                  lam (T [ σ ]) (ι⁻¹[ transᵗʸ (ty-subst-comp S π (σ ⊹)) (transᵗʸ (ty-subst-cong-subst (⊹-π-comm σ) S) (symᵗʸ (ty-subst-comp S σ π))) ] (b [ σ ⊹ ]')))
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

  ap-natural : (f : Tm Γ (T ⇛ S)) →
               (ap f) [ σ ⊹ ]' ≅ᵗᵐ (ι[ ty-subst-cong-subst-2-2 S (⊹-π-comm σ) ] ap (ι⁻¹[ ⇛-natural ] (f [ σ ]')))
  eq (ap-natural f) δ = trans (sym (trans ($-cong (f ⟨ _ , _ ⟩') hom-idʳ) (cong (f €⟨ _ , _ ⟩_) (strong-ty-id T))))
                              (naturality (f ⟨ _ , func σ (proj₁ δ) ⟩'))

  app-natural : (f : Tm Γ (T ⇛ S)) (t : Tm Γ T) →
                (app f t) [ σ ]' ≅ᵗᵐ app (ι⁻¹[ ⇛-natural ] (f [ σ ]')) (t [ σ ]')
  eq (app-natural f t) δ = $-cong (f ⟨ _ , func σ δ ⟩') refl

⇛-natural-cong : {T T' S S' : Ty Δ} {σ : Γ ⇒ Δ} {T=T' : T ≅ᵗʸ T'} {S=S' : S ≅ᵗʸ S'} →
                 transᵗʸ (ty-subst-cong-ty σ (⇛-cong T=T' S=S')) (⇛-natural σ)
                   ≅ᵉ
                 transᵗʸ (⇛-natural σ) (⇛-cong (ty-subst-cong-ty σ T=T') (ty-subst-cong-ty σ S=S'))
eq (from-eq ⇛-natural-cong) _ = to-pshfun-eq (λ _ _ _ → refl)


--------------------------------------------------
-- β and η laws for functions

⇛-β : (b : Tm (Γ ,, T) (S [ π ])) (t : Tm Γ T) → app (lam T b) t ≅ᵗᵐ ι⁻¹[ ty-weaken-subst t ] (b [ t /v ]')
eq (⇛-β {S = S} b s) γ = sym (strong-ty-id S)

⇛-η : (f : Tm Γ (T ⇛ S)) → f ≅ᵗᵐ lam T (app (ι⁻¹[ ⇛-natural π ] (f [ π ]')) ξ)
eq (⇛-η f) γ = to-pshfun-eq (λ ρ eγ t → trans ($-cong (f ⟨ _ , γ ⟩') (sym hom-idʳ)) (cong (_$⟨ hom-id , _ ⟩ t) (naturality f ρ eγ)))


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
  ≡⟨ cong (_$⟨ hom-id , ctx-id Γ ⟩ t) (naturality f ρ eγ) ⟨
    f ⟨ x , γ ⟩' $⟨ ρ ∙ hom-id , strong-ctx-comp Γ eγ (ctx-id Γ) ⟩ t
  ≡⟨ $-cong (f ⟨ x , γ ⟩') hom-idʳ ⟩
    f ⟨ x , γ ⟩' $⟨ ρ , eγ ⟩ t ∎)
  where open ≡-Reasoning


--------------------------------------------------
-- Relating function types and closed types

module _ {A : Ty Γ} {B : ClosedTy C} (clB : IsClosedNatural B ) where
  lamcl : Tm (Γ ,, A) B → Tm Γ (A ⇛ B)
  lamcl b = lam _ (ι[ closed-natural clB π ] b)

  lamcl-cong : {b b' : Tm (Γ ,, A) B} → b ≅ᵗᵐ b' → lamcl b ≅ᵗᵐ lamcl b'
  lamcl-cong 𝒆 = lam-cong A (ι-cong 𝒆)

module _ {A B : ClosedTy C} (clA : IsClosedNatural A) (clB : IsClosedNatural B) where
  fun-closed : IsClosedNatural (A ⇛ B)
  closed-natural fun-closed σ = transᵗʸ (⇛-natural σ) (⇛-cong (closed-natural clA σ) (closed-natural clB σ))
  eq (from-eq (closed-id fun-closed)) f = to-pshfun-eq (λ ρ eγ a →
    trans (eq (from-eq (closed-id clB)) _)
          (trans ($-cong f refl)
                 (cong (f $⟨ ρ , eγ ⟩_) (eq (to-eq (closed-id clA)) a))))
  eq (from-eq (closed-⊚ fun-closed σ τ)) f = to-pshfun-eq (λ ρ eγ a →
    trans (eq (from-eq (closed-⊚ clB σ τ)) _)
          (cong (func (from (closed-natural clB (σ ⊚ τ))))
            (trans ($-cong f refl)
                   (cong (f $⟨ ρ , _ ⟩_) (eq (to-eq (closed-⊚ clA σ τ)) a)))))
  eq (from-eq (closed-subst-eq fun-closed {Δ = Δ} {σ = σ} {τ} ε)) f = to-pshfun-eq (λ ρ eγ a →
    trans (cong (func (from (closed-natural clB τ))) (sym (trans (ty-cong-2-1 B hom-idˡ {eg = trans (ctx-id Δ) (sym (eq ε _))}) (ty-id B))))
          (trans (eq (from-eq (closed-subst-eq clB ε)) _)
                 (cong (func (from (closed-natural clB σ)))
                       (trans (sym (naturality f))
                              (trans ($-cong f (trans hom-idʳ hom-idˡ))
                                     (cong (f $⟨ ρ , _ ⟩_) (eq (to-eq (closed-subst-eq clA ε)) a)))))))

  lamcl-natural : {σ : Γ ⇒ Δ} {b : Tm (Δ ,, A) B} → (lamcl clB b) [ fun-closed ∣ σ ]cl ≅ᵗᵐ lamcl clB (b [ clB ∣ lift-cl-subst clA σ ]cl)
  lamcl-natural {σ = σ} =
    transᵗᵐ (ι⁻¹-cong (lam-natural _ _))
    (transᵗᵐ ι⁻¹-trans
    (transᵗᵐ (ι⁻¹-cong ι-symˡ)
    (transᵗᵐ (lam-ι⁻¹ _)
    (lam-cong A (transᵗᵐ (ι⁻¹-cong (ι⁻¹-cong (ι⁻¹-cong (transᵗᵐ (symᵗᵐ ι⁻¹-subst-commute) (transᵗᵐ (ι⁻¹-cong (tm-subst-comp _ _ _)) (ι⁻¹-cong (ι-cong (symᵗᵐ ι-subst-commute))))))))
                (transᵗᵐ (symᵗᵐ ι⁻¹-trans)
                (transᵗᵐ (symᵗᵐ ι⁻¹-trans)
                (transᵗᵐ (symᵗᵐ ι⁻¹-trans)
                (transᵗᵐ (symᵗᵐ ι-trans)
                (transᵗᵐ (ι-congᵉ-2-2 e-proof)
                (transᵗᵐ (ι-cong (symᵗᵐ (tm-subst-cong-subst _ (transˢ s-proof (symˢ (ctx-ext-subst-comp _ _ _)))))) ι-trans)))))))))))
    where
      e-proof : _ ≅ᵉ _
      eq (from-eq e-proof) t =
        let α = _
        in sym
          (trans (cong (λ x → ty-ctx-subst B α (func (to (closed-natural clB (lift-cl-subst clA σ))) (func (from (closed-natural clB π)) x)))
                       (sym (eq (isoʳ (closed-natural clB σ)) t)))
          (trans (cong (λ x → ty-ctx-subst B α (func (to (closed-natural clB (lift-cl-subst clA σ))) x))
                 (trans (eq (from-eq (closed-⊚ clB σ π)) _)
                 (trans (sym (eq (from-eq (closed-subst-eq clB (symˢ (lift-cl-subst-π-commute clA)))) _)) (sym (eq (from-eq (closed-⊚ clB π (lift-cl-subst clA σ))) _)))))
          (trans (cong (ty-ctx-subst B α) (eq (isoˡ (closed-natural clB (lift-cl-subst clA σ))) _))
          (trans (naturality (from (closed-natural clB π)))
          (cong (func (from (closed-natural clB π))) (ty-cong-2-2 B refl))))))

      s-proof : _ ≅ˢ _
      s-proof = transˢ (symˢ (ctx-ext-subst-cong-subst (transˢ ⊚-assoc (⊚-congʳ (ctx-ext-subst-β₁ π _))) _))
                       (ctx-ext-subst-cong-tm _ (record { eq = λ γ → trans (strong-ty-id A)
                                                                     (trans (sym (eq (to-eq (closed-⊚ clA σ π)) _))
                                                                     (cong (func (to (closed-natural clA σ))) (eq (isoˡ (closed-natural clA π)) _))) }))

  app-cl-natural : {σ : Γ ⇒ Δ} {f : Tm Δ (A ⇛ B)} {a : Tm Δ A} →
                   (app f a) [ clB ∣ σ ]cl ≅ᵗᵐ app (f [ fun-closed ∣ σ ]cl) (a [ clA ∣ σ ]cl)
  app-cl-natural = transᵗᵐ (ι⁻¹-cong (app-natural _ _ _)) (transᵗᵐ (symᵗᵐ (app-ι⁻¹ _ _)) (app-cong (symᵗᵐ ι⁻¹-trans) reflᵗᵐ))

  ⇛-cl-β : (b : Tm (Γ ,, A) B) (a : Tm Γ A) → app (lamcl clB b) a ≅ᵗᵐ b [ clB ∣ a /cl⟨ clA ⟩ ]cl
  ⇛-cl-β b a =
    transᵗᵐ (⇛-β _ a) (
    transᵗᵐ (ι⁻¹-cong (transᵗᵐ (symᵗᵐ ι-subst-commute) (ι-cong (tm-subst-cong-subst b (/v-/cl clA a))))) (
    transᵗᵐ (symᵗᵐ ι-trans) (
    transᵗᵐ (symᵗᵐ ι-trans) (
    ι-congᵉ (to-symᵗʸ-eq (
      transᵉ transᵗʸ-assoc (
      transᵉ (transᵗʸ-congʳ (closed-subst-eq clB _)) (
      transᵉ transᵗʸ-assoc (
      transᵉ (transᵗʸ-congʳ (closed-⊚ clB π (a /v))) (
      transᵉ (transᵗʸ-congˡ (transᵉ symᵗʸ-transᵗʸ (transᵗʸ-congʳ symᵗʸ-transᵗʸ))) (
      transᵉ (transᵉ transᵗʸ-assoc (transᵗʸ-congʳ (transᵉ transᵗʸ-assoc (transᵗʸ-congʳ (symᵉ transᵗʸ-assoc))))) (
      transᵉ (transᵗʸ-congʳ (transᵗʸ-congʳ transᵗʸ-cancelˡ-symˡ)) (
      transᵉ (transᵗʸ-congʳ (transᵗʸ-congˡ (symᵉ ty-subst-cong-subst-sym))) (
      transᵉ (transᵗʸ-congʳ (closed-subst-eq clB _)) (
      transᵉ (transᵗʸ-congʳ (closed-id clB)) symᵗʸ-invˡ)))))))))))))))

  ⇛-cl-η : (f : Tm Γ (A ⇛ B)) → f ≅ᵗᵐ lamcl clB (app (f [ fun-closed ∣ π ]cl) (ξcl clA))
  ⇛-cl-η f = transᵗᵐ (⇛-η f) (
    lam-cong A (transᵗᵐ (app-cong (symᵗᵐ (ι-congᵉ-2-1 (transᵉ (transᵗʸ-congʳ symᵗʸ-transᵗʸ) (
                                                       transᵉ (symᵉ transᵗʸ-assoc) (
                                                       transᵉ (transᵗʸ-congˡ symᵗʸ-invʳ)
                                                       reflᵗʸ-unitˡ)))))
                                  (symᵗᵐ ι-symʳ))
                        (app-ι _ _)))

fun-closed-congᶜⁿ : {A B : ClosedTy C}
                    {clA clA' : IsClosedNatural A} {clB clB' : IsClosedNatural B} →
                    clA ≅ᶜⁿ clA' → clB ≅ᶜⁿ clB' →
                    fun-closed clA clB ≅ᶜⁿ fun-closed clA' clB'
closed-natural-eq (fun-closed-congᶜⁿ eA eB) σ =
  transᵗʸ-congʳ (⇛-cong-cong (closed-natural-eq eA σ) (closed-natural-eq eB σ))

⇛-closed-cong : {A A' B B' : ClosedTy C}
                {clA : IsClosedNatural A} {clA' : IsClosedNatural A'} {clB : IsClosedNatural B} {clB' : IsClosedNatural B'} →
                clA ≅ᶜᵗʸ clA' → clB ≅ᶜᵗʸ clB' → fun-closed clA clB ≅ᶜᵗʸ fun-closed clA' clB'
closed-ty-eq (⇛-closed-cong eA eB) = ⇛-cong (closed-ty-eq eA) (closed-ty-eq eB)
closed-ty-eq-natural (⇛-closed-cong eA eB) _ =
  transᵉ (symᵉ transᵗʸ-assoc) (
  transᵉ (transᵗʸ-congˡ ⇛-natural-cong) (
  transᵉ transᵗʸ-assoc (
  transᵉ (transᵗʸ-congʳ (transᵉ (symᵉ ⇛-cong-trans) (
                         transᵉ (⇛-cong-cong (closed-ty-eq-natural eA _) (closed-ty-eq-natural eB _))
                         ⇛-cong-trans))) (
  symᵉ transᵗʸ-assoc))))
