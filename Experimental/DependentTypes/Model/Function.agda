--------------------------------------------------
-- Dependent function types
--------------------------------------------------

open import Model.BaseCategory

module Experimental.DependentTypes.Model.Function {C : BaseCategory} where

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

infixr 4 lam[_∈_]_


--------------------------------------------------
-- Description of a function type at a specific stage (object of the base category)

record PshFun {Γ : Ctx C} (T : Ty Γ) (S : Ty (Γ ,, T)) (z : Ob) (γ : Γ ⟨ z ⟩) : Set where
  constructor MkFun
  field
    _$⟨_,_⟩_ : ∀ {y} (ρ : Hom y z) {γ' : Γ ⟨ y ⟩} (eγ : Γ ⟪ ρ ⟫ γ ≡ γ') →
               (t : T ⟨ y , γ' ⟩) → S ⟨ y , [ γ' , t ] ⟩
    naturality : ∀ {x y} {ρ-xy : Hom x y} {ρ-yz : Hom y z} {γx : Γ ⟨ x ⟩} {γy : Γ ⟨ y ⟩} →
                 {eγ-zy : Γ ⟪ ρ-yz ⟫ γ ≡ γy} {eγ-yx : Γ ⟪ ρ-xy ⟫ γy ≡ γx} {t : T ⟨ y , γy ⟩} →
                 _$⟨_,_⟩_ (ρ-yz ∙ ρ-xy) (strong-ctx-comp Γ eγ-zy eγ-yx) (T ⟪ ρ-xy , eγ-yx ⟫ t) ≡
                   S ⟪ ρ-xy , to-Σ-ty-eq T eγ-yx (ty-cong-2-1 T hom-idʳ) ⟫ (_$⟨_,_⟩_ ρ-yz eγ-zy t)
  infix 13 _$⟨_,_⟩_
open PshFun public

$-cong : {T : Ty Γ} {S : Ty (Γ ,, T)}
         {γx : Γ ⟨ x ⟩} {γy : Γ ⟨ y ⟩} (f : PshFun T S y γy)
         {ρ : Hom x y} {eγ : Γ ⟪ ρ ⟫ γy ≡ γx}
         {t t' : T ⟨ x , γx ⟩} (et : t ≡ t') →
         ty-ctx-subst S (cong [ γx ,_] et) (f $⟨ ρ , eγ ⟩ t) ≡ f $⟨ ρ , eγ ⟩ t'
$-cong {S = S} f refl = strong-ty-id S

-- Here we make use of uip by pattern matching on both equality proofs.
$-hom-cong : {T : Ty Γ} {S : Ty (Γ ,, T)}
             {γx : Γ ⟨ x ⟩} {γy : Γ ⟨ y ⟩} (f : PshFun T S y γy)
             {ρ ρ' : Hom x y} (eρ : ρ ≡ ρ')
             {eγ : Γ ⟪ ρ ⟫ γy ≡ γx} {eγ' : Γ ⟪ ρ' ⟫ γy ≡ γx}
             {t : T ⟨ x , γx ⟩} →
             f $⟨ ρ , eγ ⟩ t ≡ f $⟨ ρ' , eγ' ⟩ t
$-hom-cong f refl {eγ = refl} {eγ' = refl} = refl

-- This is one of the few places where we use function extensionality.
to-pshfun-eq : {T : Ty Γ} {S : Ty (Γ ,, T)}
               {γ : Γ ⟨ y ⟩} {f g : PshFun T S y γ} →
               (∀ {x} (ρ : Hom x y) {γ'} (eγ : Γ ⟪ ρ ⟫ γ ≡ γ') t →
                   f $⟨ ρ , eγ ⟩ t ≡ g $⟨ ρ , eγ ⟩ t) →
               f ≡ g
to-pshfun-eq e = cong₂-d MkFun
  (funextI (funext (λ ρ → funextI (funext λ eq → funext λ t → e ρ eq t))))
  (funextI (funextI (funextI (funextI (funextI (funextI (funextI (funextI (funextI (uip _ _))))))))))

-- This will be used to define the action of a function type on morphisms.
lower-presheaffunc : {T : Ty Γ} {S : Ty (Γ ,, T)} (ρ-yz : Hom y z)
                     {γz : Γ ⟨ z ⟩} {γy : Γ ⟨ y ⟩} (eγ : Γ ⟪ ρ-yz ⟫ γz ≡ γy) →
                     PshFun T S z γz → PshFun T S y γy
lower-presheaffunc {Γ = Γ}{y = y}{z = z}{T = T}{S = S} ρ-yz {γz}{γy} eγ-zy f = MkFun g g-nat
  where
    g : ∀ {x} (ρ-xy : Hom x y) {γx} (eγ-yx : Γ ⟪ ρ-xy ⟫ γy ≡ γx) →
        (t : T ⟨ x , γx ⟩) → S ⟨ x , [ γx , t ] ⟩
    g ρ-xy eγ-yx t = f $⟨ ρ-yz ∙ ρ-xy , strong-ctx-comp Γ eγ-zy eγ-yx ⟩ t
    open ≡-Reasoning
    g-nat : ∀ {w x} {ρ-wx : Hom w x} {ρ-xy : Hom x y} {γx : Γ ⟨ x ⟩} {γw : Γ ⟨ w ⟩}
            {eγ-yx : Γ ⟪ ρ-xy ⟫ γy ≡ γx} {eγ-xw : Γ ⟪ ρ-wx ⟫ γx ≡ γw} {t : T ⟨ x , γx ⟩} → _
    g-nat {ρ-wx = ρ-wx}{ρ-xy}{eγ-yx = eγ-yx}{eγ-xw}{t = t} =
      begin
        f $⟨ ρ-yz ∙ (ρ-xy ∙ ρ-wx) , strong-ctx-comp Γ eγ-zy (strong-ctx-comp Γ eγ-yx eγ-xw) ⟩ (T ⟪ ρ-wx , eγ-xw ⟫ t)
      ≡⟨ $-hom-cong f ∙assoc ⟨
        f $⟨ (ρ-yz ∙ ρ-xy) ∙ ρ-wx , strong-ctx-comp Γ (strong-ctx-comp Γ eγ-zy eγ-yx) eγ-xw ⟩ (T ⟪ ρ-wx , eγ-xw ⟫ t)
      ≡⟨ naturality f ⟩
        (S ⟪ ρ-wx , to-Σ-ty-eq T eγ-xw (ty-cong-2-1 T hom-idʳ) ⟫ (f $⟨ ρ-yz ∙ ρ-xy , strong-ctx-comp Γ eγ-zy eγ-yx ⟩ t)) ∎


--------------------------------------------------
-- Definition of the function type + term constructors

Pi : {Γ : Ctx C} → (T : Ty Γ) → Ty (Γ ,, T) → Ty Γ
Pi {Γ = Γ} T S ⟨ z , γ ⟩ = PshFun T S z γ
_⟪_,_⟫_ (Pi T S) = lower-presheaffunc
ty-cong (Pi T S) refl {t = f} = to-pshfun-eq λ _ _ _ → $-hom-cong f refl
ty-id (Pi {Γ = Γ} T S) {t = f} = to-pshfun-eq (λ _ eγ _ → $-hom-cong f hom-idˡ)
ty-comp (Pi {Γ = Γ} T S) {t = f} = to-pshfun-eq (λ _ _ _ → $-hom-cong f ∙assoc)

-- Lambda abstraction that adds a nameless variable to the context (only accessible by de Bruijn index).
lam : (T : Ty Γ) {S : Ty (Γ ,, T)} → Tm (Γ ,, T) S → Tm Γ (Pi T S)
lam T {S} b ⟨ z , γz ⟩' = MkFun
  (λ ρ-yz {γy} eγ t → b ⟨ _ , [ γy , t ] ⟩')
  (sym (naturality b _ _))
naturality (lam T b) _ _ = to-pshfun-eq (λ _ _ _ → refl)

-- Version of lambda abstraction that allows to name the bound variable.
lam[_∈_]_ : (v : String) (T : Ty Γ) {S : Ty (Γ ,, T)} → Tm (Γ ,, v ∈ T) S → Tm Γ (Pi T S)
lam[_∈_]_ v = lam

-- An operator used to define function application.
_€⟨_,_⟩_ : Tm Γ (Pi T S) → (x : Ob) (γ : Γ ⟨ x ⟩) → (t : T ⟨ x , γ ⟩) → S ⟨ x , [ γ , t ] ⟩
_€⟨_,_⟩_ {Γ = Γ} f x γ t = f ⟨ x , γ ⟩' $⟨ hom-id , ctx-id Γ ⟩ t

€-cong : (f : Tm Γ (Pi T S)) {x : Ob} {γ : Γ ⟨ x ⟩} {t1 t2 : T ⟨ x , γ ⟩} →
         (et : t1 ≡ t2) → ty-ctx-subst S (cong [ γ ,_] et) (f €⟨ x , γ ⟩ t1) ≡ f €⟨ x , γ ⟩ t2
€-cong {S = S} f refl = strong-ty-id S

€-natural : (f : Tm Γ (Pi T S)) {ρ : Hom x y}
            {γy : Γ ⟨ y ⟩} {γx : Γ ⟨ x ⟩} {eγ : Γ ⟪ ρ ⟫ γy ≡ γx}
            {t : T ⟨ y , γy ⟩} →
            S ⟪ ρ , to-Σ-ty-eq T eγ (ty-cong-2-1 T hom-idʳ) ⟫ (f €⟨ y , γy ⟩ t) ≡ f €⟨ x , γx ⟩ (T ⟪ ρ , eγ ⟫ t)
€-natural {Γ = Γ}{T = T}{S = S} f {ρ}{γy}{γx}{eγ}{t} =
  begin
    S ⟪ ρ , to-Σ-ty-eq T eγ (ty-cong-2-1 T hom-idʳ) ⟫ (f ⟨ _ , γy ⟩' $⟨ hom-id , ctx-id Γ ⟩ t)
  ≡⟨ naturality (f ⟨ _ , γy ⟩') ⟨
    f ⟨ _ , γy ⟩' $⟨ hom-id ∙ ρ , strong-ctx-comp Γ (ctx-id Γ) eγ ⟩ (T ⟪ ρ , eγ ⟫ t)
  ≡⟨ $-hom-cong (f ⟨ _ , γy ⟩') (trans hom-idˡ (sym hom-idʳ)) ⟩
    f ⟨ _ , γy ⟩' $⟨ ρ ∙ hom-id , strong-ctx-comp Γ eγ (ctx-id Γ) ⟩ (T ⟪ ρ , eγ ⟫ t)
  ≡⟨ cong (λ x → x $⟨ _ , _ ⟩ _) (naturality f ρ eγ) ⟩
    f ⟨ _ , γx ⟩' $⟨ hom-id , ctx-id Γ ⟩ (T ⟪ ρ , eγ ⟫ t) ∎
  where open ≡-Reasoning

-- Inverse of lambda abstraction, producing a term in an extended context.
ap : Tm Γ (Pi T S) → Tm (Γ ,, T) S
ap f ⟨ x , [ γ , t ] ⟩' = f €⟨ x , γ ⟩ t
naturality (ap {T = T} {S = S} f) {γy = [ γy , ty ]} {γx = [ γx , tx ]} ρ e = begin
  S ⟪ ρ , e ⟫ (f €⟨ _ , γy ⟩ ty)
    ≡⟨ ty-cong-2-1 S hom-idʳ ⟨
  ty-ctx-subst S _ (S ⟪ ρ , _ ⟫ (f €⟨ _ , γy ⟩ ty))
    ≡⟨ cong (ty-ctx-subst S _) (€-natural f) ⟩
  ty-ctx-subst S _ (f €⟨ _ , γx ⟩ (T ⟪ ρ , eγ ⟫ ty))
    ≡⟨ €-cong f (trans (sym (ty-cong-2-1 T hom-idʳ)) et) ⟩
  f €⟨ _ , γx ⟩ tx ∎
  where
    open ≡-Reasoning
    eγ = proj₁ (from-Σ-ty-eq T e)
    et = proj₂ (from-Σ-ty-eq T e)

cl-app : {T : ClosedTy C} (clT : IsClosedNatural T) {S : Ty (Γ ,, T)} →
         Tm Γ (Pi T S) → (t : Tm Γ T) → Tm Γ (S [ id-subst Γ ,cl⟨ clT ⟩ t ])
cl-app clT f t = ap f [ id-subst _ ,cl⟨ clT ⟩ t ]'

{-
app : Tm Γ (Pi T S) → Tm Γ T → Tm Γ S
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


--------------------------------------------------
-- Congruence proofs

-}

pshfun-dimap : {T T' : Ty Γ} {S : Ty (Γ ,, T)} {S' : Ty (Γ ,, T')}
               (η : T' ↣ T) → (S [ ,,-map η ] ↣ S') →
               {z : Ob} {γz : Γ ⟨ z ⟩} →
               PshFun T S z γz → PshFun T' S' z γz
(pshfun-dimap η φ f) $⟨ ρ , eγ ⟩ t' = func φ (f $⟨ ρ , eγ ⟩ (func η t'))
naturality (pshfun-dimap {T = T} {T'} {S} {S'} η φ {z} {γz} f) {eγ-zy = eγ-zy} {eγ-yx} {t'} =
  begin
    func φ (f $⟨ _ , _ ⟩ (func η (T' ⟪ _ , eγ-yx ⟫ t')))
  ≡⟨ cong (func φ) ($-cong f (naturality η)) ⟨
    func φ (S ⟪ hom-id , _ ⟫ (f $⟨ _ , _ ⟩ (T ⟪ _ , eγ-yx ⟫ (func η t'))))
  ≡⟨ cong (func φ ∘ S ⟪ hom-id , _ ⟫_) (naturality f) ⟩
    func φ (S ⟪ hom-id , _ ⟫ S ⟪ _ , _ ⟫ (f $⟨ _ , eγ-zy ⟩ (func η t')))
  ≡⟨ cong (func φ) (ty-cong-2-1 S hom-idʳ) ⟩
    func φ (S ⟪ _ , _ ⟫ (f $⟨ _ , eγ-zy ⟩ (func η t')))
  ≡⟨ naturality φ ⟨
    S' ⟪ _ , _ ⟫ (func φ (f $⟨ _ , eγ-zy ⟩ (func η t'))) ∎
  where open ≡-Reasoning

Pi-dimap : (η : T' ↣ T) → (S [ ,,-map η ] ↣ S') → (Pi T S ↣ Pi T' S')
func (Pi-dimap η φ) = pshfun-dimap η φ
naturality (Pi-dimap η φ) = to-pshfun-eq (λ _ _ _ → refl)

Pi-cong : (eT : T ≅ᵗʸ T') → S ≅ᵗʸ ιc[ ,,-cong eT ] S' → Pi T S ≅ᵗʸ Pi T' S'
from (Pi-cong {S = S} {S' = S'} eT eS) = Pi-dimap (to eT) (from proof)
  where
    proof : (S [ ,,-map (to eT) ]) ≅ᵗʸ S'
    proof = transᵗʸ (ty-subst-cong-ty (,,-map (to eT)) eS)
                    (transᵗʸ (ty-subst-comp S' _ _)
                             (transᵗʸ (ty-subst-cong-subst (transˢ (symˢ (,,-map-comp _ _))
                                                                   (transˢ (,,-map-cong (isoʳ eT)) ,,-map-id)) S')
                                      (ty-subst-id S')))
to (Pi-cong eT eS) = Pi-dimap (from eT) (to eS)
eq (isoˡ (Pi-cong {S = S} {S' = S'} eT eS)) f = to-pshfun-eq (λ ρ eγ t →
  begin
    func (to eS) (S' ⟪ hom-id , _ ⟫ (func (from eS) (f $⟨ ρ , eγ ⟩ (func (to eT) (func (from eT) t)))))
  ≡⟨ cong (func (to eS) ∘ S' ⟪ hom-id , _ ⟫_ ∘ (func (from eS))) ($-cong f (sym (eq (isoˡ eT) t))) ⟨
    func (to eS) (S' ⟪ hom-id , _ ⟫ (func (from eS) (S ⟪ hom-id , _ ⟫ (f $⟨ ρ , eγ ⟩ t))))
  ≡⟨ cong (func (to eS) ∘ S' ⟪ hom-id , _ ⟫_) (naturality (from eS)) ⟨
    func (to eS) (S' ⟪ hom-id , _ ⟫ (S' ⟪ hom-id , _ ⟫ (func (from eS) (f $⟨ ρ , eγ ⟩ t))))
  ≡⟨ cong (func (to eS)) (ty-cong-2-1 S' hom-idʳ) ⟩
    func (to eS) (S' ⟪ hom-id , _ ⟫ (func (from eS) (f $⟨ ρ , eγ ⟩ t)))
  ≡⟨ cong (func (to eS)) (ty-id S') ⟩
    func (to eS) (func (from eS) (f $⟨ ρ , eγ ⟩ t))
  ≡⟨ eq (isoˡ eS) _ ⟩
    f $⟨ ρ , eγ ⟩ t ∎)
  where open ≡-Reasoning
eq (isoʳ (Pi-cong {S' = S'} eT eS)) f = to-pshfun-eq (λ ρ eγ t' →
  begin
    S' ⟪ hom-id , _ ⟫ (func (from eS) (func (to eS) (f $⟨ ρ , eγ ⟩ (func (from eT) (func (to eT) t')))))
  ≡⟨ cong (S' ⟪ hom-id , _ ⟫_) (eq (isoʳ eS) _) ⟩
    S' ⟪ hom-id , _ ⟫ (f $⟨ ρ , eγ ⟩ (func (from eT) (func (to eT) t')))
  ≡⟨ cong (S' ⟪ hom-id , _ ⟫_) ($-cong f (sym (eq (isoʳ eT) t'))) ⟨
    S' ⟪ hom-id , _ ⟫ S' ⟪ hom-id , _ ⟫ (f $⟨ ρ , eγ ⟩ t')
  ≡⟨ ty-cong-2-1 S' hom-idˡ ⟩
    S' ⟪ hom-id , _ ⟫ (f $⟨ ρ , eγ ⟩ t')
  ≡⟨ ty-id S' ⟩
    f $⟨ ρ , eγ ⟩ t' ∎)
  where open ≡-Reasoning

Pi-cong-cod : {T : Ty Γ} {S S' : Ty (Γ ,, T)} → S ≅ᵗʸ S' → Pi T S ≅ᵗʸ Pi T S'
Pi-cong-cod eS = Pi-cong reflᵗʸ (transᵗʸ eS (symᵗʸ (transᵗʸ (ty-subst-cong-subst ,,-map-id _) (ty-subst-id _))))

{-
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
-}

module _ (σ : Δ ⇒ Γ) (T : Ty Γ) (S : Ty (Γ ,, T)) {δ : Δ ⟨ z ⟩} where
  pshfun-subst-from : PshFun T S z (func σ δ) → PshFun (T [ σ ]) (S [ σ ⊹ ]) z δ
  pshfun-subst-from f $⟨ ρ-yz , eδ ⟩ t = f $⟨ ρ-yz , trans (naturality σ) (cong (func σ) eδ) ⟩ t
  naturality (pshfun-subst-from f) = trans (trans ($-hom-cong f refl) (naturality f)) (ty-cong S refl)

  pshfun-subst-to : PshFun (T [ σ ]) (S [ σ ⊹ ]) z δ → PshFun T S z (func σ δ)
  _$⟨_,_⟩_ (pshfun-subst-to f) ρ-yz {γ'} eδ t =
    ty-ctx-subst S (to-Σ-ty-eq T proof (trans (ty-cong-2-1 T hom-idˡ) (ty-id T)))
                   (f $⟨ ρ-yz , refl ⟩ ty-ctx-subst T (sym proof) t)
    where
      proof : func σ (Δ ⟪ ρ-yz ⟫ δ) ≡ γ'
      proof = trans (sym (naturality σ)) eδ
  naturality (pshfun-subst-to f) {ρ-xy = ρ-xy} {ρ-yz} {eγ-yx = eγ-yx} {t = t} =
    begin
      S ⟪ hom-id , α ⟫ (f $⟨ ρ-yz ∙ ρ-xy , refl ⟩ (T ⟪ hom-id , _ ⟫ T ⟪ ρ-xy , eγ-yx ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) ($-cong f (ty-cong-2-2 T (trans hom-idˡ (sym hom-idʳ)))) ⟨
      S ⟪ hom-id , α ⟫ S ⟪ hom-id , _ ⟫ (f $⟨ ρ-yz ∙ ρ-xy , refl ⟩ (T ⟪ ρ-xy , _ ⟫ (T ⟪ hom-id , β ⟫ t)))
    ≡⟨ ty-comp S ⟨
      S ⟪ hom-id ∙ hom-id , ε ⟫ (f $⟨ ρ-yz ∙ ρ-xy , refl ⟩ (T ⟪ ρ-xy , _ ⟫ (T ⟪ hom-id , β ⟫ t)))
    ≡⟨ cong (S ⟪ hom-id ∙ hom-id , ε ⟫_) ($-hom-cong f refl) ⟩
      S ⟪ hom-id ∙ hom-id , _ ⟫ (f $⟨ ρ-yz ∙ ρ-xy , _ ⟩ (T ⟪ ρ-xy , _ ⟫ (T ⟪ hom-id , β ⟫ t)))
    ≡⟨ cong (S ⟪ hom-id ∙ hom-id , ε ⟫_) (naturality f {eγ-yx = sym (ctx-comp Δ)}) ⟩
      S ⟪ hom-id ∙ hom-id , _ ⟫ S ⟪ ρ-xy , _ ⟫ (f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , β ⟫ t))
    ≡⟨ ty-cong-2-2 S (trans (trans (cong (ρ-xy ∙_) hom-idˡ) hom-idʳ) (sym hom-idˡ)) ⟩
      S ⟪ ρ-xy , _ ⟫ S ⟪ hom-id , _ ⟫ (f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , β ⟫ t)) ∎
    where
      open ≡-Reasoning
      α = _
      β = _
      ε = _


module _ {T : Ty Γ} {S : Ty (Γ ,, T)} (σ : Δ ⇒ Γ) where
  Pi-natural : (Pi T S) [ σ ] ≅ᵗʸ Pi (T [ σ ]) (S [ σ ⊹ ])
  func (from Pi-natural) = pshfun-subst-from σ T S
  naturality (from Pi-natural) {t = f} = to-pshfun-eq (λ _ _ _ → $-hom-cong f refl)
  func (to Pi-natural) = pshfun-subst-to σ T S
  naturality (to Pi-natural) {_} {_} {ρ-yz} {eγ = eδ-yz} {t = f} = to-pshfun-eq (λ ρ-xy eγ t →
    let α = _
        α' = _
        β = _
        β' = _
        ε = _
        ε' = _
        ζ = _
        θ = _
        eδ-yx : Δ ⟪ hom-id ⟫ (Δ ⟪ ρ-xy ⟫ _) ≡ Δ ⟪ ρ-yz ∙ ρ-xy ⟫ _
        eδ-yx = trans (ctx-id Δ) (sym (trans (ctx-comp Δ) (cong (Δ ⟪ ρ-xy ⟫_) eδ-yz)))
    in begin
      S ⟪ hom-id , α ⟫ (f $⟨ ρ-yz ∙ ρ-xy , β ⟩ (T ⟪ hom-id , ε ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) ($-cong f (ty-cong-2-1 T hom-idʳ)) ⟨
      S ⟪ hom-id , α ⟫ S ⟪ hom-id , _ ⟫ (f $⟨ ρ-yz ∙ ρ-xy , β ⟩ (T ⟪ hom-id , θ ⟫ T ⟪ hom-id , ε' ⟫ t))
    ≡⟨ ty-comp S ⟨
      S ⟪ hom-id ∙ hom-id , ζ ⟫ (f $⟨ ρ-yz ∙ ρ-xy , β ⟩ (T ⟪ hom-id , θ ⟫ T ⟪ hom-id , ε' ⟫ t))
    ≡⟨ cong (S ⟪ hom-id ∙ hom-id , ζ ⟫_) ($-hom-cong f hom-idʳ) ⟨
      S ⟪ hom-id ∙ hom-id , ζ ⟫ (f $⟨ (ρ-yz ∙ ρ-xy) ∙ hom-id , _ ⟩ (T ⟪ hom-id , θ ⟫ T ⟪ hom-id , ε' ⟫ t))
    ≡⟨ cong (S ⟪ hom-id ∙ hom-id , ζ ⟫_) (naturality f {eγ-yx = eδ-yx}) ⟩
      S ⟪ hom-id ∙ hom-id , ζ ⟫ S ⟪ hom-id , _ ⟫ (f $⟨ ρ-yz ∙ ρ-xy , β' ⟩ (T ⟪ hom-id , ε' ⟫ t))
    ≡⟨ ty-cong-2-1 S (trans hom-idˡ hom-idˡ) ⟩
      S ⟪ hom-id , α' ⟫ f $⟨ ρ-yz ∙ ρ-xy , β' ⟩ (T ⟪ hom-id , ε' ⟫ t) ∎)
    where open ≡-Reasoning
  eq (isoˡ Pi-natural) f = to-pshfun-eq (λ ρ-yz eγ t →
    let α = _
        β = _
        ε = _
    in begin
      S ⟪ hom-id , α ⟫ (f $⟨ ρ-yz , β ⟩ (T ⟪ hom-id , ε ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) ($-hom-cong f (sym hom-idʳ)) ⟩
      S ⟪ hom-id , α ⟫ (f $⟨ ρ-yz ∙ hom-id , _ ⟩ (T ⟪ hom-id , ε ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) (naturality f) ⟩
      S ⟪ hom-id , α ⟫ S ⟪ hom-id , _ ⟫ (f $⟨ ρ-yz , eγ ⟩ t)
    ≡⟨ ty-cong-2-1 S hom-idʳ ⟩
      S ⟪ hom-id , _ ⟫ (f $⟨ ρ-yz , eγ ⟩ t)
    ≡⟨ ty-id S ⟩
      f $⟨ ρ-yz , eγ ⟩ t ∎)
    where open ≡-Reasoning
  eq (isoʳ Pi-natural) f = to-pshfun-eq (λ ρ-yz eδ t →
    let α = _
        β = _
        ε = _
        ζ = _
        θ = _
    in begin
      S ⟪ hom-id , α ⟫ (f $⟨ ρ-yz , refl ⟩ (T ⟪ hom-id , β ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) ($-hom-cong f (sym (hom-idʳ))) ⟩
      S ⟪ hom-id , α ⟫ (f $⟨ ρ-yz ∙ hom-id , θ ⟩ (T ⟪ hom-id , β ⟫ t))
    ≡⟨ cong (S ⟪ hom-id , α ⟫_) ($-cong f (ty-cong T refl)) ⟨
      S ⟪ hom-id , α ⟫ S ⟪ hom-id , _ ⟫ (f $⟨ ρ-yz ∙ hom-id , θ ⟩ (T ⟪ hom-id , ζ ⟫ t))
    ≡⟨ ty-comp S ⟨
      S ⟪ hom-id ∙ hom-id , ε ⟫ (f $⟨ ρ-yz ∙ hom-id , θ ⟩ (T ⟪ hom-id , ζ ⟫ t))
    ≡⟨ cong (S ⟪ hom-id ∙ hom-id , ε ⟫_) (naturality f {eγ-yx = trans (ctx-id Δ) (sym eδ)}) ⟩
      S ⟪ hom-id ∙ hom-id , ε ⟫ S ⟪ hom-id , _ ⟫ (f $⟨ ρ-yz , eδ ⟩ t)
    ≡⟨ ty-cong-2-1 S (trans hom-idˡ hom-idˡ) ⟩
      S ⟪ hom-id , _ ⟫ (f $⟨ ρ-yz , eδ ⟩ t)
    ≡⟨ ty-id S ⟩
      f $⟨ ρ-yz , eδ ⟩ t ∎)
    where open ≡-Reasoning

Pi-natural-closed-dom : {T : ClosedTy C} (clT : IsClosedNatural T) {Γ : Ctx C} {S : Ty (Γ ,, T)} (σ : Δ ⇒ Γ) →
                        (Pi T S) [ σ ] ≅ᵗʸ Pi T (S [ lift-cl-subst clT σ ])
Pi-natural-closed-dom clT {S = S} σ =
  transᵗʸ (Pi-natural σ) (Pi-cong (closed-natural clT σ) (symᵗʸ (ty-subst-cong-subst-2-1 S (symˢ (lift-cl-subst-⊹ clT σ)))))

{-
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
  eq (app-natural f t) δ = $-hom-cong (f ⟨ _ , func σ δ ⟩') refl


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
  ≡⟨ $-hom-cong (f ⟨ x , γ ⟩') hom-idʳ ⟩
    f ⟨ x , γ ⟩' $⟨ ρ , eγ ⟩ t ∎)
  where open ≡-Reasoning


--------------------------------------------------
-- Instance of ClosedType

instance
  fun-closed : {A B : ClosedTy C} {{_ : IsClosedNatural A}} {{_ : IsClosedNatural B}} →
               IsClosedNatural (A ⇛ B)
  closed-natural {{fun-closed}} σ = transᵗʸ (⇛-natural σ) (⇛-cong (closed-natural σ) (closed-natural σ))
-}
