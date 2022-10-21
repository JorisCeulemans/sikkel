module Experimental.LogicalFramework.Proof.Equality where

open import Data.Nat as Nat hiding (_≟_)
open import Data.Nat.Properties
open import Data.String as Str hiding (_≟_)
open import Relation.Binary.PropositionalEquality as Ag using (refl)

open import Experimental.LogicalFramework.MSTT
open import Experimental.LogicalFramework.Formula
open import Experimental.LogicalFramework.Proof.CheckingMonad

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  Γ Δ : Ctx m
  T S R U : Ty m
  φ ψ : Formula Γ
  x y : String


_=m?_ : (m n : Mode) → PCM (m Ag.≡ n)
★ =m? ★ = ok refl
ω =m? ω = ok refl
_ =m? _ = error "Modes are not equal."

_=mod?_ : (μ κ : Modality m n) → PCM (μ Ag.≡ κ)
𝟙★ =mod? 𝟙★ = ok refl
forever =mod? forever = ok refl
later^[ k ]ⓜconstantly =mod? later^[ l ]ⓜconstantly = do
  refl ← from-dec (k Nat.≟ l)
  ok refl
later^[ k ] =mod? later^[ l ] = do
  refl ← from-dec (k Nat.≟ l)
  ok refl
later^[ k ]ⓜconstantlyⓜforever =mod? later^[ l ]ⓜconstantlyⓜforever = do
  refl ← from-dec (k Nat.≟ l)
  ok refl
_ =mod? _ = error "Modalities are not equal."

_=c?_ : (α β : TwoCell μ κ) → PCM (α Ag.≡ β)
id𝟙★ =c? id𝟙★ = ok refl
ltrⓜcst ineq1 =c? ltrⓜcst ineq2 = ok (Ag.cong ltrⓜcst (≤-irrelevant ineq1 ineq2))
id-frv =c? id-frv = ok refl
ltr ineq1 =c? ltr ineq2 = ok (Ag.cong ltr (≤-irrelevant ineq1 ineq2))
ltrⓜcstⓜfrv ineq1 =c? ltrⓜcstⓜfrv ineq2 = ok (Ag.cong ltrⓜcstⓜfrv (≤-irrelevant ineq1 ineq2))
cstⓜfrv≤𝟙 ineq1 =c? cstⓜfrv≤𝟙 ineq2 = ok (Ag.cong cstⓜfrv≤𝟙 (≤-irrelevant ineq1 ineq2))

show-ty : Ty m → String
show-ty Nat' = "ℕ"
show-ty Bool' = "Bool"
show-ty (T ⇛ S) = show-ty T ++ " → " ++ show-ty S
show-ty (T ⊠ S) = show-ty T ++ " × " ++ show-ty S
show-ty ⟨ μ ∣ T ⟩ = "⟨ _ ∣ " ++ show-ty T ++ " ⟩"

_=T?_ : (T S : Ty m) → PCM (T Ag.≡ S)
Nat' =T? Nat' = ok refl
Bool' =T? Bool' = ok refl
(T1 ⇛ T2) =T? (S1 ⇛ S2) = do
  refl ← T1 =T? S1
  refl ← T2 =T? S2
  ok refl
(T1 ⊠ T2) =T? (S1 ⊠ S2) =  do
  refl ← T1 =T? S1
  refl ← T2 =T? S2
  ok refl
⟨_∣_⟩ {n = n} μ T =T? ⟨_∣_⟩ {n = n'} κ S = do
  refl ← n =m? n'
  refl ← μ =mod? κ
  refl ← T =T? S
  ok refl
T =T? S = error ("Types are not equal: " ++ show-ty T ++ " != " ++ show-ty S)


bisubst : {A B : Set} (C : A → B → Set) {x y : A} {z w : B} → x Ag.≡ y → z Ag.≡ w → C x z → C y w
bisubst C refl refl c = c

bisubst-uip : {A B : Set} (C : A → B → Set) {x : A} {z : B} (p : x Ag.≡ x) (q : z Ag.≡ z) (c : C x z) →
              c Ag.≡ bisubst C p q c
bisubst-uip C refl refl c = refl

record IsLockSkip {μ : Modality p n} {T : Ty p} {κ : Modality m n} {Γ : Ctx m} (v : Var x μ T κ Γ) : Set where
  constructor is-lock-skip
  field
    {lockmode} : Mode
    lockmod : Modality m lockmode
    κ/lockmod : Modality lockmode n
    Γ-unlocked : Ctx lockmode
    ctx-locked : (Γ-unlocked ,lock⟨ lockmod ⟩) Ag.≡ Γ
    mod-eq : κ/lockmod ⓜ lockmod Ag.≡ κ
    locked-var : Var x μ T κ/lockmod Γ-unlocked
    is-locked : bisubst (Var x μ T) mod-eq ctx-locked (skip-lock lockmod locked-var) Ag.≡ v

is-lockskip? : (v : Var x μ T κ Γ) → PCM (IsLockSkip v)
is-lockskip? (skip-lock ρ v) = ok (is-lock-skip ρ _ _ refl refl v refl)
is-lockskip? _ = error "Expected a lock-skip in the De Bruijn representation of the variable."

_=v?_ : (v w : Var x μ T κ Γ) → PCM (v Ag.≡ w)
vzero =v? vzero = ok refl
vsuc v =v? (vsuc w) = do
  refl ← v =v? w
  ok refl
skip-lock {κ = κ} ρ v =v? w = do
  is-lock-skip _ κ' _ refl mod-eq w' var-eq ← is-lockskip? w
  refl ← κ =mod? κ'
  refl ← v =v? w'
  ok (Ag.trans (bisubst-uip (Var _ _ _) mod-eq refl (skip-lock ρ v)) var-eq)
_ =v? _ = error "Variables are not equal."

_=t?_ : (t s : Tm Γ T) → PCM (t Ag.≡ s)
var' {n = n} {κ = κ} {μ = μ} x {v} α =t? var' {n = n'} {κ = κ'} {μ = μ'} y {w} β = do
  refl ← from-dec (x Str.≟ y)
  refl ← n =m? n'
  refl ← κ =mod? κ'
  refl ← μ =mod? μ'
  refl ← v =v? w
  refl ← α =c? β
  ok refl
(mod⟨ μ ⟩ t) =t? (mod⟨ μ ⟩ s) = do
  refl ← t =t? s
  ok refl
mod-elim {o = o} {n = n} {T = T} ρ1 ρ2 x t1 t2 =t? mod-elim {o = o'} {n = n'} {T = T'} κ1 κ2 y s1 s2 = do
  refl ← o =m? o'
  refl ← n =m? n'
  refl ← ρ1 =mod? κ1
  refl ← ρ2 =mod? κ2
  refl ← from-dec (x Str.≟ y)
  refl ← T =T? T'
  refl ← t1 =t? s1
  refl ← t2 =t? s2
  ok refl
(lam[ x ∈ T ] t) =t? (lam[ y ∈ S ] s) = do
  refl ← from-dec (x Str.≟ y)
  refl ← T =T? S
  refl ← t =t? s
  ok refl
(_∙_ {T = T} f t) =t? (_∙_ {T = T'} f' t') = do
  refl ← T =T? T'
  refl ← f =t? f'
  refl ← t =t? t'
  ok refl
zero =t? zero = ok refl
suc =t? suc = ok refl
nat-elim z s =t? nat-elim z' s' = do
  refl ← z =t? z'
  refl ← s =t? s'
  ok refl
true =t? true = ok refl
false =t? false = ok refl
if b t f =t? if b' t' f' = do
  refl ← b =t? b'
  refl ← t =t? t'
  refl ← f =t? f'
  ok refl
pair t s =t? pair t' s' = do
  refl ← t =t? t'
  refl ← s =t? s'
  ok refl
fst {S = S} p =t? fst {S = S'} p' = do
  refl ← S =T? S'
  refl ← p =t? p'
  ok refl
snd {T = T} p =t? snd {T = T'} p' = do
  refl ← T =T? T'
  refl ← p =t? p'
  ok refl
_ =t? _ = error "Terms are not equal."

_=f?_ : (φ ψ : Formula Γ) → PCM (φ Ag.≡ ψ)
⊤ᶠ =f? ⊤ᶠ = ok refl
⊥ᶠ =f? ⊥ᶠ = ok refl
(_≡ᶠ_ {T} t1 t2) =f? (_≡ᶠ_ {S} s1 s2) = do
  refl ← T =T? S
  refl ← t1 =t? s1
  refl ← t2 =t? s2
  ok refl
(φ1 ⊃ φ2) =f? (ψ1 ⊃ ψ2) = do
  refl ← φ1 =f? ψ1
  refl ← φ2 =f? ψ2
  ok refl
(φ1 ∧ φ2) =f? (ψ1 ∧ ψ2) = do
  refl ← φ1 =f? ψ1
  refl ← φ2 =f? ψ2
  ok refl
(∀[_∣_∈_]_ {n = n} μ x T φ) =f? (∀[_∣_∈_]_ {n = n'} κ y S ψ) = do
  refl ← n =m? n'
  refl ← μ =mod? κ
  refl ← from-dec (x Str.≟ y)
  refl ← T =T? S
  refl ← φ =f? ψ
  ok refl
⟨_∣_⟩ {n = n} μ φ =f? ⟨_∣_⟩ {n = n'} κ ψ = do
  refl ← n =m? n'
  refl ← μ =mod? κ
  refl ← φ =f? ψ
  ok refl
_ =f? _ = error "Formulas are not equal."