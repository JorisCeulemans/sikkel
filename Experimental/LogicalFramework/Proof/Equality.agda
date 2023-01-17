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
★ =m? ★ = return refl
ω =m? ω = return refl
_ =m? _ = throw-error "Modes are not equal."


modality-msg : ErrorMsg
modality-msg = "Modalities are not equal."

_=mod?_ : (μ κ : Modality m n) → PCM (μ Ag.≡ κ)
𝟙 =mod? 𝟙 = return refl
non-triv nt-forever =mod? non-triv nt-forever = return refl
non-triv later^[ k ]ⓜconstantly =mod? non-triv later^[ l ]ⓜconstantly = do
  refl ← from-dec modality-msg (k Nat.≟ l)
  return refl
non-triv later^[1+ k ] =mod? non-triv later^[1+ l ] = do
  refl ← from-dec modality-msg (k Nat.≟ l)
  return refl
non-triv later^[ k ]ⓜconstantlyⓜforever =mod? non-triv later^[ l ]ⓜconstantlyⓜforever = do
  refl ← from-dec modality-msg (k Nat.≟ l)
  return refl
_ =mod? _ = throw-error modality-msg

_=c?_ : (α β : TwoCell μ κ) → PCM (α Ag.≡ β)
id𝟙 =c? id𝟙 = return refl
ltrⓜcst ineq1 =c? ltrⓜcst ineq2 = return (Ag.cong ltrⓜcst (≤-irrelevant ineq1 ineq2))
id-frv =c? id-frv = return refl
ltr ineq1 =c? ltr ineq2 = return (Ag.cong ltr (≤-irrelevant ineq1 ineq2))
𝟙≤ltr =c? 𝟙≤ltr = return refl
ltrⓜcstⓜfrv ineq1 =c? ltrⓜcstⓜfrv ineq2 = return (Ag.cong ltrⓜcstⓜfrv (≤-irrelevant ineq1 ineq2))
cstⓜfrv≤𝟙 =c? cstⓜfrv≤𝟙 = return refl
cstⓜfrv≤ltr ineq1 =c? cstⓜfrv≤ltr ineq2 = return (Ag.cong cstⓜfrv≤ltr (≤-irrelevant ineq1 ineq2))

show-ty : Ty m → String
show-ty Nat' = "ℕ"
show-ty Bool' = "Bool"
show-ty (⟨ μ ∣ T ⟩⇛ S) = "⟨ _ ∣ " ++ show-ty T ++ " ⟩→ " ++ show-ty S
show-ty (T ⊠ S) = show-ty T ++ " × " ++ show-ty S
show-ty ⟨ μ ∣ T ⟩ = "⟨ _ ∣ " ++ show-ty T ++ " ⟩"

_=T?_ : (T S : Ty m) → PCM (T Ag.≡ S)
Nat' =T? Nat' = return refl
Bool' =T? Bool' = return refl
(⟨ μ ∣ T1 ⟩⇛ T2) =T? (⟨ ρ ∣ S1 ⟩⇛ S2) = do
  refl ← mod-dom μ =m? mod-dom ρ
  refl ← μ =mod? ρ
  refl ← T1 =T? S1
  refl ← T2 =T? S2
  return refl
(T1 ⊠ T2) =T? (S1 ⊠ S2) =  do
  refl ← T1 =T? S1
  refl ← T2 =T? S2
  return refl
⟨_∣_⟩ {n = n} μ T =T? ⟨_∣_⟩ {n = n'} κ S = do
  refl ← n =m? n'
  refl ← μ =mod? κ
  refl ← T =T? S
  return refl
T =T? S = throw-error ("Types are not equal: " ++ show-ty T ++ " != " ++ show-ty S)


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
is-lockskip? (skip-lock ρ v) = return (is-lock-skip ρ _ _ refl refl v refl)
is-lockskip? _ = throw-error "Expected a lock-skip in the De Bruijn representation of the variable."

_=v?_ : (v w : Var x μ T κ Γ) → PCM (v Ag.≡ w)
vzero =v? vzero = return refl
vsuc v =v? (vsuc w) = do
  refl ← v =v? w
  return refl
skip-lock {κ = κ} ρ v =v? w = do
  is-lock-skip _ κ' _ refl mod-eq w' var-eq ← is-lockskip? w
  refl ← κ =mod? κ'
  refl ← v =v? w'
  return (Ag.trans (bisubst-uip (Var _ _ _) mod-eq refl (skip-lock ρ v)) var-eq)
_ =v? _ = throw-error "Variables are not equal."


tm-msg : ErrorMsg
tm-msg = "Terms are not equal."

_=t?_ : (t s : Tm Γ T) → PCM (t Ag.≡ s)
var' {n = n} {κ = κ} {μ = μ} x {v} α =t? var' {n = n'} {κ = κ'} {μ = μ'} y {w} β = do
  refl ← from-dec tm-msg (x Str.≟ y)
  refl ← n =m? n'
  refl ← κ =mod? κ'
  refl ← μ =mod? μ'
  refl ← v =v? w
  refl ← α =c? β
  return refl
(mod⟨ μ ⟩ t) =t? (mod⟨ μ ⟩ s) = do
  refl ← t =t? s
  return refl
mod-elim {o = o} {n = n} {T = T} ρ1 ρ2 x t1 t2 =t? mod-elim {o = o'} {n = n'} {T = T'} κ1 κ2 y s1 s2 = do
  refl ← o =m? o'
  refl ← n =m? n'
  refl ← ρ1 =mod? κ1
  refl ← ρ2 =mod? κ2
  refl ← from-dec tm-msg (x Str.≟ y)
  refl ← T =T? T'
  refl ← t1 =t? s1
  refl ← t2 =t? s2
  return refl
(lam[ μ ∣ x ∈ T ] t) =t? (lam[ ρ ∣ y ∈ S ] s) = do
  refl ← from-dec tm-msg (x Str.≟ y)
  refl ← T =T? S
  refl ← t =t? s
  return refl
(_∙_ {T = T} {μ = μ} f t) =t? (_∙_ {T = T'} {μ = μ'} f' t') = do
  refl ← mod-dom μ =m? mod-dom μ'
  refl ← μ =mod? μ'
  refl ← T =T? T'
  refl ← f =t? f'
  refl ← t =t? t'
  return refl
zero =t? zero = return refl
suc m =t? suc n = do
  refl ← m =t? n
  return refl
nat-elim z s n =t? nat-elim z' s' n' = do
  refl ← z =t? z'
  refl ← s =t? s'
  refl ← n =t? n'
  return refl
true =t? true = return refl
false =t? false = return refl
if b t f =t? if b' t' f' = do
  refl ← b =t? b'
  refl ← t =t? t'
  refl ← f =t? f'
  return refl
pair t s =t? pair t' s' = do
  refl ← t =t? t'
  refl ← s =t? s'
  return refl
fst {S = S} p =t? fst {S = S'} p' = do
  refl ← S =T? S'
  refl ← p =t? p'
  return refl
snd {T = T} p =t? snd {T = T'} p' = do
  refl ← T =T? T'
  refl ← p =t? p'
  return refl
_ =t? _ = throw-error tm-msg


frm-msg : ErrorMsg
frm-msg = "Formulas are not equal."

_=f?_ : (φ ψ : Formula Γ) → PCM (φ Ag.≡ ψ)
⊤ᶠ =f? ⊤ᶠ = return refl
⊥ᶠ =f? ⊥ᶠ = return refl
(_≡ᶠ_ {T} t1 t2) =f? (_≡ᶠ_ {S} s1 s2) = do
  refl ← T =T? S
  refl ← t1 =t? s1
  refl ← t2 =t? s2
  return refl
(φ1 ⊃ φ2) =f? (ψ1 ⊃ ψ2) = do
  refl ← φ1 =f? ψ1
  refl ← φ2 =f? ψ2
  return refl
(φ1 ∧ φ2) =f? (ψ1 ∧ ψ2) = do
  refl ← φ1 =f? ψ1
  refl ← φ2 =f? ψ2
  return refl
(∀[_∣_∈_]_ {n = n} μ x T φ) =f? (∀[_∣_∈_]_ {n = n'} κ y S ψ) = do
  refl ← n =m? n'
  refl ← μ =mod? κ
  refl ← from-dec frm-msg (x Str.≟ y)
  refl ← T =T? S
  refl ← φ =f? ψ
  return refl
⟨_∣_⟩ {n = n} μ φ =f? ⟨_∣_⟩ {n = n'} κ ψ = do
  refl ← n =m? n'
  refl ← μ =mod? κ
  refl ← φ =f? ψ
  return refl
_ =f? _ = throw-error frm-msg
