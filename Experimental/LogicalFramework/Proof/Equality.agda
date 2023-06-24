open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory

module Experimental.LogicalFramework.Proof.Equality (ℳ : ModeTheory) where

open import Data.Nat as Nat hiding (_≟_)
open import Data.Nat.Properties
open import Data.String as Str hiding (_≟_)
open import Relation.Binary.PropositionalEquality as Ag using (refl)

open ModeTheory ℳ

open import Experimental.LogicalFramework.MSTT.Syntax ℳ
open import Experimental.LogicalFramework.bProp.Named ℳ
open import Experimental.LogicalFramework.Proof.CheckingMonad

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  Γ Δ : Ctx m
  T S R U : Ty m
  φ ψ : bProp Γ
  x y : String


_=m?_ : (m n : Mode) → PCM (m Ag.≡ n)
m =m? n = from-maybe "Modes are not equal." (mode-eq? m n)

modality-msg : ErrorMsg
modality-msg = "Modalities are not equal."

_=mod?_ : (μ κ : Modality m n) → PCM (μ Ag.≡ κ)
𝟙 =mod? 𝟙 = return Ag.refl
‵ μ =mod? ‵ κ = do
  refl ← from-maybe modality-msg (non-triv-mod-eq? μ κ)
  return Ag.refl
_ =mod? _ = throw-error modality-msg

_=c?_ : (α β : TwoCell μ κ) → PCM (α Ag.≡ β)
α =c? β = from-maybe "Two-cells are not equal." (two-cell-eq? α β)

show-ty : Ty m → String
show-ty Nat' = "ℕ"
show-ty Bool' = "Bool"
show-ty (⟨ μ ∣ T ⟩⇛ S) = "⟨ _ ∣ " ++ show-ty T ++ " ⟩→ " ++ show-ty S
show-ty (T ⊠ S) = show-ty T ++ " × " ++ show-ty S
show-ty ⟨ μ ∣ T ⟩ = "⟨ _ ∣ " ++ show-ty T ++ " ⟩"

_=T?_ : (T S : Ty m) → PCM (T Ag.≡ S)
Nat' =T? Nat' = return Ag.refl
Bool' =T? Bool' = return Ag.refl
(⟨ μ ∣ T1 ⟩⇛ T2) =T? (⟨ ρ ∣ S1 ⟩⇛ S2) = do
  refl ← mod-dom μ =m? mod-dom ρ
  refl ← μ =mod? ρ
  refl ← T1 =T? S1
  refl ← T2 =T? S2
  return Ag.refl
(T1 ⊠ T2) =T? (S1 ⊠ S2) =  do
  refl ← T1 =T? S1
  refl ← T2 =T? S2
  return Ag.refl
⟨_∣_⟩ {n = n} μ T =T? ⟨_∣_⟩ {n = n'} κ S = do
  refl ← n =m? n'
  refl ← μ =mod? κ
  refl ← T =T? S
  return Ag.refl
T =T? S = throw-error ("Types are not equal: " ++ show-ty T ++ " != " ++ show-ty S)


bisubst : {A B : Set} (C : A → B → Set) {x y : A} {z w : B} → x Ag.≡ y → z Ag.≡ w → C x z → C y w
bisubst C refl refl c = c

bisubst-uip : {A B : Set} (C : A → B → Set) {x : A} {z : B} (p : x Ag.≡ x) (q : z Ag.≡ z) (c : C x z) →
              c Ag.≡ bisubst C p q c
bisubst-uip C refl refl c = Ag.refl

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
is-lockskip? (skip-lock ρ v) = return (is-lock-skip ρ _ _ Ag.refl Ag.refl v Ag.refl)
is-lockskip? _ = throw-error "Expected a lock-skip in the De Bruijn representation of the variable."

_=v?_ : (v w : Var x μ T κ Γ) → PCM (v Ag.≡ w)
vzero =v? vzero = return Ag.refl
vsuc v =v? (vsuc w) = do
  refl ← v =v? w
  return Ag.refl
skip-lock {κ = κ} ρ v =v? w = do
  is-lock-skip _ κ' _ refl mod-eq w' var-eq ← is-lockskip? w
  refl ← κ =mod? κ'
  refl ← v =v? w'
  return (Ag.trans (bisubst-uip (Var _ _ _) mod-eq Ag.refl (skip-lock ρ v)) var-eq)
_ =v? _ = throw-error "Variables are not equal."


tm-msg : ErrorMsg
tm-msg = "Terms are not equal."

infix 10 _=t?_
_=t?_ : (t s : Tm Γ T) → PCM (t Ag.≡ s)
var' {n = n} {κ = κ} {μ = μ} x {v} α =t? var' {n = n'} {κ = κ'} {μ = μ'} y {w} β = do
  refl ← from-dec tm-msg (x Str.≟ y)
  refl ← n =m? n'
  refl ← κ =mod? κ'
  refl ← μ =mod? μ'
  refl ← v =v? w
  refl ← α =c? β
  return Ag.refl
(mod⟨ μ ⟩ t) =t? (mod⟨ μ ⟩ s) = do
  refl ← t =t? s
  return Ag.refl
mod-elim {o = o} {n = n} {T = T} ρ1 ρ2 x t1 t2 =t? mod-elim {o = o'} {n = n'} {T = T'} κ1 κ2 y s1 s2 = do
  refl ← o =m? o'
  refl ← n =m? n'
  refl ← ρ1 =mod? κ1
  refl ← ρ2 =mod? κ2
  refl ← from-dec tm-msg (x Str.≟ y)
  refl ← T =T? T'
  refl ← t1 =t? s1
  refl ← t2 =t? s2
  return Ag.refl
(lam[ μ ∣ x ∈ T ] t) =t? (lam[ ρ ∣ y ∈ S ] s) = do
  refl ← from-dec tm-msg (x Str.≟ y)
  refl ← T =T? S
  refl ← t =t? s
  return Ag.refl
(_∙_ {T = T} {μ = μ} f t) =t? (_∙_ {T = T'} {μ = μ'} f' t') = do
  refl ← mod-dom μ =m? mod-dom μ'
  refl ← μ =mod? μ'
  refl ← T =T? T'
  refl ← f =t? f'
  refl ← t =t? t'
  return Ag.refl
zero =t? zero = return Ag.refl
suc m =t? suc n = do
  refl ← m =t? n
  return Ag.refl
nat-rec z s n =t? nat-rec z' s' n' = do
  refl ← z =t? z'
  refl ← s =t? s'
  refl ← n =t? n'
  return Ag.refl
true =t? true = return Ag.refl
false =t? false = return Ag.refl
if b t f =t? if b' t' f' = do
  refl ← b =t? b'
  refl ← t =t? t'
  refl ← f =t? f'
  return Ag.refl
pair t s =t? pair t' s' = do
  refl ← t =t? t'
  refl ← s =t? s'
  return Ag.refl
fst {S = S} p =t? fst {S = S'} p' = do
  refl ← S =T? S'
  refl ← p =t? p'
  return Ag.refl
snd {T = T} p =t? snd {T = T'} p' = do
  refl ← T =T? T'
  refl ← p =t? p'
  return Ag.refl
_ =t? _ = throw-error tm-msg


bprop-msg : ErrorMsg
bprop-msg = "Propositions are not equal."

infix 10 _=b?_
_=b?_ : (φ ψ : bProp Γ) → PCM (φ Ag.≡ ψ)
⊤ᵇ =b? ⊤ᵇ = return Ag.refl
⊥ᵇ =b? ⊥ᵇ = return Ag.refl
(_≡ᵇ_ {T} t1 t2) =b? (_≡ᵇ_ {S} s1 s2) = do
  refl ← T =T? S
  refl ← t1 =t? s1
  refl ← t2 =t? s2
  return Ag.refl
(⟨ μ ∣ φ1 ⟩⊃ φ2) =b? (⟨ κ ∣ ψ1 ⟩⊃ ψ2) = do
  refl ← mod-dom μ =m? mod-dom κ
  refl ← μ =mod? κ
  refl ← φ1 =b? ψ1
  refl ← φ2 =b? ψ2
  return Ag.refl
(φ1 ∧ φ2) =b? (ψ1 ∧ ψ2) = do
  refl ← φ1 =b? ψ1
  refl ← φ2 =b? ψ2
  return Ag.refl
(∀[_∣_∈_]_ {n = n} μ x T φ) =b? (∀[_∣_∈_]_ {n = n'} κ y S ψ) = do
  refl ← n =m? n'
  refl ← μ =mod? κ
  refl ← from-dec bprop-msg (x Str.≟ y)
  refl ← T =T? S
  refl ← φ =b? ψ
  return Ag.refl
⟨_∣_⟩ {n = n} μ φ =b? ⟨_∣_⟩ {n = n'} κ ψ = do
  refl ← n =m? n'
  refl ← μ =mod? κ
  refl ← φ =b? ψ
  return Ag.refl
_ =b? _ = throw-error bprop-msg
