open import Experimental.LogicalFramework.MSTT.Parameter
open import Experimental.LogicalFramework.Parameter.bPropExtension
open import Data.String

module Experimental.LogicalFramework.Proof.Equality
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 String 𝓉)
  where

open import Data.List using (List; []; _∷_)
open import Data.Nat as Nat hiding (_≟_)
open import Data.Nat.Properties
open import Data.Product using (_,_)
open import Data.String as Str hiding (_≟_)
open import Relation.Binary.PropositionalEquality as Ag using (refl)

open import Model.Helpers -- we need uip for term equality

open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension ℳ
open TyExt 𝒯
open import Experimental.LogicalFramework.MSTT.Parameter.TermExtension ℳ 𝒯 String
open TmExt 𝓉
open import Experimental.LogicalFramework.Parameter.bPropExtension
open bPropExt 𝒷

open import Experimental.LogicalFramework.MSTT.Syntax ℳ 𝒯 𝓉
open import Experimental.LogicalFramework.bProp.Named 𝒫 𝒷
open import Experimental.LogicalFramework.Proof.CheckingMonad

private variable
  m n o p : Mode
  μ ρ κ : Modality m n
  Γ Δ : Ctx m
  T S R U : Ty m
  φ ψ : bProp Γ
  x y : String


_≟var_ : {Λ : LockTele m n} (v w : Var x T Γ Λ) → PCM (v Ag.≡ w)
vzero α ≟var vzero β = do
  refl ← α ≟cell β
  return Ag.refl
vsuc v  ≟var vsuc w  = do
  refl ← v ≟var w
  return Ag.refl
vlock v ≟var vlock w = do
  refl ← v ≟var w
  return Ag.refl
_ ≟var _ = throw-error "Variables are not equal."


tm-msg : ErrorMsg
tm-msg = "Terms are not equal."

infix 10 _≟tm_
_≟tm_ : (t s : Tm Γ T) → PCM (t Ag.≡ s)
ext-tmargs-equal? : ∀ {arginfos} (args1 args2 : ExtTmArgs arginfos Γ) → PCM (args1 Ag.≡ args2)

var' x {v} ≟tm var' y {w} = do
  refl ← from-dec tm-msg (x Str.≟ y)
  refl ← v ≟var w
  return Ag.refl
(mod⟨ μ ⟩ t) ≟tm (mod⟨ μ ⟩ s) = do
  refl ← t ≟tm s
  return Ag.refl
mod-elim {o = o} {n = n} {T = T} ρ1 ρ2 x t1 t2 ≟tm mod-elim {o = o'} {n = n'} {T = T'} κ1 κ2 y s1 s2 = do
  refl ← o ≟mode o'
  refl ← n ≟mode n'
  refl ← ρ1 ≟mod κ1
  refl ← ρ2 ≟mod κ2
  refl ← from-dec tm-msg (x Str.≟ y)
  refl ← T ≟ty T'
  refl ← t1 ≟tm s1
  refl ← t2 ≟tm s2
  return Ag.refl
(lam[ μ ∣ x ∈ T ] t) ≟tm (lam[ ρ ∣ y ∈ S ] s) = do
  refl ← from-dec tm-msg (x Str.≟ y)
  refl ← T ≟ty S
  refl ← t ≟tm s
  return Ag.refl
(_∙_ {T = T} {μ = μ} f t) ≟tm (_∙_ {T = T'} {μ = μ'} f' t') = do
  refl ← mod-dom μ ≟mode mod-dom μ'
  refl ← μ ≟mod μ'
  refl ← T ≟ty T'
  refl ← f ≟tm f'
  refl ← t ≟tm t'
  return Ag.refl
zero ≟tm zero = return Ag.refl
suc m ≟tm suc n = do
  refl ← m ≟tm n
  return Ag.refl
nat-rec z s n ≟tm nat-rec z' s' n' = do
  refl ← z ≟tm z'
  refl ← s ≟tm s'
  refl ← n ≟tm n'
  return Ag.refl
true ≟tm true = return Ag.refl
false ≟tm false = return Ag.refl
if b t f ≟tm if b' t' f' = do
  refl ← b ≟tm b'
  refl ← t ≟tm t'
  refl ← f ≟tm f'
  return Ag.refl
pair t s ≟tm pair t' s' = do
  refl ← t ≟tm t'
  refl ← s ≟tm s'
  return Ag.refl
fst {S = S} p ≟tm fst {S = S'} p' = do
  refl ← S ≟ty S'
  refl ← p ≟tm p'
  return Ag.refl
snd {T = T} p ≟tm snd {T = T'} p' = do
  refl ← T ≟ty T'
  refl ← p ≟tm p'
  return Ag.refl
(ext c1 args1 ty-eq1) ≟tm (ext c2 args2 ty-eq2) = do
  refl ← c1 ≟tm-code c2
  refl ← ext-tmargs-equal? args1 args2
  refl ← return (uip ty-eq1 ty-eq2)
  return Ag.refl
_ ≟tm _ = throw-error tm-msg

ext-tmargs-equal? {arginfos = []}                 _              _              = return Ag.refl
ext-tmargs-equal? {arginfos = arginfo ∷ arginfos} (arg1 , args1) (arg2 , args2) =
  Ag.cong₂ _,_ <$> arg1 ≟tm arg2 <*> ext-tmargs-equal? args1 args2


bprop-msg : ErrorMsg
bprop-msg = "Propositions are not equal."

infix 10 _≟bprop_
_≟bprop_ : (φ ψ : bProp Γ) → PCM (φ Ag.≡ ψ)
ext-bpargs-equal? : ∀ {arginfos} (args1 args2 : ExtBPArgs arginfos Γ) → PCM (args1 Ag.≡ args2)

⊤ᵇ ≟bprop ⊤ᵇ = return Ag.refl
⊥ᵇ ≟bprop ⊥ᵇ = return Ag.refl
(_≡ᵇ_ {T} t1 t2) ≟bprop (_≡ᵇ_ {S} s1 s2) = do
  refl ← T ≟ty S
  refl ← t1 ≟tm s1
  refl ← t2 ≟tm s2
  return Ag.refl
(⟨ μ ∣ φ1 ⟩⊃ φ2) ≟bprop (⟨ κ ∣ ψ1 ⟩⊃ ψ2) = do
  refl ← mod-dom μ ≟mode mod-dom κ
  refl ← μ ≟mod κ
  refl ← φ1 ≟bprop ψ1
  refl ← φ2 ≟bprop ψ2
  return Ag.refl
(φ1 ∧ φ2) ≟bprop (ψ1 ∧ ψ2) = do
  refl ← φ1 ≟bprop ψ1
  refl ← φ2 ≟bprop ψ2
  return Ag.refl
(∀[_∣_∈_]_ {n = n} μ x T φ) ≟bprop (∀[_∣_∈_]_ {n = n'} κ y S ψ) = do
  refl ← n ≟mode n'
  refl ← μ ≟mod κ
  refl ← from-dec bprop-msg (x Str.≟ y)
  refl ← T ≟ty S
  refl ← φ ≟bprop ψ
  return Ag.refl
⟨_∣_⟩ {n = n} μ φ ≟bprop ⟨_∣_⟩ {n = n'} κ ψ = do
  refl ← n ≟mode n'
  refl ← μ ≟mod κ
  refl ← φ ≟bprop ψ
  return Ag.refl
(ext c1 tmargs1 bpargs1) ≟bprop (ext c2 tmargs2 bpargs2) = do
  refl ← c1 ≟bp-code c2
  refl ← ext-tmargs-equal? tmargs1 tmargs2
  refl ← ext-bpargs-equal? bpargs1 bpargs2
  return Ag.refl
_ ≟bprop _ = throw-error bprop-msg

ext-bpargs-equal? {arginfos = []}    bps1         bps2         = return Ag.refl
ext-bpargs-equal? {arginfos = _ ∷ _} (bp1 , bps1) (bp2 , bps2) =
  Ag.cong₂ _,_ <$> bp1 ≟bprop bp2 <*> ext-bpargs-equal? bps1 bps2
