module Experimental.DependentTypes.DeepEmbedding.Alternative1 where

open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory as M
open import Model.CwF-Structure as M hiding (_,,_)
open import Model.Type.Constant as M
open import Model.Type.Function as M hiding (_⇛_)
open import Model.Type.Product as M hiding (_⊠_)

import Experimental.DependentTypes.Model.IdentityType.AlternativeTerm as M

open import Experimental.DependentTypes.DeepEmbedding.Syntax.UnannotatedIdentity
open import MSTT.TCMonad


interpret-ctx : CtxExpr → TCM (Ctx ★)
inspect-interpret-ctx : (Γ : CtxExpr) → Reveal interpret-ctx · Γ is interpret-ctx Γ
interpret-ty : TyExpr → (Γ : CtxExpr) (sΓ : Ctx ★) → interpret-ctx Γ ≡ ok sΓ → TCM (Ty sΓ)
ty-eq? : (T S : TyExpr) (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : interpret-ctx Γ ≡ ok sΓ)
         (sT sS : Ty sΓ) → interpret-ty T Γ sΓ Γ-ok ≡ ok sT → interpret-ty S Γ sΓ Γ-ok ≡ ok sS →
         TCM (sT ≅ᵗʸ sS)
record InferInterpretResult (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : interpret-ctx Γ ≡ ok sΓ) : Set₁
infer-interpret-tm : TmExpr → (Γ : CtxExpr) (sΓ : Ctx ★) (Γ-ok : interpret-ctx Γ ≡ ok sΓ) → TCM (InferInterpretResult Γ sΓ Γ-ok)

record InferInterpretResult Γ sΓ Γ-ok where
  pattern
  constructor tm-result
  field
    T : TyExpr
    sT : Ty sΓ
    type-valid : interpret-ty T Γ sΓ Γ-ok ≡ ok sT
    interpretation : Tm sΓ sT

interpret-ctx ◇ = return M.◇
interpret-ctx (Γ ,, T) with interpret-ctx Γ | inspect-interpret-ctx Γ
interpret-ctx (Γ ,, T) | type-error m | _ = type-error m
interpret-ctx (Γ ,, T) | ok sΓ        | [ Γ-ok ] with interpret-ty T Γ sΓ Γ-ok
interpret-ctx (Γ ,, T) | ok sΓ        | [ Γ-ok ] | type-error m = type-error m
interpret-ctx (Γ ,, T) | ok sΓ        | [ Γ-ok ] | ok sT = return (sΓ M.,, sT)

inspect-interpret-ctx Γ = [ refl ]

interpret-ty Nat Γ sΓ Γ-ok = return M.Nat'
interpret-ty Bool Γ sΓ Γ-ok = return M.Bool'
interpret-ty (T ⇛ S) Γ sΓ Γ-ok = do
  sT ← interpret-ty T Γ sΓ Γ-ok
  sS ← interpret-ty S Γ sΓ Γ-ok
  return (sT M.⇛ sS)
interpret-ty (T ⊠ S) Γ sΓ Γ-ok = do
  sT ← interpret-ty T Γ sΓ Γ-ok
  sS ← interpret-ty S Γ sΓ Γ-ok
  return (sT M.⊠ sS)
interpret-ty (Id t s) Γ sΓ Γ-ok = do
  tm-result T sT T-ok ⟦t⟧ ← infer-interpret-tm t Γ sΓ Γ-ok
  tm-result S sS S-ok ⟦s⟧ ← infer-interpret-tm s Γ sΓ Γ-ok
  sT=sS ← ty-eq? T S Γ sΓ Γ-ok sT sS T-ok S-ok
  return (M.Id ⟦t⟧ (ι[ sT=sS ] ⟦s⟧))

ty-eq? Nat Nat Γ sΓ Γ-ok .Nat' .Nat' refl refl = return reflᵗʸ
ty-eq? Bool Bool Γ sΓ Γ-ok .Bool' .Bool' refl refl = return reflᵗʸ
ty-eq? (T1 ⇛ T2) (S1 ⇛ S2) Γ sΓ Γ-ok sT sS T-ok S-ok with interpret-ty T1 Γ sΓ Γ-ok in eqT1 | interpret-ty T2 Γ sΓ Γ-ok in eqT2 | interpret-ty S1 Γ sΓ Γ-ok in eqS1 | interpret-ty S2 Γ sΓ Γ-ok in eqS2
ty-eq? (T1 ⇛ T2) (S1 ⇛ S2) Γ sΓ Γ-ok .(sT1 M.⇛ sT2) .(sS1 M.⇛ sS2) refl refl | ok sT1 | ok sT2 | ok sS1 | ok sS2 = do
  T1=S1 ← ty-eq? T1 S1 Γ sΓ Γ-ok sT1 sS1 eqT1 eqS1
  T2=S2 ← ty-eq? T2 S2 Γ sΓ Γ-ok sT2 sS2 eqT2 eqS2
  return (⇛-cong T1=S1 T2=S2)
ty-eq? (T1 ⊠ T2) (S1 ⊠ S2) Γ sΓ Γ-ok sT sS T-ok S-ok with interpret-ty T1 Γ sΓ Γ-ok in eqT1 | interpret-ty T2 Γ sΓ Γ-ok in eqT2 | interpret-ty S1 Γ sΓ Γ-ok in eqS1 | interpret-ty S2 Γ sΓ Γ-ok in eqS2
ty-eq? (T1 ⊠ T2) (S1 ⊠ S2) Γ sΓ Γ-ok .(sT1 M.⊠ sT2) .(sS1 M.⊠ sS2) refl refl | ok sT1 | ok sT2 | ok sS1 | ok sS2 = do
  T1=S1 ← ty-eq? T1 S1 Γ sΓ Γ-ok sT1 sS1 eqT1 eqS1
  T2=S2 ← ty-eq? T2 S2 Γ sΓ Γ-ok sT2 sS2 eqT2 eqS2
  return (⊠-cong T1=S1 T2=S2)
ty-eq? (Id t1 t2) (Id s1 s2) Γ sΓ Γ-ok sT sS T-ok S-ok = {!!}
ty-eq? T S Γ sΓ Γ-ok sT sS T-ok S-ok = type-error ""

infer-interpret-tm = {!!}
