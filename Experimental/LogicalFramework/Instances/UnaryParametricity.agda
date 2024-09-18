module Experimental.LogicalFramework.Instances.UnaryParametricity where

import Data.Nat.Properties as Nat
open import Data.Product
open import Data.Product.Properties
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality as Ag

open import Applications.UnaryParametricity.Model

open import Experimental.LogicalFramework.Instances.UnaryParametricity.TypeExtension
open import Experimental.LogicalFramework.Instances.UnaryParametricity.TermExtension
open import Experimental.LogicalFramework.Instances.UnaryParametricity.bPropExtension
open import Experimental.LogicalFramework.Instances.UnaryParametricity.ProofExtension

open import Experimental.LogicalFramework.Parameter



open import Experimental.LogicalFramework.Instances.UnaryParametricity.MSTT public

unary-param-param : BiSikkelParameter
BiSikkelParameter.𝒫 unary-param-param = unary-param-mstt
BiSikkelParameter.𝒷 unary-param-param = unary-param-bp-ext
BiSikkelParameter.⟦𝒷⟧ unary-param-param = unary-param-bp-ext-sem
BiSikkelParameter.𝓅 unary-param-param = unary-param-pf-ext

open import Experimental.LogicalFramework unary-param-param public


pattern Pred A a = ext (bPred-code A) (tt , tt) (a , tt) tt tt
pattern param A = ext (param-code A) tt tt tt tt tt tt
pattern extent-from A B f p = ext (extent-from-code A B) (tt , tt) (f , tt) tt tt (tt , tt) (p , tt)


instance
  pred-extractable : {Γ : Ctx ★} {t : Tm Γ ⟨ forget ∣ EncBool ⟩} {{ _ : ExtractableCtx Γ }} →
                     {{ ExtractableTm t }} →
                     ExtractableProp (Pred EncBool t)
  ExtractableProp.AgdaProp (pred-extractable {t = t}) γ = IsBit (extract-tm t γ)
  ExtractableProp.extract-prop-iso (pred-extractable {t = t}) γ = mk↔ₛ′
    (λ ((n , bit-n) , e) → Ag.subst IsBit (Ag.trans e (Ag.sym (extract-tm-semtm {t = t} γ))) bit-n)
    (λ bit-extr-t → (extract-tm t γ , bit-extr-t) , extract-tm-semtm {t = t} γ)
    (λ x → isbit-hprop)
    (λ ((n , bit-n) , e) → Σ-≡,≡→≡ ((Σ-≡,≡→≡ (Ag.trans (extract-tm-semtm {t = t} γ) (Ag.sym e) , isbit-hprop)) , Nat.≡-irrelevant _ _))
