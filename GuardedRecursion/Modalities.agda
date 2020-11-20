{-# OPTIONS --omega-in-omega #-}

module GuardedRecursion.Modalities where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Unit using (⊤; tt)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories
open import CwF-Structure

private
  variable
    ℓ ℓ' ℓc ℓt : Level

module _ where
  private
    variable
      Δ Γ Θ : Ctx ω ℓ

  now : Ctx ω ℓ → Ctx ★ ℓ
  set (now Γ) _ = Γ ⟨ 0 ⟩
  rel (now Γ) _ γ = γ
  rel-id (now Γ) _ = refl
  rel-comp (now Γ) _ _ _ = refl

  now-subst : Δ ⇒ Γ → now Δ ⇒ now Γ
  func (now-subst σ) = func σ
  _⇒_.naturality (now-subst σ) _ = refl

  now-subst-id : now-subst (id-subst Γ) ≅ˢ id-subst (now Γ)
  eq now-subst-id _ = refl

  now-subst-⊚ : (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) → now-subst (σ ⊚ τ) ≅ˢ now-subst σ ⊚ now-subst τ
  eq (now-subst-⊚ σ τ) _ = refl

  timeless-ty : Ty (now Γ) ℓ' → Ty Γ ℓ'
  type (timeless-ty {Γ = Γ} T) n γ = T ⟨ tt , Γ ⟪ z≤n ⟫ γ ⟩
  morph (timeless-ty {Γ = Γ} T) m≤n {γy = γn}{γx = γm} eγ = T ⟪ tt , proof ⟫
    where
      open ≡-Reasoning
      proof : Γ ⟪ z≤n ⟫ γn ≡ Γ ⟪ z≤n ⟫ γm
      proof =
        begin
          Γ ⟪ z≤n ⟫ γn
        ≡⟨⟩
          Γ ⟪ ≤-trans z≤n m≤n ⟫ γn
        ≡⟨ rel-comp Γ z≤n m≤n γn ⟩
          Γ ⟪ z≤n ⟫ (Γ ⟪ m≤n ⟫ γn)
        ≡⟨ cong (Γ ⟪ z≤n ⟫_) eγ ⟩
          Γ ⟪ z≤n ⟫ γm ∎
  morph-cong (timeless-ty T) e = morph-cong T refl
  morph-id (timeless-ty T) t = trans (morph-cong T refl) (morph-id T t)
  morph-comp (timeless-ty T) _ _ _ _ t = trans (morph-cong T refl) (morph-comp T tt tt _ _ t)

  module _ {T : Ty (now Γ) ℓ} where
    timeless-tm : Tm (now Γ) T → Tm Γ (timeless-ty T)
    term (timeless-tm t) n γ = t ⟨ tt , Γ ⟪ z≤n ⟫ γ ⟩'
    Tm.naturality (timeless-tm t) _ _ = Tm.naturality t tt _

    untimeless-tm : Tm Γ (timeless-ty T) → Tm (now Γ) T
    term (untimeless-tm t) _ γ = ctx-element-subst T (rel-id Γ γ) (t ⟨ 0 , γ ⟩')
    Tm.naturality (untimeless-tm t) tt refl = morph-id T _

    timeless-ty-η : (t : Tm Γ (timeless-ty T)) → timeless-tm (untimeless-tm t) ≅ᵗᵐ t
    eq (timeless-ty-η t) {n} γ =
      begin
        T ⟪ tt , rel-id Γ (Γ ⟪ z≤n ⟫ γ) ⟫ (t ⟨ 0 , Γ ⟪ z≤n ⟫ γ ⟩')
      ≡˘⟨ cong (T ⟪ tt , rel-id Γ (Γ ⟪ z≤n ⟫ γ) ⟫_) (Tm.naturality t z≤n refl) ⟩
        T ⟪ tt , rel-id Γ (Γ ⟪ z≤n ⟫ γ) ⟫ T ⟪ tt , _ ⟫ (t ⟨ n , γ ⟩')
      ≡˘⟨ morph-comp T tt tt _ _ (t ⟨ n , γ ⟩') ⟩
        T ⟪ tt , _ ⟫ (t ⟨ n , γ ⟩')
      ≡⟨ morph-cong T refl ⟩
        T ⟪ tt , _ ⟫ (t ⟨ n , γ ⟩')
      ≡⟨ Tm.naturality t ≤-refl (rel-id Γ γ) ⟩
        t ⟨ n , γ ⟩' ∎
      where open ≡-Reasoning

    timeless-ty-β : (t : Tm (now Γ) T) → untimeless-tm (timeless-tm t) ≅ᵗᵐ t
    eq (timeless-ty-β t) γ = Tm.naturality t tt _

  timeless-ty-cong : {T : Ty (now Γ) ℓ} {S : Ty (now Γ) ℓ'} → T ≅ᵗʸ S → timeless-ty T ≅ᵗʸ timeless-ty S
  func (from (timeless-ty-cong T=S)) = func (from T=S)
  CwF-Structure.naturality (from (timeless-ty-cong T=S)) = CwF-Structure.naturality (from T=S)
  func (to (timeless-ty-cong T=S)) = func (to T=S)
  CwF-Structure.naturality (to (timeless-ty-cong T=S)) = CwF-Structure.naturality (to T=S)
  eq (isoˡ (timeless-ty-cong T=S)) = eq (isoˡ T=S)
  eq (isoʳ (timeless-ty-cong T=S)) = eq (isoʳ T=S)

  -- TODO: Show that timeless-tm and untimeless-tm are congruent as well.

  timeless-ty-natural : (σ : Δ ⇒ Γ) (T : Ty (now Γ) ℓ) → (timeless-ty T) [ σ ] ≅ᵗʸ timeless-ty (T [ now-subst σ ])
  func (from (timeless-ty-natural σ T)) = ctx-element-subst T (_⇒_.naturality σ _)
  CwF-Structure.naturality (from (timeless-ty-natural σ T)) t =
    begin
      T ⟪ tt , _ ⟫ (T ⟪ tt , _⇒_.naturality σ _ ⟫ t)
    ≡˘⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-cong T refl ⟩ -- no refl here because proofs don't match
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , _⇒_.naturality σ _ ⟫ (T ⟪ tt , _ ⟫ t) ∎
    where open ≡-Reasoning
  func (to (timeless-ty-natural σ T)) = ctx-element-subst T (sym (_⇒_.naturality σ _))
  CwF-Structure.naturality (to (timeless-ty-natural σ T)) t =
    begin
      T ⟪ tt , _ ⟫ (T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ t)
    ≡˘⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-cong T refl ⟩ -- no refl here because proofs don't match
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ (T ⟪ tt , _ ⟫ t) ∎
    where open ≡-Reasoning
  eq (isoˡ (timeless-ty-natural σ T)) t =
    begin
      T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ (T ⟪ tt , _⇒_.naturality σ _ ⟫ t)
    ≡˘⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-cong T refl ⟩
      T ⟪ tt , refl ⟫ t
    ≡⟨ morph-id T t ⟩
      t ∎
    where open ≡-Reasoning
  eq (isoʳ (timeless-ty-natural σ T)) t =
    begin
      T ⟪ tt , _⇒_.naturality σ _ ⟫ (T ⟪ tt , sym (_⇒_.naturality σ _) ⟫ t)
    ≡˘⟨ morph-comp T tt tt _ _ t ⟩
      T ⟪ tt , _ ⟫ t
    ≡⟨ morph-cong T refl ⟩
      T ⟪ tt , refl ⟫ t
    ≡⟨ morph-id T t ⟩
      t ∎
    where open ≡-Reasoning

  timeless-tm-natural : (σ : Δ ⇒ Γ) {T : Ty (now Γ) ℓ} (t : Tm (now Γ) T) →
                    (timeless-tm t) [ σ ]' ≅ᵗᵐ ι[ timeless-ty-natural σ T ] timeless-tm (t [ now-subst σ ]')
  eq (timeless-tm-natural σ t) δ = sym (Tm.naturality t tt _)

  untimeless-tm-natural : (σ : Δ ⇒ Γ) {T : Ty (now Γ) ℓ} (t : Tm Γ (timeless-ty T)) →
                   (untimeless-tm t) [ now-subst σ ]' ≅ᵗᵐ untimeless-tm (ι⁻¹[ timeless-ty-natural σ T ] (t [ σ ]'))
  eq (untimeless-tm-natural {Δ = Δ}{Γ = Γ} σ {T = T} t) δ =
    begin
      T ⟪ tt , rel-id Γ (func σ δ) ⟫ (t ⟨ 0 , func σ δ ⟩')
    ≡⟨ morph-cong T refl ⟩
      T ⟪ tt , _ ⟫ (t ⟨ 0 , func σ δ ⟩')
    ≡⟨ morph-comp T tt tt _ _ _ ⟩
      T ⟪ tt , cong (func σ) (rel-id Δ δ) ⟫ (T ⟪ tt , _⇒_.naturality σ δ ⟫ (t ⟨ 0 , func σ δ ⟩')) ∎
    where open ≡-Reasoning


module _ where
  private
    variable
      Δ Γ Θ : Ctx ★ ℓ

  timeless-ctx : Ctx ★ ℓ → Ctx ω ℓ
  set (timeless-ctx Γ) _ = Γ ⟨ tt ⟩
  rel (timeless-ctx Γ) _ γ = γ
  rel-id (timeless-ctx Γ) _ = refl
  rel-comp (timeless-ctx Γ) _ _ _ = refl

  timeless-subst : Δ ⇒ Γ → timeless-ctx Δ ⇒ timeless-ctx Γ
  func (timeless-subst σ) = func σ
  _⇒_.naturality (timeless-subst σ) _ = refl

  timeless-subst-id : timeless-subst (id-subst Γ) ≅ˢ id-subst (timeless-ctx Γ)
  eq timeless-subst-id _ = refl

  timeless-subst-⊚ : (σ : Γ ⇒ Θ) (τ : Δ ⇒ Γ) → timeless-subst (σ ⊚ τ) ≅ˢ timeless-subst σ ⊚ timeless-subst τ
  eq (timeless-subst-⊚ σ τ) _ = refl

  const-subst : Γ ⟨ tt ⟩ → ◇ ⇒ timeless-ctx Γ
  func (const-subst γ) _ = γ
  _⇒_.naturality (const-subst γ) _ = refl

  const-subst-cong : {γ1 γ2 : Γ ⟨ tt ⟩} → γ1 ≡ γ2 → const-subst {Γ = Γ} γ1 ≅ˢ const-subst γ2
  eq (const-subst-cong eγ) tt = eγ

  const-subst-natural : (δ : Δ ⟨ tt ⟩) (σ : Δ ⇒ Γ) → timeless-subst σ ⊚ const-subst δ ≅ˢ const-subst (func σ δ)
  eq (const-subst-natural δ σ) _ = refl

  global-ty : Ty (timeless-ctx Γ) ℓ → Ty Γ ℓ
  type (global-ty T) tt γ = Tm ◇ (T [ const-subst γ ])
  morph (global-ty {Γ = Γ} T) tt {γ}{γ'} eγ t = ι⁻¹[ proof ] t
    where
      proof : T [ const-subst γ ] ≅ᵗʸ T [ const-subst γ' ]
      proof = ty-subst-cong-subst (const-subst-cong (trans (sym (rel-id Γ γ)) eγ)) T
  morph-cong (global-ty T) _ = tm-≅-to-≡ (record { eq = λ _ → morph-cong T refl })
  morph-id (global-ty T) _ = tm-≅-to-≡ (record { eq = λ _ → trans (morph-cong T refl) (morph-id T _) })
  morph-comp (global-ty T) tt tt eγ-zy eγ-yx t = tm-≅-to-≡
    (record { eq = λ _ → trans (morph-cong T (≤-irrelevant _ _)) (morph-comp T ≤-refl ≤-refl _ _ _) })

  module _ {T : Ty (timeless-ctx Γ) ℓ} where
    global-tm : Tm (timeless-ctx Γ) T → Tm Γ (global-ty T)
    term (term (global-tm t) tt γ) n tt = t ⟨ n , γ ⟩'
    Tm.naturality (term (global-tm t) tt γ) m≤n refl = Tm.naturality t m≤n refl
    Tm.naturality (global-tm t) tt refl = tm-≅-to-≡ (record { eq = λ _ → Tm.naturality t ≤-refl _ })

    unglobal-tm : Tm Γ (global-ty T) → Tm (timeless-ctx Γ) T
    term (unglobal-tm t) n γ = t ⟨ tt , γ ⟩' ⟨ n , tt ⟩'
    Tm.naturality (unglobal-tm t) m≤n refl = Tm.naturality (t ⟨ tt , _ ⟩') m≤n refl

    global-ty-β : (t : Tm (timeless-ctx Γ) T) → unglobal-tm (global-tm t) ≅ᵗᵐ t
    eq (global-ty-β t) _ = refl

    global-ty-η : (t : Tm Γ (global-ty T)) → global-tm (unglobal-tm t) ≅ᵗᵐ t
    eq (global-ty-η t) γ = tm-≅-to-≡ (record { eq = λ { tt → refl } })

  global-ty-cong : {T : Ty (timeless-ctx Γ) ℓ} {S : Ty (timeless-ctx Γ) ℓ'} →
                   T ≅ᵗʸ S → global-ty T ≅ᵗʸ global-ty S
  func (from (global-ty-cong T=S)) = ι⁻¹[ ty-subst-cong-ty (const-subst _) T=S ]_
  CwF-Structure.naturality (from (global-ty-cong T=S)) _ = tm-≅-to-≡ (record { eq = λ _ → CwF-Structure.naturality (from T=S) _ })
  func (to (global-ty-cong T=S)) = ι[ ty-subst-cong-ty (const-subst _) T=S ]_
  CwF-Structure.naturality (to (global-ty-cong T=S)) _ = tm-≅-to-≡ (record { eq = λ _ → CwF-Structure.naturality (to T=S) _ })
  eq (isoˡ (global-ty-cong T=S)) _ = tm-≅-to-≡ (ι-symʳ (ty-subst-cong-ty (const-subst _) T=S) _)
  eq (isoʳ (global-ty-cong T=S)) _ = tm-≅-to-≡ (ι-symˡ (ty-subst-cong-ty (const-subst _) T=S) _)

  ty-const-subst : (T : Ty (timeless-ctx Γ) ℓ) (σ : Δ ⇒ Γ) (δ : Δ ⟨ tt ⟩) →
                   (T [ timeless-subst σ ]) [ const-subst δ ] ≅ᵗʸ T [ const-subst (func σ δ) ]
  ty-const-subst T σ δ = ≅ᵗʸ-trans (ty-subst-comp T (timeless-subst σ) (const-subst _))
                                   (ty-subst-cong-subst (const-subst-natural _ σ) T)

  global-ty-natural : (σ : Δ ⇒ Γ) (T : Ty (timeless-ctx Γ) ℓ) → (global-ty T) [ σ ] ≅ᵗʸ global-ty (T [ timeless-subst σ ])
  func (from (global-ty-natural σ T)) = ι[ ty-const-subst T σ _ ]_
  CwF-Structure.naturality (from (global-ty-natural σ T)) t = tm-≅-to-≡ (record { eq = λ _ → 
    trans (sym (morph-comp T _ _ _ _ _)) (trans (morph-cong T refl) (morph-comp T _ _ _ _ _)) })
  func (to (global-ty-natural σ T)) = ι⁻¹[ ty-const-subst T σ _ ]_
  CwF-Structure.naturality (to (global-ty-natural σ T)) t = tm-≅-to-≡ (record { eq = λ _ →
    trans (sym (morph-comp T _ _ _ _ _)) (trans (morph-cong T refl) (morph-comp T _ _ _ _ _)) })
  eq (isoˡ (global-ty-natural σ T)) t = tm-≅-to-≡ (ι-symˡ (ty-const-subst T σ _) t)
  eq (isoʳ (global-ty-natural σ T)) t = tm-≅-to-≡ (ι-symʳ (ty-const-subst T σ _) t)

  module _ (σ : Δ ⇒ Γ) {T : Ty (timeless-ctx Γ) ℓ} where
    global-tm-natural : (t : Tm (timeless-ctx Γ) T) →
                          (global-tm t) [ σ ]' ≅ᵗᵐ ι[ global-ty-natural σ T ] global-tm (t [ timeless-subst σ ]')
    eq (global-tm-natural t) _ = tm-≅-to-≡ (record { eq = λ _ → sym (morph-id T _) })

    unglobal-tm-natural : (t : Tm Γ (global-ty T)) →
                            (unglobal-tm t) [ timeless-subst σ ]' ≅ᵗᵐ unglobal-tm (ι⁻¹[ global-ty-natural σ T ] (t [ σ ]'))
    eq (unglobal-tm-natural t) _ = sym (morph-id T _)


open import GuardedRecursion.Later
import Data.Unit.Polymorphic as PolyUnit

earlier-timeless-ctx : {Γ : Ctx ★ ℓ} → ◄ (timeless-ctx Γ) ≅ᶜ timeless-ctx Γ
func (from (earlier-timeless-ctx {Γ = Γ})) γ = γ
_⇒_.naturality (from (earlier-timeless-ctx {Γ = Γ})) _ = refl
func (to (earlier-timeless-ctx {Γ = Γ})) γ = γ
_⇒_.naturality (to (earlier-timeless-ctx {Γ = Γ})) _ = refl
eq (isoˡ (earlier-timeless-ctx {Γ = Γ})) _ = refl
eq (isoʳ (earlier-timeless-ctx {Γ = Γ})) _ = refl

global-later-ty : {Γ : Ctx ★ ℓc} (T : Ty (timeless-ctx Γ) ℓt) →
                  global-ty T ≅ᵗʸ global-ty (▻ (T [ from-earlier (timeless-ctx Γ) ]))
term (func (from (global-later-ty T)) t) zero _ = PolyUnit.tt
term (func (from (global-later-ty T)) t) (suc n) _ = t ⟨ n , tt ⟩'
Tm.naturality (func (from (global-later-ty T)) t) z≤n _ = refl
Tm.naturality (func (from (global-later-ty T)) t) (_≤_.s≤s m≤n) _ = trans (morph-cong T refl) (Tm.naturality t m≤n refl)
CwF-Structure.naturality (from (global-later-ty T)) t = tm-≅-to-≡ (record { eq =  λ { {zero} _ → refl ; {suc n} _ → morph-cong T refl } })
term (func (to (global-later-ty T)) t) n _ = t ⟨ suc n , tt ⟩'
Tm.naturality (func (to (global-later-ty T)) t) m≤n _ = trans (morph-cong T refl) (Tm.naturality t (_≤_.s≤s m≤n) refl)
CwF-Structure.naturality (to (global-later-ty T)) t = tm-≅-to-≡ (record { eq = λ _ → morph-cong T refl })
eq (isoˡ (global-later-ty T)) t = tm-≅-to-≡ (record { eq = λ _ → refl })
eq (isoʳ (global-later-ty T)) t = tm-≅-to-≡ (record { eq = λ { {zero} _ → refl ; {suc n} _ → refl } })

global-later'-ty : {Γ : Ctx ★ ℓc} (T : Ty (timeless-ctx Γ) ℓt) →
                   global-ty T ≅ᵗʸ global-ty (▻' T)
global-later'-ty = global-later-ty


open import GuardedRecursion.GuardedStreams renaming (Stream to GuardedStream; stream-nul to guarded-stream-nul)
open import Types.Functions
open import Types.Discrete
open import Types.Products
open import Reflection.Naturality
open import Reflection.Tactic.Lambda
open import Reflection.Naturality.Instances

instance
  now-functor : IsCtxFunctor now
  IsCtxFunctor.ctx-map now-functor = now-subst
  IsCtxFunctor.ctx-map-id now-functor = now-subst-id
  IsCtxFunctor.ctx-map-⊚ now-functor = now-subst-⊚
  
  timeless-ty-un : IsUnaryNatural timeless-ty
  IsUnaryNatural.natural-un timeless-ty-un = λ σ → timeless-ty-natural σ _
  IsUnaryNatural.cong-un timeless-ty-un = timeless-ty-cong

  timeless-ctx-functor : IsCtxFunctor timeless-ctx
  IsCtxFunctor.ctx-map timeless-ctx-functor = timeless-subst
  IsCtxFunctor.ctx-map-id timeless-ctx-functor = timeless-subst-id
  IsCtxFunctor.ctx-map-⊚ timeless-ctx-functor = timeless-subst-⊚

  global-ty-un : IsUnaryNatural global-ty
  IsUnaryNatural.natural-un global-ty-un = λ σ → global-ty-natural σ _
  IsUnaryNatural.cong-un global-ty-un = global-ty-cong

discr-global : {Γ : Ctx ★ ℓc} {A : Set ℓ} →
               global-ty (Discr A) ≅ᵗʸ Discr {Γ = Γ} A
func (from discr-global) t = t ⟨ 0 , tt ⟩'
CwF-Structure.naturality (from discr-global) _ = refl
term (func (to discr-global) a) n _ = a
Tm.naturality (func (to discr-global) a) _ _ = refl
CwF-Structure.naturality (to discr-global) a = tm-≅-to-≡ (record { eq = λ _ → refl })
eq (isoˡ discr-global) t = tm-≅-to-≡ (record { eq = λ _ → sym (Tm.naturality t z≤n refl) })
eq (isoʳ discr-global) _ = refl

module _ where
  private
    variable
      Γ : Ctx ★ ℓ
      
  Stream : Ty Γ 0ℓ
  Stream = global-ty GuardedStream

  instance
    stream-nul : IsNullaryNatural Stream
    IsNullaryNatural.natural-nul stream-nul σ = ≅ᵗʸ-trans (global-ty-natural σ GuardedStream)
                                                         (global-ty-cong (stream-natural (timeless-subst σ)))

  {-
  head : Tm Γ Stream → Tm Γ Nat'
  head s = ι⁻¹[ discr-global ] global-tm (str-head $ unglobal-tm s)
  -}

  head : Tm Γ (Stream ⇛ Nat')
  head = lamι Stream (ι⁻¹[ discr-global ] global-tm (str-head $ unglobal-tm (varι 0)))
  
  {-
  tail : Tm Γ Stream → Tm Γ Stream
  tail s = ι[ global-later'-ty GuardedStream ] global-tm (str-tail $ unglobal-tm s)
  -}

  tail : Tm Γ (Stream ⇛ Stream)
  tail = lamι Stream (ι[ global-later'-ty GuardedStream ] global-tm (str-tail $ unglobal-tm (varι 0)))

  cons : Tm Γ Nat' → Tm Γ Stream → Tm Γ Stream
  cons n s = global-tm (str-cons $ pair (unglobal-tm (ι[ discr-global ] n))
                                        (unglobal-tm (ι⁻¹[ global-later'-ty GuardedStream ] s)))
