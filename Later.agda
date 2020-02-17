module Later where

--------------------------------------------------
-- Later modality for types
--------------------------------------------------
{-
▻ : {Γ : Ctx ℓ} → Ty Γ → Ty Γ
type (▻ {Γ = Γ} T) = λ { zero _ → Lift _ ⊤ ; (suc n) γ → T ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩ }
morph (▻ {Γ = Γ} T) = λ { z≤n γ → λ _ → lift tt ; (s≤s ineq) γ → {!T ⟪ ineq , Γ ⟪ n≤1+n _ ⟫ γ ⟫!} }
-- morph-id (▻ T) = {!!}
-- morph-comp (▻ T) = {!!}

next : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → Tm Γ (▻ T)
term (next {Γ = Γ} t) = λ { zero γ → lift tt ; (suc n) γ → t ⟨ n , Γ ⟪ n≤1+n n ⟫ γ ⟩' }
naturality (next t) = λ ineq γ → {!!}
-}
