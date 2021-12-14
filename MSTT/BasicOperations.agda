--------------------------------------------------
-- Some convenient operators for programming in MSTT
--------------------------------------------------

open import MSTT.Parameter.ModeTheory
open import MSTT.Parameter.TypeExtension
open import MSTT.Parameter.TermExtension

module MSTT.BasicOperations (mt : ModeTheory) (ty-ext : TyExt mt) (tm-ext : TmExt mt ty-ext) where

open ModeTheory mt

open import MSTT.Syntax.Type mt ty-ext
open import MSTT.Syntax.Term mt ty-ext tm-ext

private variable
  m m' m'' : ModeExpr


-- Any two-cell α from μ to ρ induces a coercion via coe.
--   If Γ ⊢ t : ⟨ μ ∣ A ⟩, then Γ ⊢ coe[ α ∈ μ ⇒ ρ ] t : ⟨ ρ ∣ A ⟩.
--   No problem arises if t contains a variable named "x" since t is checked in
--   Γ and not Γ , μ ∣ "x" ∈ A.
coe[_∈_⇒_]_ : TwoCellExpr → ModalityExpr m m' → ModalityExpr m m' → TmExpr m' → TmExpr m'
coe[ α ∈ μ ⇒ ρ ] t = let' mod⟨ μ ⟩ "x" ← t in' (mod⟨ ρ ⟩ (var "x" α))


triv : TmExpr m → TmExpr m
triv t = mod⟨ 𝟙 ⟩ t

triv⁻¹ : TmExpr m → TmExpr m
triv⁻¹ t = let' mod⟨ 𝟙 ⟩ "x" ← t in' (svar "x")

comp : ModalityExpr m' m'' → ModalityExpr m m' → TmExpr m'' → TmExpr m''
comp μ ρ t = let' mod⟨ μ ⟩ "x" ← t in'
             let⟨ μ ⟩ mod⟨ ρ ⟩ "y" ← (svar "x") in'
             (mod⟨ μ ⓜ ρ ⟩ svar "y")

comp⁻¹ : ModalityExpr m' m'' → ModalityExpr m m' → TmExpr m'' → TmExpr m''
comp⁻¹ μ ρ t = let' mod⟨ μ ⓜ ρ ⟩ "x" ← t in' (mod⟨ μ ⟩ (mod⟨ ρ ⟩ (svar "x")))

_⊛⟨_⟩_ : TmExpr m' → ModalityExpr m m' → TmExpr m' → TmExpr m'
f ⊛⟨ μ ⟩ t = let' mod⟨ μ ⟩ "f0" ← f in'
             let' mod⟨ μ ⟩ "t0" ← t in'
             (mod⟨ μ ⟩ (svar "f0" ∙ svar "t0"))
