module Experimental.DeepEmbedding.Parametricity.IntegerExample where

open import Data.Nat
open import Data.Product renaming (_,_ to [_,_])
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories hiding (★; ⋀)
open import CwF-Structure hiding (_,,_; var) renaming (◇ to ′◇)
open import Types.Discrete renaming (Nat' to ′Nat'; Bool' to ′Bool')
open import Types.Functions hiding (lam; lam[_∈_]_) renaming (_⇛_ to _′⇛_)
open import Types.Products hiding (pair; fst; snd) renaming (_⊠_ to _′⊠_)
open import Types.Instances
open import Parametricity.Binary.TypeSystem hiding (FromRel; from-rel; from-rel1; from-rel2; forget-left; forget-right)
open import Parametricity.Binary.IntegerExample using (DiffNat; SignNat; _∼_; _+D_; _+S_; +-preserves-∼; negateD; negateS; negate-preserves-∼)
open import Translation

open import Experimental.DeepEmbedding.Parametricity.TypeChecker.Builtin
open import Experimental.DeepEmbedding.Parametricity.TypeChecker.Monad

data CodeUniv : Set where
  ℤ-code : CodeUniv

builtin : BuiltinTypes
BuiltinTypes.Code builtin = CodeUniv
BuiltinTypes.show-code builtin ℤ-code = "ℤ"
BuiltinTypes._≟code_ builtin ℤ-code ℤ-code = return refl
BuiltinTypes.interpret-code builtin ℤ-code =
  record { Left = DiffNat ; Right = SignNat ; Relation = _∼_ }


open import Experimental.DeepEmbedding.Parametricity.TypeChecker builtin

private
  variable
    m : ModeExpr

-- If Γ ⊢ f : ⟨ μ ∣ A ⇛ B ⟩ and Γ ⊢ t : ⟨ μ ∣ A ⟩, then Γ ⊢ f ⊛⟨ μ ⟩ t : ⟨ μ ∣ B ⟩.
infixl 5 _⊛⟨_⟩_
_⊛⟨_⟩_ : ∀ {m m'} → TmExpr m → ModalityExpr m' m → TmExpr m → TmExpr m
f ⊛⟨ μ ⟩ t = mod-intro μ (mod-elim μ f ∙ mod-elim μ t)

-- If Γ ,lock⟨ μ ⟩ ⊢ f : A ⇛ B and Γ ⊢ t : ⟨ μ ∣ A ⟩, then Γ ⊢ f ⟨$- μ ⟩ t : ⟨ μ ∣ B ⟩.
infixl 5 _⟨$-_⟩_
_⟨$-_⟩_ : ∀ {m m'} → TmExpr m' → ModalityExpr m' m → TmExpr m → TmExpr m
f ⟨$- μ ⟩ t = mod-intro μ (f ∙ mod-elim μ t)


record IntStructure {m} (A : TyExpr m) : Set₁ where
  field
    add : TmExpr m
    negate : TmExpr m
    add-well-typed : ∀ {Γ} → infer-type add Γ ≡ ok (A ⇛ A ⇛ A)
    negate-well-typed : ∀ {Γ} → infer-type negate Γ ≡ ok (A ⇛ A)

open IntStructure {{...}}

subtract : (A : TyExpr m) {{_ : IntStructure A}} → TmExpr m
subtract A = lam[ "a" ∈  A ] lam[ "b" ∈ A ] add ∙ var "a" ∙ (negate ∙ var "b")

ℤ : TyExpr ⋀
ℤ = Builtin ℤ-code

instance
  ℤ-is-int : IntStructure ℤ
  IntStructure.add ℤ-is-int = from-rel2 ℤ-code ℤ-code ℤ-code _+D_ _+S_ +-preserves-∼
  IntStructure.negate ℤ-is-int = from-rel1 ℤ-code ℤ-code negateD negateS negate-preserves-∼
  IntStructure.add-well-typed ℤ-is-int = refl
  IntStructure.negate-well-typed ℤ-is-int = refl

subtract★-left : TmExpr ★
subtract★-left =
  lam[ "i" ∈ ⟨ forget-right ∣ ℤ ⟩ ]
    lam[ "j" ∈ ⟨ forget-right ∣ ℤ ⟩ ]
      subtract ℤ ⟨$- forget-right ⟩ var "i" ⊛⟨ forget-right ⟩ var "j"

subtract★-right : TmExpr ★
subtract★-right =
  lam[ "i" ∈ ⟨ forget-left ∣ ℤ ⟩ ]
    lam[ "j" ∈ ⟨ forget-left ∣ ℤ ⟩ ]
      subtract ℤ ⟨$- forget-left ⟩ var "i" ⊛⟨ forget-left ⟩ var "j"

subtract-DiffNat : DiffNat → DiffNat → DiffNat
subtract-DiffNat = translate-term (⟦ subtract★-left ⟧tm-in ◇)

subtract-SignNat : SignNat → SignNat → SignNat
subtract-SignNat = translate-term (⟦ subtract★-right ⟧tm-in ◇)

subtract-preserves-∼ : (_∼_ ⟨→⟩ _∼_ ⟨→⟩ _∼_) subtract-DiffNat subtract-SignNat
subtract-preserves-∼ {d1}{s1} r1 {d2}{s2} r2 =
  let subtract-ℤ = ⟦ subtract ℤ ⟧tm-in ◇
  in proj₂ ((subtract-ℤ €⟨ relation , tt ⟩ [ [ d1 , s1 ] , r1 ]) $⟨ relation-id , refl ⟩ [ [ d2 , s2 ] , r2 ])
