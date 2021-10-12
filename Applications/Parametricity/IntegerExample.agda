--------------------------------------------------
-- An example of representation independence using
-- binary parametricity
--------------------------------------------------

module Applications.Parametricity.IntegerExample where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product renaming (_,_ to [_,_])
open import Data.Unit
open import Level using (0ℓ)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model.BaseCategory hiding (★; ⋀)
open import Model.Type.Function hiding (_⇛_; lam; lam[_∈_]_)
open import Extraction

open import Applications.Parametricity.Model as M using (_⟨→⟩_)
open import Applications.Parametricity.MSTT.TypeExtension.RelExtension
open import MSTT.TCMonad using (return)
import Applications.Parametricity.MSTT


--------------------------------------------------
-- ℕ × ℕ and Sign × ℕ as representations of integers
--   together with the corresponding implementations for
--   addition and negation.

data Sign : Set where
  pos neg : Sign

flipSign : Sign → Sign
flipSign pos = neg
flipSign neg = pos

DiffNat : Set
DiffNat = ℕ × ℕ

SignNat : Set
SignNat = Sign × ℕ

infix 3 _∼_
data _∼_ : REL DiffNat SignNat 0ℓ where
  pos-zero : ∀ {n} → [ n , 0 ] ∼ [ pos , n ]
  neg-zero : ∀ {n} → [ 0 , n ] ∼ [ neg , n ]
  diff-suc : ∀ {m n j} → [ m , n ] ∼ j → [ suc m , suc n ] ∼ j

_+D_ : DiffNat → DiffNat → DiffNat
[ m1 , n1 ] +D [ m2 , n2 ] = [ m1 + m2 , n1 + n2 ]

negateD : DiffNat → DiffNat
negateD [ m , n ] = [ n , m ]

_-_ : ℕ → ℕ → SignNat
m     - zero  = [ pos , m ]
zero  - n     = [ neg , n ]
suc m - suc n = m - n

_+S_ : SignNat → SignNat → SignNat
[ pos , m ] +S [ pos , n ] = [ pos , m + n ]
[ pos , m ] +S [ neg , n ] = m - n
[ neg , m ] +S [ pos , n ] = n - m
[ neg , m ] +S [ neg , n ] = [ neg , m + n ]

negateS : SignNat → SignNat
negateS = map₁ flipSign

negate-preserves-∼ : (_∼_ ⟨→⟩ _∼_) negateD negateS
negate-preserves-∼ pos-zero = neg-zero
negate-preserves-∼ neg-zero = pos-zero
negate-preserves-∼ (diff-suc r) = diff-suc (negate-preserves-∼ r)

difference-∼ : ∀ m n → [ m , n ] ∼ m - n
difference-∼ zero    zero    = pos-zero
difference-∼ zero    (suc n) = neg-zero
difference-∼ (suc m) zero    = pos-zero
difference-∼ (suc m) (suc n) = diff-suc (difference-∼ m n)

+-preserves-∼ : (_∼_ ⟨→⟩ _∼_ ⟨→⟩ _∼_) _+D_ _+S_
+-preserves-∼  pos-zero       pos-zero = pos-zero
+-preserves-∼ (pos-zero {m}) (neg-zero {n}) rewrite +-identityʳ m = difference-∼ m n
+-preserves-∼ (pos-zero {m}) (diff-suc {n} r2) rewrite +-suc m n = diff-suc (+-preserves-∼ pos-zero r2)
+-preserves-∼ (neg-zero {m}) (pos-zero {n}) rewrite +-identityʳ m = difference-∼ n m
+-preserves-∼  neg-zero       neg-zero = neg-zero
+-preserves-∼ (neg-zero {m}) (diff-suc {_}{n} r2) rewrite +-suc m n = diff-suc (+-preserves-∼ neg-zero r2)
+-preserves-∼ (diff-suc r1)   r2 = diff-suc (+-preserves-∼ r1 r2)


--------------------------------------------------
-- Definition of a universe for the instance of MSTT for parametricity.
--   There is one code for a type ℤ, representing DiffNat and SignNat
--   with the relation ~.

data RelCode : Set where
  ℤ-code : RelCode

builtin : RelExt
RelExt.RelCode builtin = RelCode
RelExt.show-code builtin ℤ-code = "ℤ"
RelExt._≟code_ builtin ℤ-code ℤ-code = return refl
RelExt.interpret-code builtin ℤ-code =
  record { Left = DiffNat ; Right = SignNat ; Relation = _∼_ }


--------------------------------------------------
-- Definition of some basic operations in MSTT.

open Applications.Parametricity.MSTT builtin

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

-- Γ ⊢ liftA2 μ A B C : ⟨ μ ∣ A ⇛ B ⇛ C ⟩ ⇛ ⟨ μ ∣ A ⟩ ⇛ ⟨ μ ∣ B ⟩ ⇛ ⟨ μ ∣ C ⟩
liftA2 : ∀ {m m'} → ModalityExpr m' m → TyExpr m' → TyExpr m' → TyExpr m' → TmExpr m
liftA2 μ A B C =
  lam[ "f" ∈ ⟨ μ ∣ A ⇛ B ⇛ C ⟩ ]
    lam[ "a" ∈ ⟨ μ ∣ A ⟩ ]
      lam[ "b" ∈ ⟨ μ ∣ B ⟩ ]
        var "f" ⊛⟨ μ ⟩ var "a" ⊛⟨ μ ⟩ var "b"


--------------------------------------------------
-- Continuing the integer example: definition of the interface
--   and proof that subtraction preserves the relation ~.

record IntStructure {m} (A : TyExpr m) : Set where
  field
    add : TmExpr m
    negate : TmExpr m
    add-well-typed : ∀ {Γ} → infer-type add Γ ≡ ok (A ⇛ A ⇛ A)
    negate-well-typed : ∀ {Γ} → infer-type negate Γ ≡ ok (A ⇛ A)

open IntStructure {{...}}

subtract : (A : TyExpr m) {{_ : IntStructure A}} → TmExpr m
subtract A = lam[ "a" ∈  A ] lam[ "b" ∈ A ] add ∙ var "a" ∙ (negate ∙ var "b")

ℤ : TyExpr ⋀
ℤ = FromRel ℤ-code

instance
  ℤ-is-int : IntStructure ℤ
  IntStructure.add ℤ-is-int = from-rel2 ℤ-code ℤ-code ℤ-code _+D_ _+S_ +-preserves-∼
  IntStructure.negate ℤ-is-int = from-rel1 ℤ-code ℤ-code negateD negateS negate-preserves-∼
  IntStructure.add-well-typed ℤ-is-int = refl
  IntStructure.negate-well-typed ℤ-is-int = refl

subtract★-left : TmExpr ★
subtract★-left = liftA2 forget-right ℤ ℤ ℤ ∙ mod-intro forget-right (subtract ℤ)

subtract★-right : TmExpr ★
subtract★-right = liftA2 forget-left ℤ ℤ ℤ ∙ mod-intro forget-left (subtract ℤ)

subtract-DiffNat : DiffNat → DiffNat → DiffNat
subtract-DiffNat = extract-term (⟦ subtract★-left ⟧tm)

subtract-SignNat : SignNat → SignNat → SignNat
subtract-SignNat = extract-term (⟦ subtract★-right ⟧tm)

subtract-∼ : (_∼_ ⟨→⟩ _∼_ ⟨→⟩ _∼_) subtract-DiffNat subtract-SignNat
subtract-∼ r1 r2 =
  let subtract-ℤ = ⟦ subtract ℤ ⟧tm
  in proj₂ ((subtract-ℤ €⟨ relation , tt ⟩ [ _ , r1 ]) $⟨ relation-id , refl ⟩ [ _ , r2 ])
