module Applications.GuardedRecursion.StreamsExamples where

open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Vec hiding (take; head; tail)
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure renaming (◇ to ′◇)
open import Model.Type.Discrete renaming (Nat' to ′Nat'; Bool' to ′Bool')
open import Model.Type.Function hiding (lam; lam[_∈_]_) renaming (_⇛_ to _′⇛_)
open import Model.Type.Product hiding (pair; fst; snd) renaming (_⊠_ to _′⊠_)
open import Applications.GuardedRecursion.Model.Modalities
  hiding (timeless; allnow; later; next; löb; lift▻; lift2▻; 𝟙≤later) renaming (▻ to ′▻)
open import Applications.GuardedRecursion.Model.Streams.Guarded hiding (g-cons; g-head; g-tail) renaming (GStream to ′GStream)
open import Applications.GuardedRecursion.Model.Streams.Standard renaming (Stream' to ′Stream')
open import Extraction

open import Applications.GuardedRecursion.MSTT


g-consN = g-cons Nat'
g-headN = g-head Nat'
g-tailN = g-tail Nat'

-- If Γ ⊢ f : ⟨ μ ∣ A ⇛ B ⟩ and Γ ⊢ t : ⟨ μ ∣ A ⟩, then Γ ⊢ f ⊛⟨ μ ⟩ t : ⟨ μ ∣ B ⟩.
infixl 5 _⊛⟨_⟩_
_⊛⟨_⟩_ : ∀ {m m'} → TmExpr m → ModalityExpr m' m → TmExpr m → TmExpr m
f ⊛⟨ μ ⟩ t = mod-intro μ (mod-elim μ f ∙ mod-elim μ t)

-- If Γ ,lock⟨ μ ⟩ ⊢ f : A ⇛ B and Γ ⊢ t : ⟨ μ ∣ A ⟩, then Γ ⊢ f ⟨$- μ ⟩ t : ⟨ μ ∣ B ⟩.
infixl 5 _⟨$-_⟩_
_⟨$-_⟩_ : ∀ {m m'} → TmExpr m' → ModalityExpr m' m → TmExpr m → TmExpr m
f ⟨$- μ ⟩ t = mod-intro μ (f ∙ mod-elim μ t)

-- If Γ ⊢ t : T, then Γ ⊢ next t : ▻ T.
-- Note that this is different from (mod-intro later t), where t would be type-checked
--   in context Γ ,lock⟨ later ⟩.
next : TmExpr ω → TmExpr ω
next t = coe[ 𝟙≤later ∈ 𝟙 ⇒ later ] mod-intro 𝟙 t

-- If Γ ⊢ f : A ⇛ B and Γ ⊢ t : ▻ A, then Γ ⊢ f ⟨$-later⟩' t : ▻ B.
-- The difference with f ⟨$- later ⟩ t is that f is type-checked in Γ and not Γ ,lock⟨ later ⟩.
infixl 5 _⟨$-later⟩'_
_⟨$-later⟩'_ : TmExpr ω → TmExpr ω → TmExpr ω
f ⟨$-later⟩' t = next f ⊛⟨ later ⟩ t

-- Γ ⊢ lift▻ T S : (T ⇛ S) ⇛ ▻ T ⇛ ▻ S.
lift▻ : TyExpr ω → TyExpr ω → TmExpr ω
lift▻ T S = lam[ "f" ∈ T ⇛ S ] lam[ "t" ∈ ▻ T ] (var "f" ⟨$-later⟩' var "t")

-- Γ ⊢ lift2▻ T S R : (T ⇛ S ⇛ R) ⇛ ▻ T ⇛ ▻ S ⇛ ▻ R.
lift2▻ : TyExpr ω → TyExpr ω → TyExpr ω → TmExpr ω
lift2▻ T S R =
  lam[ "f" ∈ T ⇛ S ⇛ R ] lam[ "t" ∈ ▻ T ] lam[ "s" ∈ ▻ S ] (var "f" ⟨$-later⟩' var "t" ⊛⟨ later ⟩ var "s")


-- Γ ⊢ g-map A B : ⟨ timeless ∣ A ⇛ B ⟩ ⇛ GStream A ⇛ GStream B
g-map : TyExpr ★ → TyExpr ★ → TmExpr ω
g-map A B =
  lam[ "f" ∈ ⟨ timeless ∣ A ⇛ B ⟩ ]
    löb[ "m" ∈▻ (GStream A ⇛ GStream B) ]
      lam[ "s" ∈ GStream A ]
        g-cons B ∙ (var "f" ⊛⟨ timeless ⟩ g-head A ∙ var "s")
                 ∙ (var "m" ⊛⟨ later ⟩ g-tail A ∙ var "s")

g-map-sem : Tm ′◇ (timeless-ty (′Nat' ′⇛ ′Nat') ′⇛ ′GStream ′Nat' ′⇛ ′GStream ′Nat')
g-map-sem = ⟦ g-map Nat' Nat' ⟧tm-in ◇

-- Γ ⊢ g-nats : GStream Nat'
g-nats : TmExpr ω
g-nats =
  löb[ "s" ∈▻ (GStream Nat') ]
    g-consN ∙ mod-intro timeless (lit 0)
            ∙ (g-map Nat' Nat' ∙ mod-intro timeless suc ⟨$-later⟩' var "s")

g-nats-sem : Tm ′◇ (′GStream ′Nat')
g-nats-sem = ⟦ g-nats ⟧tm-in ◇

-- Γ ⊢ g-snd A : GStream A ⇛ ▻ ⟨ timeless ∣ A ⟩
g-snd : TyExpr ★ → TmExpr ω
g-snd A = lam[ "s" ∈ GStream A ] g-head A ⟨$-later⟩' g-tail A ∙ var "s"

g-snd-sem : Tm ′◇ (′GStream ′Nat' ′⇛ ′▻ (timeless-ty ′Nat'))
g-snd-sem = ⟦ g-snd Nat' ⟧tm-in ◇

-- Γ ⊢ g-thrd A : GStream A ⇛ ▻ (▻ ⟨ timeless ∣ A ⟩)
g-thrd : TyExpr ★ → TmExpr ω
g-thrd A = lam[ "s" ∈ GStream A ] g-snd A ⟨$-later⟩' g-tail A ∙ var "s"

g-thrd-sem : Tm ′◇ (′GStream ′Bool' ′⇛ ′▻ (′▻ (timeless-ty ′Bool')))
g-thrd-sem = ⟦ g-thrd Bool' ⟧tm-in ◇

-- Γ ⊢ g-zeros : GStream Nat'
g-zeros : TmExpr ω
g-zeros = löb[ "s" ∈▻ (GStream Nat') ] g-consN ∙ mod-intro timeless (lit 0) ∙ var "s"

g-zeros-sem : Tm ′◇ (′GStream ′Nat')
g-zeros-sem = ⟦ g-zeros ⟧tm-in ◇

-- Γ ⊢ g-iterate' A : ⟨ timeless | A ⇛ A ⟩ ⇛ ⟨ timeless ∣ A ⟩ ⇛ GStream A
g-iterate' : TyExpr ★ → TmExpr ω
g-iterate' A =
  lam[ "f" ∈ ⟨ timeless ∣ A ⇛ A ⟩ ]
    löb[ "g" ∈▻ (⟨ timeless ∣ A ⟩ ⇛ GStream A) ]
      lam[ "x" ∈ ⟨ timeless ∣ A ⟩ ]
        g-cons A ∙ var "x"
                 ∙ (var "g" ⊛⟨ later ⟩ (next (var "f" ⊛⟨ timeless ⟩ var "x")))

g-iterate'-sem : Tm ′◇ (timeless-ty (′Nat' ′⇛ ′Nat') ′⇛ timeless-ty ′Nat' ′⇛ ′GStream ′Nat')
g-iterate'-sem = ⟦ g-iterate' Nat' ⟧tm-in ◇

-- Γ ⊢ g-iterate A : ⟨ timeless | A ⇛ A ⟩ ⇛ ⟨ timeless ∣ A ⟩ ⇛ GStream A
g-iterate : TyExpr ★ → TmExpr ω
g-iterate A =
  lam[ "f" ∈ ▻ ⟨ timeless ∣ A ⇛ A ⟩ ]
    lam[ "a" ∈ ⟨ timeless ∣ A ⟩ ]
      löb[ "s" ∈▻ (GStream A) ]
        g-cons A ∙ var "a"
                 ∙ (g-map A A ⟨$-later⟩' var "f" ⊛⟨ later ⟩ var "s")

g-iterate-sem : Tm ′◇ (′▻ (timeless-ty (′Bool' ′⇛ ′Bool')) ′⇛ timeless-ty ′Bool' ′⇛ ′GStream ′Bool')
g-iterate-sem = ⟦ g-iterate Bool' ⟧tm-in ◇

-- Γ ⊢ g-nats' : GStream Nat'
g-nats' : TmExpr ω
g-nats' = g-iterate Nat' ∙ next (mod-intro timeless suc) ∙ mod-intro timeless (lit 0)

g-nats'-sem : Tm ′◇ (′GStream ′Nat')
g-nats'-sem = ⟦ g-nats' ⟧tm-in ◇

-- Γ ⊢ g-interleave A : GStream A ⇛ ▻ (GStream A) ⇛ GStream A
g-interleave : TyExpr ★ → TmExpr ω
g-interleave A =
  löb[ "g" ∈▻ (GStream A ⇛ ▻ (GStream A) ⇛ GStream A) ]
    lam[ "s" ∈ GStream A ]
      lam[ "t" ∈ ▻ (GStream A) ]
        g-cons A ∙ (g-head A ∙ var "s")
                 ∙ (var "g" ⊛⟨ later ⟩ var "t" ⊛⟨ later ⟩ next (g-tail A ∙ var "s"))

g-interleave-sem : Tm ′◇ (′GStream ′Nat' ′⇛ ′▻ (′GStream ′Nat') ′⇛ ′GStream ′Nat')
g-interleave-sem = ⟦ g-interleave Nat' ⟧tm-in ◇

-- Γ ⊢ g-toggle : GStream Nat'
g-toggle : TmExpr ω
g-toggle = löb[ "s" ∈▻ (GStream Nat') ]
             g-consN ∙ (mod-intro timeless (lit 1))
                     ∙ (next (g-consN ∙ mod-intro timeless (lit 0) ∙ var "s"))

g-toggle-sem : Tm ′◇ (′GStream ′Nat')
g-toggle-sem = ⟦ g-toggle ⟧tm-in ◇

-- Γ ⊢ g-paperfolds : GStream Nat'
g-paperfolds : TmExpr ω
g-paperfolds = löb[ "s" ∈▻ (GStream Nat') ] g-interleave Nat' ∙ g-toggle ∙ var "s"

g-paperfolds-sem : Tm ′◇ (′GStream ′Nat')
g-paperfolds-sem = ⟦ g-paperfolds ⟧tm-in ◇

-- Γ ⊢ g-initial : ((⟨ timeless ∣ A ⟩ ⊠ (▻ T)) ⇛ T) ⇛ GStream A ⇛ T
g-initial : TyExpr ★ → TyExpr ω → TmExpr ω
g-initial A T =
  löb[ "g" ∈▻ (((⟨ timeless ∣ A ⟩ ⊠ (▻ T)) ⇛ T) ⇛ GStream A ⇛ T) ]
    lam[ "f" ∈ (⟨ timeless ∣ A ⟩ ⊠ (▻ T)) ⇛ T ]
      lam[ "s" ∈ GStream A ]
        var "f" ∙ (pair (g-head A ∙ (var "s"))
                        (var "g" ⊛⟨ later ⟩ next (var "f") ⊛⟨ later ⟩ g-tail A ∙ var "s"))

g-initial-sem : Tm ′◇ (((timeless-ty ′Nat' ′⊠ ′▻ ′Bool') ′⇛ ′Bool') ′⇛ ′GStream ′Nat' ′⇛ ′Bool')
g-initial-sem = ⟦ g-initial Nat' Bool' ⟧tm-in ◇

-- Γ ⊢ g-final : (T ⇛ (⟨ timeless ∣ A ⟩ ⊠ (▻ T))) ⇛ T ⇛ GStream A
g-final : TyExpr ★ → TyExpr ω → TmExpr ω
g-final A T =
  löb[ "g" ∈▻ ((T ⇛ (⟨ timeless ∣ A ⟩ ⊠ (▻ T))) ⇛ T ⇛ GStream A) ]
    lam[ "f" ∈ T ⇛ (⟨ timeless ∣ A ⟩ ⊠ (▻ T)) ]
      lam[ "x" ∈ T ]
        g-cons A ∙ (fst (var "f" ∙ var "x"))
                 ∙ (var "g" ⊛⟨ later ⟩ next (var "f") ⊛⟨ later ⟩ snd (var "f" ∙ var "x"))

g-final-sem : Tm ′◇ ((′Bool' ′⇛ (timeless-ty ′Nat' ′⊠ ′▻ ′Bool')) ′⇛ ′Bool' ′⇛ ′GStream ′Nat')
g-final-sem = ⟦ g-final Nat' Bool' ⟧tm-in ◇

g-consB = g-cons Bool'
g-headB = g-head Bool'
g-tailB = g-tail Bool'

-- Γ ⊢ g-thumorse : GStream Bool'
g-thumorse : TmExpr ω
g-thumorse =
  let liftSB▻ = lift▻ (GStream Bool') (GStream Bool')
      liftLSB▻ = lift▻ (▻ (GStream Bool')) (▻ (GStream Bool'))
  in
  löb[ "t-m" ∈▻ (GStream Bool') ]
    g-consB ∙ mod-intro timeless false
            ∙ (g-consB ∙ (mod-intro timeless true)
                       ⟨$-later⟩' (liftLSB▻ ∙ (liftSB▻ ∙ h)) ∙
                            (g-tailB ⟨$-later⟩' liftSB▻ ∙ h ∙ var "t-m"))
  where
    h : TmExpr ω
    h =
      löb[ "g" ∈▻ (GStream Bool' ⇛ GStream Bool') ]
        lam[ "s" ∈ GStream Bool' ]
          timeless-if (g-headB ∙ var "s")
                      (g-consB ∙ mod-intro timeless true
                               ∙ (next (g-consB ∙ mod-intro timeless false ∙ (var "g" ⊛⟨ later ⟩ g-tailB ∙ var "s"))))
                      (g-consB ∙ mod-intro timeless false
                               ∙ (next (g-consB ∙ mod-intro timeless true  ∙ (var "g" ⊛⟨ later ⟩ g-tailB ∙ var "s"))))

g-thumorse-sem : Tm ′◇ (′GStream ′Bool')
g-thumorse-sem = ⟦ g-thumorse ⟧tm-in ◇

-- Γ ⊢ g-fibonacci-word : GStream Bool'
g-fibonacci-word : TmExpr ω
g-fibonacci-word =
  let liftSB▻ = lift▻ (GStream Bool') (GStream Bool')
      liftLSB▻ = lift▻ (▻ (GStream Bool')) (▻ (GStream Bool'))
  in
  löb[ "fw" ∈▻ (GStream Bool') ]
    g-consB ∙ mod-intro timeless false
            ∙ (g-consB ∙ mod-intro timeless true
                       ⟨$-later⟩' (liftLSB▻ ∙ (liftSB▻ ∙ f)) ∙
                            (g-tailB ⟨$-later⟩' liftSB▻ ∙ f ∙ var "fw"))
  where
    f : TmExpr ω
    f =
      löb[ "g" ∈▻ (GStream Bool' ⇛ GStream Bool') ]
        lam[ "s" ∈ GStream Bool' ]
          timeless-if (g-headB ∙ var "s")
                      (g-consB ∙ mod-intro timeless false ∙ (var "g" ⊛⟨ later ⟩ g-tailB ∙ var "s"))
                      (g-consB ∙ mod-intro timeless false ∙ next (
                          g-consB ∙ mod-intro timeless true ∙ (var "g" ⊛⟨ later ⟩ g-tailB ∙ var "s")))

g-fibonacci-word-sem : Tm ′◇ (′GStream ′Bool')
g-fibonacci-word-sem = ⟦ g-fibonacci-word ⟧tm-in ◇

-- Γ ⊢ g-mergef A B C : (⟨ timeless ∣ A ⟩ ⇛ ⟨ timeless ∣ B ⟩ ⇛ ▻ (GStream C) ⇛ GStream C) ⇛ GStream A ⇛ GStream B ⇛ GStream C
g-mergef : (A B C : TyExpr ★) → TmExpr ω
g-mergef A B C =
  lam[ "f" ∈ ⟨ timeless ∣ A ⟩ ⇛ ⟨ timeless ∣ B ⟩ ⇛ ▻ (GStream C) ⇛ GStream C ]
    löb[ "g" ∈▻ (GStream A ⇛ GStream B ⇛ GStream C) ]
      lam[ "xs" ∈ GStream A ]
        lam[ "ys" ∈ GStream B ]
          var "f" ∙ (g-head A ∙ var "xs")
                  ∙ (g-head B ∙ var "ys")
                  ∙ (var "g" ⊛⟨ later ⟩ g-tail A ∙ var "xs" ⊛⟨ later ⟩ g-tail B ∙ var "ys")

g-mergef-sem : Tm ′◇ ((timeless-ty ′Nat' ′⇛ timeless-ty ′Bool' ′⇛ ′▻ (′GStream ′Nat') ′⇛ ′GStream ′Nat') ′⇛ ′GStream ′Nat' ′⇛ ′GStream ′Bool' ′⇛ ′GStream ′Nat')
g-mergef-sem = ⟦ g-mergef Nat' Bool' Nat' ⟧tm-in ◇

-- Γ ⊢ g-zipWith A B C : ⟨ timeless ∣ A ⇛ B ⇛ C ⟩ ⇛ GStream A ⇛ GStream B ⇛ GStream C
g-zipWith : (A B C : TyExpr ★) → TmExpr ω
g-zipWith A B C =
  lam[ "f" ∈ ⟨ timeless ∣ A ⇛ B ⇛ C ⟩ ]
    löb[ "g" ∈▻ (GStream A ⇛ GStream B ⇛ GStream C) ]
      lam[ "as" ∈ GStream A ]
        lam[ "bs" ∈ GStream B ]
          g-cons C ∙ (var "f" ⊛⟨ timeless ⟩ g-head A ∙ var "as" ⊛⟨ timeless ⟩ g-head B ∙ var "bs")
                   ∙ (var "g" ⊛⟨ later ⟩ g-tail A ∙ var "as" ⊛⟨ later ⟩ g-tail B ∙ var "bs")

g-zipWith-sem : Tm ′◇ (timeless-ty (′Bool' ′⇛ ′Nat' ′⇛ ′Bool') ′⇛ ′GStream ′Bool' ′⇛ ′GStream ′Nat' ′⇛ ′GStream ′Bool')
g-zipWith-sem = ⟦ g-zipWith Bool' Nat' Bool' ⟧tm-in ◇

-- Γ ⊢ g-fibs : GStream Nat'
g-fibs : TmExpr ω
g-fibs =
  let lift2SN▻ = lift2▻ (GStream Nat') (GStream Nat') (GStream Nat')
  in
  löb[ "s" ∈▻ (GStream Nat') ]
    g-consN ∙ mod-intro timeless (lit 1)
            ∙ (g-consN ∙ mod-intro timeless (lit 1)
                       ⟨$-later⟩' (lift2SN▻ ∙ (g-zipWith Nat' Nat' Nat' ∙ mod-intro timeless plus)
                                            ∙ var "s"
                                            ⟨$-later⟩' (g-tailN ⟨$-later⟩' var "s")))

g-fibs-sem : Tm ′◇ (′GStream ′Nat')
g-fibs-sem = ⟦ g-fibs ⟧tm-in ◇

-- Γ ⊢ g-flipFst A : GStream A ⇛ ▻ (GStream A)
g-flipFst : TyExpr ★ → TmExpr ω
g-flipFst A =
  lam[ "s" ∈ GStream A ]
    g-cons A ⟨$-later⟩' g-snd A ∙ var "s" ⊛⟨ later ⟩ next (
    g-cons A ⟨$-later⟩' next (g-head A ∙ var "s") ⊛⟨ later ⟩ (g-tail A ⟨$-later⟩' g-tail A ∙ var "s"))

g-flipFst-sem : Tm ′◇ (′GStream ′Bool' ′⇛ ′▻ (′GStream ′Bool'))
g-flipFst-sem = ⟦ g-flipFst Bool' ⟧tm-in ◇



Stream' : TyExpr ★ → TyExpr ★
Stream' A = ⟨ allnow ∣ GStream A ⟩

-- Γ ⊢ nats : Stream' Nat'
nats : TmExpr ★
nats = mod-intro allnow g-nats

nats-sem : Tm ′◇ (′Stream' ′Nat')
nats-sem = ⟦ nats ⟧tm-in ◇

nats-agda : Stream ℕ
nats-agda = extract-term nats-sem

nats-test : take 10 nats-agda ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
nats-test = refl

-- Γ ⊢ paperfolds : Stream' Nat'
paperfolds : TmExpr ★
paperfolds = mod-intro allnow g-paperfolds

paperfolds-sem : Tm ′◇ (′Stream' ′Nat')
paperfolds-sem = ⟦ paperfolds ⟧tm-in ◇

paperfolds-agda : Stream ℕ
paperfolds-agda = extract-term paperfolds-sem

paperfolds-test : take 10 paperfolds-agda ≡ 1 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ []
paperfolds-test = refl

-- Γ ⊢ thue-morse : Stream' Bool'
thue-morse : TmExpr ★
thue-morse = mod-intro allnow g-thumorse

thue-morse-sem : Tm ′◇ (′Stream' ′Bool')
thue-morse-sem = ⟦ thue-morse ⟧tm-in ◇

thue-morse-agda : Stream Bool
thue-morse-agda = extract-term thue-morse-sem

thue-morse-test : take 10 thue-morse-agda ≡ false ∷ true ∷ true ∷ false ∷ true ∷ false ∷ false ∷ true ∷ true ∷ false ∷ []
thue-morse-test = refl

-- Γ ⊢ fibonacci-word : Stream' Bool'
fibonacci-word : TmExpr ★
fibonacci-word = mod-intro allnow g-fibonacci-word

fibonacci-word-sem : Tm ′◇ (′Stream' ′Bool')
fibonacci-word-sem = ⟦ fibonacci-word ⟧tm-in ◇

fibonacci-word-agda : Stream Bool
fibonacci-word-agda = extract-term fibonacci-word-sem

fibonacci-word-test : take 10 fibonacci-word-agda ≡ false ∷ true ∷ false ∷ false ∷ true ∷ false ∷ true ∷ false ∷ false ∷ true ∷ []
fibonacci-word-test = refl

-- Γ ⊢ fibs : Stream' Nat'
fibs : TmExpr ★
fibs = mod-intro allnow g-fibs

fibs-sem : Tm ′◇ (′Stream' ′Nat')
fibs-sem = ⟦ fibs ⟧tm-in ◇

fibs-agda : Stream ℕ
fibs-agda = extract-term fibs-sem

fibs-test : take 10 fibs-agda ≡ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ 55 ∷ []
fibs-test = refl


-- Γ ⊢ head' A : Stream' A ⇛ A
head' : TyExpr ★ → TmExpr ★
head' A = ann
  lam[ "s" ∈ Stream' A ] g-head A ⟨$- allnow ⟩ var "s"
  ∈ (Stream' A ⇛ A)

head-nats : TmExpr ★
head-nats = head' Nat' ∙ nats

head-nats-agda : ℕ
head-nats-agda = extract-term (⟦ head-nats ⟧tm-in ◇)

head-nats-test : head-nats-agda ≡ 0
head-nats-test = refl

-- Γ ⊢ tail' A : Stream' A ⇛ Stream' A
tail' : TyExpr ★ → TmExpr ★
tail' A = ann
  lam[ "s" ∈ Stream' A ] g-tail A ⟨$- allnow ⟩ var "s"
  ∈ (Stream' A ⇛ Stream' A)

tailN-sem : Tm ′◇ (′Stream' ′Nat' ′⇛ ′Stream' ′Nat')
tailN-sem = ⟦ tail' Nat' ⟧tm-in ◇

-- Γ ⊢ cons' A : A ⇛ Stream' A ⇛ Stream' A
cons' : TyExpr ★ → TmExpr ★
cons' A = ann
  lam[ "a" ∈ A ] lam[ "as" ∈ Stream' A ]
    g-cons A ⟨$- allnow ⟩ (ann (var "a") ∈ ⟨ allnow ∣ ⟨ timeless ∣ A ⟩ ⟩)
             ⊛⟨ allnow ⟩ (ann (var "as") ∈ ⟨ allnow ∣ ⟨ later ∣ GStream A ⟩ ⟩)
  ∈ (A ⇛ Stream' A ⇛ Stream' A)

consB-sem : Tm ′◇ (′Bool' ′⇛ ′Stream' ′Bool' ′⇛ ′Stream' ′Bool')
consB-sem = ⟦ cons' Bool' ⟧tm-in ◇

-- Γ ⊢ map' A B : (A ⇛ B) ⇛ Stream' A ⇛ Stream' B
map' : TyExpr ★ → TyExpr ★ → TmExpr ★
map' A B =
  lam[ "f" ∈ A ⇛ B ]
    lam[ "s" ∈ Stream' A ]
      g-map A B ⟨$- allnow ⟩ ann (var "f") ∈ ⟨ allnow ∣ ⟨ timeless ∣ A ⇛ B ⟩ ⟩
                ⊛⟨ allnow ⟩ var "s"

map'-sem : Tm ′◇ ((′Nat' ′⇛ ′Nat') ′⇛ ′Stream' ′Nat' ′⇛ ′Stream' ′Nat')
map'-sem = ⟦ map' Nat' Nat' ⟧tm-in ◇

-- Γ ⊢ g-every2nd A : ⟨ timeless ∣ Stream' A ⟩ ⇛ GStream A
g-every2nd : TyExpr ★ → TmExpr ω
g-every2nd A =
  löb[ "g" ∈▻ (⟨ timeless ∣ Stream' A ⟩ ⇛ GStream A) ]
    lam[ "s" ∈ ⟨ timeless ∣ Stream' A ⟩ ]
      g-cons A ∙ (head' A ⟨$- timeless ⟩ var "s")
               ∙ (var "g" ⊛⟨ later ⟩ next (tail' A ⟨$- timeless ⟩ (tail' A ⟨$- timeless ⟩ var "s")))

g-every2ndB-sem : Tm ′◇ (timeless-ty (′Stream' ′Bool') ′⇛ ′GStream ′Bool')
g-every2ndB-sem = ⟦ g-every2nd Bool' ⟧tm-in ◇

-- Γ ⊢ every2nd A : Stream' A ⇛ Stream' A
every2nd : TyExpr ★ → TmExpr ★
every2nd A =
  lam[ "s" ∈ Stream' A ]
    g-every2nd A ⟨$- allnow ⟩ ann (var "s") ∈ ⟨ allnow ∣ ⟨ timeless ∣ Stream' A ⟩ ⟩

every2ndN-sem : Tm ′◇ (′Stream' ′Nat' ′⇛ ′Stream' ′Nat')
every2ndN-sem = ⟦ every2nd Nat' ⟧tm-in ◇

every2nd-test : take 6 (extract-term (every2ndN-sem $ nats-sem))
                ≡ 0 ∷ 2 ∷ 4 ∷ 6 ∷ 8 ∷ 10 ∷ []
every2nd-test = refl

-- Γ ⊢ g-diag : ⟨ timeless ∣ Stream' (Stream' A) ⟩ ⇛ GStream A
g-diag : TyExpr ★ → TmExpr ω
g-diag A =
  löb[ "g" ∈▻ (⟨ timeless ∣ Stream' (Stream' A) ⟩ ⇛ GStream A) ]
    lam[ "xss" ∈ ⟨ timeless ∣ Stream' (Stream' A) ⟩ ]
      g-cons A ∙ (head' A ⟨$- timeless ⟩ (head' (Stream' A) ⟨$- timeless ⟩ var "xss"))
               ∙ (var "g" ⊛⟨ later ⟩ next (map' (Stream' A) (Stream' A) ∙ tail' A
                                                ⟨$- timeless ⟩ (tail' (Stream' A) ⟨$- timeless ⟩ var "xss")))

g-diagB⟧ : Tm ′◇ (timeless-ty (′Stream' (′Stream' ′Bool')) ′⇛ ′GStream ′Bool')
g-diagB⟧ = ⟦ g-diag Bool' ⟧tm-in ◇

-- Γ ⊢ diag : Stream' (Stream' A) ⇛ Stream' A
diag : TyExpr ★ → TmExpr ★
diag A =
  lam[ "s" ∈ Stream' (Stream' A) ]
    g-diag A ⟨$- allnow ⟩ ann (var "s") ∈ ⟨ allnow ∣ ⟨ timeless ∣ Stream' (Stream' A) ⟩ ⟩

diagB-sem : Tm ′◇ (′Stream' (′Stream' ′Bool') ′⇛ ′Stream' ′Bool')
diagB-sem = ⟦ diag Bool' ⟧tm-in ◇
