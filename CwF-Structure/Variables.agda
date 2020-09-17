{-# OPTIONS --omega-in-omega #-}

--------------------------------------------------
-- Constructs for working with variables
--
-- The main definition in this module is the macro "var" which lets
-- a user refer to a variable by its de Bruijn index as a natural number,
-- rather than manually weakening the term ξ an appropriate number of times.
-- Note that we use the option omega-in-omega in order to define
-- an inductive data type in Setω and to pattern match on it (which
-- is not possible in Agda 2.6.1 without this option). This code should
-- typecheck without this option in Agda 2.6.2 once released.
--------------------------------------------------

open import Categories

module CwF-Structure.Variables where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc; #_)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _<?_)
open import Data.Product using (_×_; _,_)
open import Data.Unit
open import Data.Vec using (Vec; []; _∷_; foldr; lookup)
open import Level renaming (suc to lsuc)
open import Reflection hiding (var; lam)
open import Reflection.Argument using (_⟨∷⟩_; _⟅∷⟆_)
open import Reflection.TypeChecking.MonadSyntax using (_<$>_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import CwF-Structure.Contexts
open import CwF-Structure.Types
open import CwF-Structure.Terms
open import CwF-Structure.ContextExtension


--------------------------------------------------
-- Internal representation of an extended context

module _ {C : Category} where

  private
    variable
      ℓ ℓ' ℓc : Level
      Γ : Ctx C ℓ
      n : ℕ
      ℓs : Vec Level n

  level-fold : ∀ {n} → Vec Level n → Level
  level-fold = foldr _ _⊔_ 0ℓ

  -- A value of TypeSequence Γ n ℓs is a list of types Ts = [] ∷ T1 ∷ T2 ∷ ... ∷ Tn so that
  -- T1 is valid in Γ, T2 is valid in Γ ,, T1 etc. and hence Γ ,, T1 ,, T2 ,, ... ,, Tn
  -- is a valid context written as Γ ,,, Ts.
  data TypeSequence (Γ : Ctx C ℓc) : (n : ℕ) → Vec Level n → Setω
  _,,,_ : (Γ : Ctx C ℓc) {n : ℕ} {ℓs : Vec Level n} → TypeSequence Γ n ℓs → Ctx C (ℓc ⊔ level-fold ℓs)

  data TypeSequence Γ where
    []  : TypeSequence Γ 0 []
    _∷_ : ∀ {ℓt n ℓs} (Ts : TypeSequence Γ n ℓs) → Ty (Γ ,,, Ts) ℓt → TypeSequence Γ (suc n) (ℓt ∷ ℓs)

  Γ ,,, []       = Γ
  Γ ,,, (Ts ∷ T) = (Γ ,,, Ts) ,, T

  var-type : (Ts : TypeSequence Γ n ℓs) (x : Fin n) → Ty (Γ ,,, Ts) (lookup ℓs x)
  var-type (Ts ∷ T) zero    = T [ π ]
  var-type (Ts ∷ T) (suc x) = (var-type Ts x) [ π ]

  prim-var : (Ts : TypeSequence Γ n ℓs) (x : Fin n) → Tm (Γ ,,, Ts) (var-type Ts x)
  prim-var (Ts ∷ T) zero    = ξ
  prim-var (Ts ∷ T) (suc x) = (prim-var Ts x) [ π ]'


--------------------------------------------------
-- Definition of a macro that automatically transforms the current
-- context into a type sequence and then applies prim-var

-- If get-ctx is applied to an Agda type of the form Tm Γ T, then
-- the context Γ is returned.
get-ctx : Type → Maybe Term
get-ctx (def (quote Tm) args) = go args
  where
    go : List (Arg Term) → Maybe Term
    go [] = nothing
    go (ctx ⟨∷⟩ xs) = just ctx
    go (_ ∷ xs) = go xs
get-ctx _ = nothing

-- ctx-to-tyseq takes a value of type Ctx C ℓ and transforms it into a type
-- sequence. If a context is of the form Γ ,, T then T is added to the type
-- sequence and ctx-to-tyseq is called recursively on Γ. Otherwise the process
-- stops and ctx-to-tyseq returns an empty sequence.
ctx-to-tyseq : Term → TC Term
ctx-to-tyseq (def (quote _,,_) xs) = go xs
  where
    go : List (Arg Term) → TC Term
    go [] = typeError (strErr "Invalid use of context extension." ∷ [])
    go (ctx ⟨∷⟩ ty ⟨∷⟩ xs) = (λ tyseq → con (quote TypeSequence._∷_) (vArg tyseq ∷ vArg ty ∷ [])) <$>
                             (ctx-to-tyseq ctx)
    go (_ ∷ xs) = go xs
ctx-to-tyseq (meta m args) = debugPrint "vtac" 5 (strErr "Blocking on meta" ∷ termErr (meta m args) ∷ strErr "in ctx-to-tyseq." ∷ []) >> blockOnMeta m
ctx-to-tyseq ctx = return (con (quote TypeSequence.[]) [])

-- Check whether the provided de Bruijn index is within bounds.
check-within-bounds : Term → Term → TC ⊤
check-within-bounds t-x t-tyseq = do
  x ← unquoteTC t-x
  def (quote TypeSequence) args ← inferType t-tyseq
    where _ → typeError (strErr "An error occurred, this point should not be reached." ∷ [])
  t-n ← get-tyseq-length args
  n ← unquoteTC t-n
  go ⌊ x <? n ⌋ t-n
  where
    get-tyseq-length : List (Arg Term) → TC Term
    get-tyseq-length [] = typeError (strErr "An error occurred, this point should not be reached." ∷ [])
    get-tyseq-length (_ ⟨∷⟩ t-n ⟨∷⟩ _) = return t-n
    get-tyseq-length (_ ∷ args)       = get-tyseq-length args

    go : Bool → Term → TC ⊤
    go false t-n = typeError (strErr "The provided de Bruijn index" ∷ termErr t-x ∷
                              strErr " is too high. Number of available variables:" ∷ termErr t-n ∷ [])
    go true  t-n = return tt

var-macro : Term → Term → TC ⊤
var-macro x hole = do
  goal ← inferType hole
  debugPrint "vtac" 5 (strErr "var macro called, goal:" ∷ termErr goal ∷ [])
  just ctx ← return (get-ctx goal)
    where nothing → typeError (strErr "The var macro can only be used to produce a term." ∷ termErr goal ∷ [])
  tyseq ← ctx-to-tyseq ctx
  check-within-bounds x tyseq
  let solution = def (quote prim-var) (vArg tyseq ∷ vArg (def (quote #_) (vArg x ∷ [])) ∷ [])
  debugPrint "vtac" 5 (strErr "var macro successfully constructed solution:" ∷ termErr solution ∷ [])
  unify hole solution

macro
  var : Term → Term → TC ⊤
  var = var-macro


--------------------------------------------------
-- Some tests

private
  module _ {C : Category} where
    open import Types.Discrete
    open import Types.Functions

    test : Tm {C = C} (◇ ,, Bool') (Bool' [ π ])
    test = var 0

    test2 : Tm {C = C} (◇ ,, Bool' ,, (Nat' ⇛ Nat')) ((Nat' ⇛ Nat') [ π ])
    test2 = var 0

    test3 : Tm {C = C} (◇ ,, Bool' ,, Nat') ((Bool' [ π ]) [ π ])
    test3 = var 1

    id : ∀ {ℓ ℓ'} {Γ : Ctx C ℓ} {T : Ty Γ ℓ'} → Tm Γ (T ⇛ T)
    id {Γ = Γ}{T = T} = lam T (var 0)
