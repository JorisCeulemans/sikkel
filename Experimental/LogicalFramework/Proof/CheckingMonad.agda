module Experimental.LogicalFramework.Proof.CheckingMonad where

open import Data.List
open import Data.Product hiding (_<*>_)
open import Data.String hiding (_++_)
open import Level
open import Relation.Nullary as Ag using (Dec; yes; no)

open import Experimental.LogicalFramework.MSTT.ModeTheory
open import Experimental.LogicalFramework.Formula
open import Experimental.LogicalFramework.Proof.Definition

private variable
  ℓ : Level
  A B : Set ℓ


record Goal : Set where
  constructor goal
  field
    identifier  : String
    {goal-mode} : Mode
    goal-ctx    : ProofCtx goal-mode
    goal-prop   : Formula (to-ctx goal-ctx)

-- The proof checking monad PCM essentially consists of the error
-- monad transformer (responsible for handling errors while proof
-- checking) applied to the writer monad (responsible for logging the
-- goals in a proof that need to be filled in).
data PCError (A : Set ℓ) : Set ℓ where
  ok : A → PCError A
  error : String → PCError A

record PCM (A : Set ℓ) : Set ℓ where
  constructor pcm
  field
    pc-comp : PCError A
    goals : List Goal


-- Some operations useful while proof checking.
censor : (List Goal → List Goal) → PCM A → PCM A
censor f (pcm x goals) = pcm x (f goals)

cons-goal : Goal → PCM A → PCM A
cons-goal g = censor (g ∷_)
ErrorMsg : Set
ErrorMsg = String

throw-error : String → PCM A
throw-error msg = pcm (error msg) []

goal-fail : Goal → PCM A
goal-fail g = pcm (error "The proof contains unsolved goals.") (g ∷ [])


infixl 4 _<$>_ _<*>_ _<|*|>_ _<|,|>_
infixl 1 _>>=_ _>>_

-- Functor, Applicative and Monad instances of PCM (since this is the
-- only monad we work with, we do not make use of instance arguments).
_<$>_ : (A → B) → PCM A → PCM B
f <$> (pcm (ok a)      goals) = pcm (ok (f a)) goals
f <$> (pcm (error msg) goals) = pcm (error msg) goals

_<*>_ : PCM (A → B) → PCM A → PCM B
pcm (ok f)      gf <*> pcm (ok a) ga      = pcm (ok (f a)) (gf ++ ga)
pcm (ok f)      gf <*> pcm (error msg) ga = pcm (error msg) (gf ++ ga)
pcm (error msg) gf <*> _                  = pcm (error msg) gf

return : A → PCM A
return a = pcm (ok a) []

_>>=_ : PCM A → (A → PCM B) → PCM B
pcm (ok a)      goals >>= f = censor (goals ++_) (f a)
pcm (error msg) goals >>= f = pcm (error msg) goals

_>>_ : PCM A → PCM B → PCM B
pcm (ok _)      goals >> mb = censor (goals ++_) mb
pcm (error msg) goals >> _  = pcm (error msg) goals


-- When checking recursively checking two or more subproofs of a
-- proof, we want to continue checking the other subproofs if one of
-- them failed (in order to still print out the goals for all the
-- holes). This is achieved by equipping PCM with a different
-- applicative structure than the one above. It is in fact the
-- structure obtained by composing the Error and Writer applicative
-- functors.
fst-err-applicative : PCError (A → B) → PCError A → PCError B
fst-err-applicative (error msg) _           = error msg
fst-err-applicative (ok _)      (error msg) = error msg
fst-err-applicative (ok f)      (ok a)      = ok (f a)

_<|*|>_ : PCM (A → B) → PCM A → PCM B
pcm mf gf <|*|> pcm ma ga = pcm (fst-err-applicative mf ma) (gf ++ ga)

_<|,|>_ : PCM A → PCM B → PCM (A × B)
ma <|,|> mb = _,_ <$> ma <|*|> mb
from-dec : ErrorMsg → Dec A → PCM A
from-dec msg (yes a) = return a
from-dec msg (no ¬a) = throw-error msg


