module Experimental.LogicalFramework.Proof.CheckingMonad where

open import Data.List
open import Data.Product hiding (_<*>_)
open import Data.String hiding (_++_)
open import Level
open import Relation.Nullary as Ag using (Dec; yes; no)

private variable
  ℓ : Level
  A B : Set ℓ


ErrorMsg : Set
ErrorMsg = String

-- The proof checking monad PCM is essentially the error monad.
data PCM (A : Set ℓ) : Set ℓ where
  ok : A → PCM A
  error : ErrorMsg → PCM A

throw-error : ErrorMsg → PCM A
throw-error msg = error msg

infixl 4 _<$>_ _<*>_
infixl 1 _>>=_ _>>_

-- Functor, Applicative and Monad instances of PCM (since this is the
-- only monad we work with, we do not make use of instance arguments).
_<$>_ : (A → B) → PCM A → PCM B
f <$> (ok a)      = ok (f a)
f <$> (error msg) = error msg

_<*>_ : PCM (A → B) → PCM A → PCM B
ok f      <*> ok a      = ok (f a)
ok f      <*> error msg = error msg
error msg <*> _         = error msg

return : A → PCM A
return a = ok a

_>>=_ : PCM A → (A → PCM B) → PCM B
ok a      >>= f = f a
error msg >>= f = error msg

_>>_ : PCM A → PCM B → PCM B
ok _      >> mb = mb
error msg >> _  = error msg

from-dec : ErrorMsg → Dec A → PCM A
from-dec msg (yes a) = return a
from-dec msg (no ¬a) = throw-error msg
