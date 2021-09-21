--------------------------------------------------
-- The Type Checking Monad
--------------------------------------------------

module Applications.Parametricity.MSTT.TCMonad where

open import Data.String
open import Level

private
  variable
    ℓ : Level
    A B : Set ℓ

infixl 4 _<$>_ _⊛_
infixl 1 _>>=_


-- The type checking monad currently only allows for simple strings as error messages.
data TCM (A : Set ℓ) : Set ℓ where
  type-error : String → TCM A
  ok : A → TCM A

_<$>_ : (A → B) → TCM A → TCM B
f <$> type-error msg = type-error msg
f <$> ok a           = ok (f a)

_⊛_ : TCM (A → B) → TCM A → TCM B
type-error msg ⊛ x = type-error msg
ok f           ⊛ x = f <$> x

return : A → TCM A
return = ok

_>>=_ : TCM A → (A → TCM B) → TCM B
type-error msg >>= f = type-error msg
ok a           >>= f = f a

_>>_ : TCM A → TCM B → TCM B
x >> y = x >>= (λ _ → y)

_<∣>_ : TCM A → TCM A → TCM A
type-error msg <∣> y = y
ok a           <∣> y = ok a

tcm-elim : (String → B) → (A → B) → TCM A → B
tcm-elim f g (type-error msg) = f msg
tcm-elim f g (ok a) = g a

modify-error-msg : (String → String) → TCM A → TCM A
modify-error-msg f (type-error msg) = type-error (f msg)
modify-error-msg f (ok a) = ok a

with-error-msg : String → TCM A → TCM A
with-error-msg msg = modify-error-msg (λ _ → msg)
