--------------------------------------------------
-- An instance of MSTT can be extended with custom term constructors, and this
--   file provides the interface to do so. MSTT is parametrized by a record of
--   type TmExt, which specifies a universe of codes for the new term constructors
--   and their interpretation in a presheaf model.
--   Every code in the universe comes with information about its type
--   and the context and type for each of its arguments. The context
--   of an argument is obtained by adding a telescope to the context
--   of the current term.
--------------------------------------------------

open import Experimental.LogicalFramework.MSTT.Parameter.ModeTheory
open import Experimental.LogicalFramework.MSTT.Parameter.TypeExtension

module Experimental.LogicalFramework.MSTT.Parameter.TermExtension
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (Name : Set)
  where

open import Data.List
open import Relation.Binary.PropositionalEquality

open import Experimental.LogicalFramework.Proof.CheckingMonad
open import Experimental.LogicalFramework.MSTT.Syntax.Types ℳ 𝒯
open import Experimental.LogicalFramework.MSTT.Syntax.Contexts ℳ 𝒯 Name

open ModeTheory ℳ

private variable
  m : Mode


-- A value of type TmArgInfo m contains the information about an
-- argument to a term constructor in mode m, i.e. the mode of the
-- argument, how the context should be modified, and the type of the
-- argument.
record TmArgInfo (m : Mode) : Set where
  constructor tmarginfo
  field
    {n} : Mode
    tmarg-tel : Telescope m n
    tmarg-ty : Ty n
open TmArgInfo public hiding (n)


record TmExt : Set₁ where
  field
    TmExtCode : (m : Mode) → Set
      -- ^ The universe of codes, every code corresponds to a new term former.
    _≟tm-code_ : (c1 c2 : TmExtCode m) → PCM (c1 ≡ c2)
      -- ^ We should be able to test codes for equality.
    tm-code-ty : TmExtCode m → Ty m
      -- ^ Specification of the type of every new term former.
    tm-code-arginfos : TmExtCode m → List (TmArgInfo m)
      -- ^ Every new term former can take a number of terms as
      --   arguments, their types and context modifications are
      --   collected here.
