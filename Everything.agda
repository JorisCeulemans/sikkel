module Everything where

import Model.Helpers
import Model.BaseCategory
import Model.CwF-Structure
import Model.CwF-Structure.Reflection.Substitution
import Model.CwF-Structure.Reflection.SubstitutionSequence
import Model.Type.Discrete
import Model.Type.Function
import Model.Type.Product
import Model.Type.Sum
import Model.Modality

import MSTT.TCMonad
import MSTT.Parameter.ModeTheory
import MSTT.Parameter.TypeExtension
import MSTT.Parameter.TermExtension
import MSTT.Syntax.Type
import MSTT.Syntax.Context
import MSTT.Syntax.Term
import MSTT.InterpretTypes
import MSTT.Equivalence
import MSTT.TypeChecker.ResultType
import MSTT.TypeChecker

import Extraction

import Applications.GuardedRecursion.Model.Modalities
import Applications.GuardedRecursion.Model.Streams.Guarded
import Applications.GuardedRecursion.Model.Streams.Standard
import Applications.GuardedRecursion.MSTT
-- import Applications.GuardedRecursion.StreamsExamples
-- import Applications.GuardedRecursion.ModalityInteractionTest
{-
import Applications.Parametricity.Model
import Applications.Parametricity.MSTT
import Applications.Parametricity.IntegerExample
-}
