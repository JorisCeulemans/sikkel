module Experimental.Everything where

import Experimental.DependentTypes.IdentityType
import Experimental.DependentTypes.SigmaType
import Experimental.DependentTypes.LaterExperiment
import Experimental.DependentTypes.Boolean

import Experimental.UntypedNaturalitySolver.Solver
import Experimental.UntypedNaturalitySolver.Tactic.Naturality
import Experimental.UntypedNaturalitySolver.Tactic.Telescopes
import Experimental.UntypedNaturalitySolver.Tactic.ConstructExpression
import Experimental.UntypedNaturalitySolver.Tactic.Lambda
import Experimental.UntypedNaturalitySolver.Tactic.LobInduction
import Experimental.UntypedNaturalitySolver.Examples.Naturality

import Experimental.AlternativeVariablePrimitives.ContextExtension
import Experimental.AlternativeVariablePrimitives.Telescopes
import Experimental.AlternativeVariablePrimitives.Reflection.Tactic.ConstructExpression
import Experimental.AlternativeVariablePrimitives.Reflection.Tactic.Telescopes

import Experimental.NaturalityInstances.CwF-Structure.Telescopes
import Experimental.NaturalityInstances.GuardedRecursion.Modalities
import Experimental.NaturalityInstances.GuardedRecursion.Modalities.Later
import Experimental.NaturalityInstances.GuardedRecursion.Modalities.Instances
import Experimental.NaturalityInstances.GuardedRecursion.Streams.Guarded
import Experimental.NaturalityInstances.GuardedRecursion.Streams.Examples.Guarded
import Experimental.NaturalityInstances.Types.Functions

import Experimental.DeepEmbedding.Simple.TypeChecker
import Experimental.DeepEmbedding.Simple.PerformanceTest
import Experimental.DeepEmbedding.GuardedRecursion.TypeChecker
import Experimental.DeepEmbedding.GuardedRecursion.GuardedStreamsExamples
