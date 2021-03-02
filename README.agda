--------------------------------------------------
-- README
--------------------------------------------------

module README where

{-
  This is the readme for the Sikkel library, as presented in the ICFP submission
  Sikkel: Multimode Simple Type Theory as an Agda Library.

  We use Agda 2.6.1 and the Agda standard library (version 1.5).
  We will first give an overview of the paper with references to the relevant code.
  Subsequently we discuss code that does not appear in the paper.
-}


--------------------------------------------------
-- SECTION 1: Introduction

{-
  The code for the introductory example about the stream of all natural numbers
  can be found in the following two files.
-}

open import GuardedRecursion.Streams.Examples.Guarded
open import GuardedRecursion.Streams.Examples.Standard


--------------------------------------------------
-- SECTION 2: Programming in Sikkel

{-
  All concepts that come from the CwF structure of a Sikkel type theory (contexts,
  types, terms, substitutions, variables, equality of types, ...) are made available
  by importing the file CwF-Structure.
-}

open import CwF-Structure

{-
  Sikkel's simple built-in types and type constructors can be imported from
  several files in the directory Types.
-}

open import Types.Functions
open import Types.Products
open import Types.Sums
open import Types.Discrete

{-
  The by-naturality tactic and derived operations lamι and varι are contained
  in the following files.
  Note that one should import Types.Instances in order for the naturality solver
  to work with Sikkel's built-in types and type constructors.
-}

open import Reflection.Tactic.Naturality -- for by-naturality
open import Reflection.Tactic.Lambda     -- for lamι
open import Reflection.Tactic.Telescopes -- for varι (but this is already reexported by CwF-Structure)

open import Types.Instances

{-
  The definition of the later modality can be found in the following file.
-}

open import GuardedRecursion.Modalities.Later

{-
  The general definition of a modality and its (applicative) functor operations
  are exported by the following module.
  Note that we also prove some extra results, e.g. that all modalities preserve
  product types and the unit type.
-}

open import Modalities

{-
  The type class underlying Sikkel's extraction mechanism for embedded terms to
  Agda terms is defined in the following file.
  It also defines instances for Sikkel's built-in types and type constructors.
-}

open import Translation


--------------------------------------------------
-- SECTION 3: Applications

{-
  The different modalities of the system for guarded recursion can be found in
  the following file, together with some proofs of how they interact.
-}

open import GuardedRecursion.Modalities

{-
  The example implementations from the paper involving streams, together with
  many more examples, are in the next two modules.
-}

open import GuardedRecursion.Streams.Examples.Guarded
open import GuardedRecursion.Streams.Examples.Standard

{-
  The case study involving parametricity is worked out in the following file.
-}

open import Parametricity.Binary


--------------------------------------------------
-- SECTION 4: Implementation of Sikkel

{-
  Definition of small categories (= modes)
-}

open import Categories

{-
  Definition of contexts, substitutions and the empty context.
  Note that unlike the definition given in the paper, the fields of the record
  type Ctx have names set, rel, rel-id and rel-comp instead of _⟨_⟩, _⟪_⟫_, ctx-id
  and ctx-comp. The operators _⟨_⟩ and _⟪_⟫_ are defined after Ctx and are used
  in the definition of functions, but not as destructors when copattern matching.
-}

open import CwF-Structure.Contexts

{-
  Definition of types and type equality
  Note again that the field names for Ty differ from the one in the paper.
  The code replaces _⟨_,_⟩ by type, _⟪_,_⟫_ by morph, ty-cong by morph-cong,
  ty-id by morph-id and ty-comp by morph-comp. Again _⟨_,_⟩ and _⟪_,_⟫_ are
  defined as functions.
-}

open import CwF-Structure.Types

{-
  Definition of terms
  The field _⟨_,_⟩' from the paper is renamed to term.
-}

open import CwF-Structure.Terms

{-
  Definition of function types
-}

open import Types.Functions

{-
  The implementation of the later modality and of the parametricity example
  can be found in the following modules.
-}

open import GuardedRecursion.Modalities.Later
open import Parametricity.Binary

{-
  The different type operations are defined in Reflection.Naturality.TypeOperations.
  The naturality solver is implemented in Reflection.Naturality.Solver.
  The implementation of the by-naturality tactic can be found in Reflection.Tactic.Naturality
-}

open import Reflection.Naturality.TypeOperations
open import Reflection.Naturality.Solver
open import Reflection.Tactic.Naturality


--------------------------------------------------
-- Code not discussed in the paper

{-
  Apart from binary parametricity, we also have a worked-out example of unary parametricity.
  The set-up is quite similar: we describe a simplistic interface for booleans and an implementation
  of this interface by ℕ (0 representinf false and 1 representing true).
  Unary parametricity will then allow us to prove that any function implemented with the operations
  of the interface will map 0 and 1 again to 0 or 1 (but no other natural number).
-}

open import Parametricity.Unary

{-
  We have a simple formalization of the Yoneda embedding.
  This is not used in any of the examples.
-}

open import CwF-Structure.Yoneda

{-
  The module LiftingFunctors describes how a functor from a category C to a category D gives rise to a
  CwF morphism from the presheaf category with base category D to the presheaf category with base category C.
  This is not used in any of the examples.
-}

open import LiftingFunctors
