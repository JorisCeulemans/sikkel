--------------------------------------------------
-- README
--------------------------------------------------

module README where

{-
  This is the readme for the Sikkel library, as presented in the CPP submission
    Sikkel: Multimode Simple Type Theory as an Agda Library.

  We use Agda 2.6.2 and the Agda standard library (version 1.7).
  Instructions for installing Agda can be found on https://agda.readthedocs.io/en/v2.6.2/getting-started/installation.html
  Installation instructions for the Agda standard library are located at https://github.com/agda/agda-stdlib/blob/master/notes/installation-guide.md

  If Agda and the standard library are installed, you can open this file in emacs and press C-c C-l to typecheck it.

  This file presents an overview of the paper with references to the relevant parts of the code as import statements.
  After typechecking this file (by pressing C-c C-l), you can directly jump to the imported module by clicking it with the middle mouse button
  or by placing the cursor at the module name and pressing M-.
-}


--------------------------------------------------
-- SECTION 1: Introduction

{-
  No code for this section.
-}


--------------------------------------------------
-- SECTION 2: Multimode Simple Type Theory (MSTT)

{-
  The definition of an MSTT mode theory can be found in the following module.
  Of course, this definition also contains the extra fields that were discussed
  in later sections of the paper.
-}

import MSTT.ModeTheory

{-
  The syntax for MSTT types, contexts and terms is contained in the following
  module.
-}

import MSTT.Syntax

{-
  The typing relation of MSTT is not formalized as an Agda relation.
  Instead, we immediately wrote a type inference algorithm discussed in Section 5.
  The same is true for equivalence of types.

  The Example program at the end of the paragraph is located in the following
  module.
-}

import MSTT.Example


--------------------------------------------------
-- SECTION 3: Application 1: GuardedRecursive Type Theory

{-
  The mode theory and syntax of the MSTT instance for guarded recursion are
  worked out in the following modules.
-}

import Applications.GuardedRecursion.MSTT.ModeTheory
import Applications.GuardedRecursion.MSTT.Syntax -- similar to MSTT.Syntax which was used as a template

{-
  Many example programs involving streams (guarded and standard) are presented
  in the following module. Note that the type checker an extraction mechanism
  are also already used in this file.

  The example about (g-)nats can be found at lines 80 and 348.
  The implementation of tail' is at line 423.
-}

import Applications.GuardedRecursion.StreamsExamples


--------------------------------------------------
-- SECTION 4: Presheaf Models

{-
  The notion of a base category, together with all instances used in the examples
  are defined in the following module.
-}

import Model.BaseCategory

{-
  All concepts that are related to the CwF structure can be found in the following modules.
-}

-- Contexts, substitutions
import Model.CwF-Structure.Context

-- Types, equivalence of types
import Model.CwF-Structure.Type

-- Terms, transport operation ι[_]_
import Model.CwF-Structure.Term

-- Closed types
import Model.CwF-Structure.ClosedType

{-
  Sikkel's simple built-in types and type constructors can be imported from
  several files in the directory Model.Type.
-}

import Model.Type.Function
import Model.Type.Product
import Model.Type.Sum
import Model.Type.Discrete

{-
  The definition of a DRA, together with the unit DRA, composition,
  equivalence of DRAs and semantic 2-cells can be found in the
  following module.
-}

import Model.Modality

{-
  The definition of the base category ω is defined in Model.BaseCategory
  imported above.

  Implementation of the semantic later modality and earlier operation
  are found in the following module.
-}

import Applications.GuardedRecursion.Model.Modalities.Later

{-
  Although not presented in the paper, the semantics of the other
  modalities for guarded recursion, together with some proofs on how
  they interact are implemented in the following modules.
-}

import Applications.GuardedRecursion.Model.Modalities.Constantly
import Applications.GuardedRecursion.Model.Modalities.Forever
import Applications.GuardedRecursion.Model.Modalities.Interaction

{-
  The semantics of guarded streams can be found in the following module.
-}

import Applications.GuardedRecursion.Model.Streams.Guarded


--------------------------------------------------
-- SECTION 5: A Sound Type Checker

{-
  The functions ⟦_⟧mode and ⟦_⟧modality for the interpretation of modes
  and modalities were already included in MSTT.ModeTheory.

  Interpretation of types and contexts can be found in MSTT.InterpretTypes.
-}

import MSTT.InterpretTypes

{-
  The definition of the type checking monad is located in the following module.
-}

import MSTT.TCMonad

{-
  Again, the testing procedures for mode equality and modality equivalence
  were included in MSTT.ModeTheory.

  The function for testing whethet types are equivalent is defined in the
  following file.
-}

import MSTT.Equality

{-
  Finally, the type inference algorithm is implemented in the following module
-}

import MSTT.SoundTypeChecker

{-
  The type inference algorithms and equivalence testing procedures for the
  specific instance of MSTT for guarded recursion can be found in the following
  file.
-}

import Applications.GuardedRecursion.MSTT.Equality
import Applications.GuardedRecursion.MSTT.SoundTypeChecker

{-
  The semantics of the nats example from the end of the section was already
  implemented in Applications.GuardedRecursion.StreamsExamples imported above.
-}


--------------------------------------------------
-- SECTION 6: Extraction to the Meta-level

{-
  The definition of the extraction mechanism, as well as instances of the
  Extractable type class for natural numbers, booleans, functions and products,
  are located in the following module.
-}

import Extraction

{-
  The Extractable instance for ⟨ forever ∣ GStream A ⟩ is implemented in
  the following file.
-}

import Applications.GuardedRecursion.Model.Streams.Standard

{-
  Again, the example nats-agda is found in
  Applications.GuardedRecursion.StreamsExamples imported above (line 358)
-}


--------------------------------------------------
-- SECTION 7: Application 2 : Representation Independence through Parametricity

{-
  The mode theory for the MSTT instance described in this section can be found
  in the following file.
-}

import Applications.Parametricity.MSTT.ModeTheory

{-
  The other parts of the implementation of this MSTT instance are located in
  the following modules.
-}

import Applications.Parametricity.MSTT.Syntax
import Applications.Parametricity.MSTT.Equality
import Applications.Parametricity.MSTT.SoundTypeChecker

{-
  The definition of the base category ⋀ is worked out in Model.BaseCategory,
  which was already imported above.

  Further details about the presheaf model behind this example, such as the
  implementation of the semantic forget-right and forget-left modalities,
  are located in the following module.
-}

import Applications.Parametricity.Model

{-
  The example about the integer interface and the function preserving the relation
  ∼ between two implementations is worked out in the following file.
  Note that we used synonyms DiffNat for ℕ × ℕ and SignNat for Sign × ℕ.
-}

import Applications.Parametricity.IntegerExample


--------------------------------------------------
-- SECTION 8: Discussion, Related and Future Work

{-
  No code for this section.
-}
