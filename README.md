# Shallowly Embedding Type Theories as Presheaf Models in Agda

This repository contains Agda code for shallow embeddings of extensions of Martin-Löf Type Theory (MLTT) as presheaf models.
The framework can be instantiated with an arbitrary small base category, and a user can then manipulate types and terms in a similar way as in MLTT.
The notions of contexts, types and terms are organized as an internal category with families, as defined by Peter Dybjer (see [here](https://link.springer.com/chapter/10.1007/3-540-61780-9_66)).

We use Agda 2.6.1 and the Agda standard library (version 1.3).
We assume uniqueness of identity proofs and function extensionality (although the latter is only used when working with functions in the embedded type theory).

## Overview of this Repository

* Some basic definitions and examples of categories and functors can be found in Categories.agda.
* The definitions of the notions of contexts, substitutions, types and terms are in the folder CwF-Structure.
* The folder Types contains the definition of some basic types (booleans, natural numbers, ...) and of some simple type constructors (non-dependent product types, sum types, non-dependent function types).
* In the folder GuardedRecursion, we instantiate the framework with base category ω (the category structure induced on the set of natural numbers by its standard order), and we define a later modality on types and a primitive for working with Löb induction. This modality is then used to define a type of guarded streams and we construct a stream of zeros via Löb induction.
* The file LiftingFunctors describes how a functor from a category _C_ to a category _D_ gives rise to a cwf morphism from the presheaf model with base category _D_ to the presheaf model with base category _C_.
* The Yoneda embedding and the Yondeda lemma are worked out in Yoneda.agda.

## Using Your Own Base Category

If you want to experiment with presheaves over a new small base category, you should first construct a term `my-category : Category` to represent this base category.
A context should then have type `Ctx my-category ℓ` for an appropriate level `ℓ`.
In the Agda types for types (`Ty`) and terms (`Tm`), the base category is an implicit parameter and hence needs not to be mentioned.
