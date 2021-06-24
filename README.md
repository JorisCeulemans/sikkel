# Shallowly Embedding Type Theories as Presheaf Models in Agda

This repository contains Agda code for shallow embeddings of extensions of Martin-Löf Type Theory (MLTT) as presheaf models.
The framework can be instantiated with an arbitrary small base category, and a user can then manipulate types and terms in a similar way as in MLTT.
The notions of contexts, types and terms are organized as an internal category with families, as defined by Peter Dybjer (see [here](https://link.springer.com/chapter/10.1007/3-540-61780-9_66)).

We use Agda 2.6.2 and the Agda standard library (version 1.7).
We assume uniqueness of identity proofs and function extensionality (although the latter is only used when working with functions in the embedded type theory).

## Overview of this Repository

* Some basic definitions and examples of categories and functors can be found in Categories.agda.
* The definitions of the notions of contexts, substitutions, types and terms are in the folder CwF-Structure.
* The folder Types contains the definition of some basic types (booleans, natural numbers, ...) and of some simple type constructors (non-dependent product types, sum types, non-dependent function types).
* In the folder GuardedRecursion, we instantiate the framework with base category ω (the category structure induced on the set of natural numbers by its standard order), and we define a later modality on types and a primitive for working with Löb induction. This modality is then used to define a type of guarded streams of natural numbers and we implement some operations on streams (such as map and iterate) via Löb induction. Furthermore, this folder contains work in progress on the construction of solutions of recursive domain equations using guarded recursion, in particular the construction of a type in which the untyped lambda calculus can be interpreted.
* The folder Reflection contains some solvers that generate equality proofs for substitutions and types. The naturality solver (which is the most frequently used) is implemented in Reflection.Naturality.agda.
* The file LiftingFunctors describes how a functor from a category _C_ to a category _D_ gives rise to a cwf morphism from the presheaf model with base category _D_ to the presheaf model with base category _C_.
* The Yoneda embedding and the Yondeda lemma are worked out in Yoneda.agda.

## Using Your Own Base Category

If you want to experiment with presheaves over a new small base category, you should first construct a term `my-category : Category` to represent this base category.
A context should then have type `Ctx my-category ℓ` for an appropriate level `ℓ`.
In most of the other constructs (e.g. in the Agda types for types (`Ty`) and terms (`Tm`)), the base category is an implicit parameter and hence needs not to be mentioned.
When you define new operations on types, you probably want the naturality solver to work with them. In order to do so, you just need to provide a value of one of the types `NullaryTypeOp`, `UnaryTypeOp` or `BinaryTypeOp` from the module Reflection.Naturality.
