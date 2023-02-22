# Sikkel

Sikkel is an Agda library that allows a user to program in multimode simple type theories.
It uses a deeply embedded language that is parametrized by a mode theory (specifying the available modes and modalities) and that can be easily extended with additional type and term constructors, thus supporting a wide variety of type theories.
Moreover, Sikkel has a type checker that is sound by construction in the sense that all well-typed programs are automatically translated to their semantics in a shallow embedding based on presheaf models.
Additionally, our model supports combining different base categories by using modalities to transport definitions between them.
This enables in particular a general approach for extracting definitions to the meta-level, so that we can use the extended type theories to define regular Agda functions and prove properties of them.

For an overview of the MSFP paper "Sikkel: Multimode Simple Type Theory as an Agda Library" together with the relevant code, we refer to the file [README.agda](README.agda).

## Installation

Sikkel is tested with Agda 2.6.3, but it is probably also still compatible with Agda 2.6.2. It uses the Agda standard library (version 1.7.2).
To use the library in your Agda development, perform
```
git clone https://github.com/JorisCeulemans/sikkel.git
```
and add the path to Sikkel to the `libraries` file in your `AGDA_DIR` (see https://agda.readthedocs.io/en/v2.6.3/tools/package-system.html for more info).
You can then add a `.agda-lib` file to your project containing
```
depend: sikkel
```
which will allow you to use Sikkel.


## Overview of this Repository

* The deeply embedded syntactic layer can be found in the MSTT directory, together with the sound type checker.
* The formalization of presheaf models is located in the folder Model.
* Extracting shallowly embedded terms in the model to Agda programs is implemented in the file Extraction.agda.
* We have worked out two use cases of Sikkel: guarded recursive type theory and parametricity. They can be found in the directory Applications.
