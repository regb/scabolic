#SCABOLIC

This is the official repository for the Scabolic source code. The aim of
Scabolic is to combine in a single tool/library several automated reasoning
algorithms. In particular this should (soon) support SAT/SMT solving as well as
features from computer algebra.

Scabolic is written in the Scala programming language and provide (well, it
will provide it in the near future) a nice Domain Specific Language (DSL) to be
used either as an interactive tool within the Scala REPL or as a Scala library.

Currently, Scabolic provides two documented interfaces:

- The CafeSat tool
- A Scala API to use inner SAT solver

##CafeSat

CafeSat is the tool interface to the SAT solver in Scabolic. To build CafeSat:

    sbt clean
    sbt compile
    sbt cafesat

Then you can use CafeSat as follows:

    ./cafesat [ OPTIONS ] INPUT

By default (actually, this cannot be changed so far), the INPUT is assumed to
be in Dimacs CNF format.

##Scala API

Scabolic exports a mini API usable from Scala programs. The API is not stable
yet and is expected to change frequently. It will not be backward compatible.
The best way to learn the API is to look at the examples in the apps branch of
this repository.
