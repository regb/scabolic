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

##Setup

This project depends on the
[Scala-SMTLIB](https://github.com/regb/scala-smtlib) library, which need to be
separately built from the repository and its jar added to the classpath.

To build Scabolic simply type:

    sbt compile

##CafeSat

<p align="center">
  <img height="300px" src="/logo/cafesat2.jpg" />
</p>

CafeSat is the tool interface to the SAT solver in Scabolic. To build CafeSat:

    sbt clean
    sbt compile
    sbt cafesat

Then you can use CafeSat as follows:

    ./cafesat [ OPTIONS ] INPUT

By default (actually, this cannot be changed so far), the INPUT is assumed to
be in Dimacs CNF format.

The [Scala'13 paper](http://dx.doi.org/10.1145/2489837.2489839) gives a short overview
of CafeSat.

##Scala API

Scabolic exports a mini API usable from Scala programs. The API is not stable
yet and is expected to change frequently. It will not be backward compatible.
The best way to learn the API is to look at the examples in the apps branch of
this repository.

##Licence

Scabolic is distributed under the terms of The MIT License.

All source code in this repository is distributed under this license. The
reference text is in the file LICENSE, no copy of the text shall be included in
any of the source file, but it is implicitly assumed they are available under
the terms specified in LICENSE.

BY COMMITTING TO THIS REPOSITORY, YOU ACCEPT TO RELEASE YOUR CODE UNDER
THE TERMS OF THE MIT LICENSE AS DESCRIBE IN THE LICENSE FILE.

##Copyright

The copyright for each portion of code is owned by the respective committer,
based on the git history. There is no per file or per function copyright as
this does not make sense in general. Sorry to be picky, but that's copyright
law for you. More information can be found in the COPYRIGHT.md file.
